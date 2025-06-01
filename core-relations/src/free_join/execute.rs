//! Core free join execution.

use std::{
    iter, mem,
    sync::{atomic::AtomicUsize, Arc},
};

use numeric_id::{DenseIdMap, IdVec, NumericId};
use smallvec::SmallVec;
use web_time::Instant;

use crate::{
    action::{Bindings, ExecutionState, PredictedVals},
    common::{DashMap, Value},
    free_join::{get_index_from_tableinfo, RuleReport, RuleSetReport},
    hash_index::{ColumnIndex, IndexBase, TupleIndex},
    offsets::{Offsets, SortedOffsetVector, Subset},
    pool::{Clear, Pooled},
    query::RuleSet,
    row_buffer::TaggedRowBuffer,
    table_spec::{ColumnId, Offset, WrappedTableRef},
    Constraint, OffsetRange, Pool, PoolSet, SubsetRef,
};

use super::{
    get_column_index_from_tableinfo,
    plan::{JoinHeader, JoinStage, Plan},
    with_pool_set, ActionId, AtomId, Database, HashColumnIndex, HashIndex, TableId, Variable,
};

enum DynamicIndex {
    Cached {
        intersect_outer: bool,
        table: HashIndex,
    },
    CachedColumn {
        intersect_outer: bool,
        table: HashColumnIndex,
    },
    Dynamic(TupleIndex),
    DynamicColumn(Arc<ColumnIndex>),
}

struct Prober {
    subset: Subset,
    pool: Pool<SortedOffsetVector>,
    ix: DynamicIndex,
}

impl Prober {
    fn get_subset(&self, key: &[Value]) -> Option<Subset> {
        match &self.ix {
            DynamicIndex::Cached {
                intersect_outer,
                table,
            } => {
                let mut sub = table.get().unwrap().get_subset(key)?.to_owned(&self.pool);
                if *intersect_outer {
                    sub.intersect(self.subset.as_ref(), &self.pool);
                    if sub.is_empty() {
                        return None;
                    }
                }
                Some(sub)
            }
            DynamicIndex::CachedColumn {
                intersect_outer,
                table,
            } => {
                debug_assert_eq!(key.len(), 1);
                let mut sub = table
                    .get()
                    .unwrap()
                    .get_subset(&key[0])?
                    .to_owned(&self.pool);
                if *intersect_outer {
                    sub.intersect(self.subset.as_ref(), &self.pool);
                    if sub.is_empty() {
                        return None;
                    }
                }
                Some(sub)
            }
            DynamicIndex::Dynamic(tab) => tab.get_subset(key).map(|x| x.to_owned(&self.pool)),
            DynamicIndex::DynamicColumn(tab) => {
                tab.get_subset(&key[0]).map(|x| x.to_owned(&self.pool))
            }
        }
    }
    fn for_each(&self, mut f: impl FnMut(&[Value], SubsetRef)) {
        match &self.ix {
            DynamicIndex::Cached {
                intersect_outer: true,
                table,
            } => table.get().unwrap().for_each(|k, v| {
                let mut res = v.to_owned(&self.pool);
                res.intersect(self.subset.as_ref(), &self.pool);
                if !res.is_empty() {
                    f(k, res.as_ref())
                }
            }),
            DynamicIndex::Cached {
                intersect_outer: false,
                table,
            } => table.get().unwrap().for_each(|k, v| f(k, v)),
            DynamicIndex::CachedColumn {
                intersect_outer: true,
                table,
            } => {
                table.get().unwrap().for_each(|k, v| {
                    let mut res = v.to_owned(&self.pool);
                    res.intersect(self.subset.as_ref(), &self.pool);
                    if !res.is_empty() {
                        f(&[*k], res.as_ref())
                    }
                });
            }
            DynamicIndex::CachedColumn {
                intersect_outer: false,
                table,
            } => {
                table.get().unwrap().for_each(|k, v| f(&[*k], v));
            }
            DynamicIndex::Dynamic(tab) => {
                tab.for_each(f);
            }
            DynamicIndex::DynamicColumn(tab) => tab.for_each(|k, v| {
                f(&[*k], v);
            }),
        }
    }

    fn len(&self) -> usize {
        match &self.ix {
            DynamicIndex::Cached { table, .. } => table.get().unwrap().len(),
            DynamicIndex::CachedColumn { table, .. } => table.get().unwrap().len(),
            DynamicIndex::Dynamic(tab) => tab.len(),
            DynamicIndex::DynamicColumn(tab) => tab.len(),
        }
    }
}

impl Database {
    pub fn run_rule_set(&mut self, rule_set: &RuleSet) -> RuleSetReport {
        fn do_parallel() -> bool {
            #[cfg(debug_assertions)]
            {
                use rand::Rng;
                rand::thread_rng().gen_bool(0.5)
            }

            #[cfg(not(debug_assertions))]
            {
                rayon::current_num_threads() > 1
            }
        }
        if rule_set.plans.is_empty() {
            return RuleSetReport::default();
        }
        let preds = with_pool_set(|ps| ps.get::<PredictedVals>());
        let index_cache = IndexCache::default();
        let match_counter = MatchCounter::new(rule_set.actions.n_ids());

        let mut instrs = rule_set
            .plans
            .vals()
            .map(|(plan, _, _)| Vec::from_iter(0..plan.stages.instrs.len()))
            .collect::<Vec<_>>();

        let search_and_apply_timer = Instant::now();
        let rule_reports = DashMap::default();
        if do_parallel() {
            rayon::in_place_scope(|scope| {
                for ((plan, desc, _action), instr_order) in
                    rule_set.plans.vals().zip(instrs.iter_mut())
                {
                    scope.spawn(|scope| {
                        let join_state = JoinState::new(self, &preds, &index_cache);
                        let mut action_buf =
                            ScopedActionBuffer::new(scope, rule_set, &match_counter);
                        let mut binding_info = BindingInfo::default();
                        for (id, info) in plan.atoms.iter() {
                            let table = join_state.db.get_table(info.table);
                            binding_info.subsets.insert(id, table.all());
                        }

                        let search_and_apply_timer = Instant::now();
                        join_state.run_header(
                            plan,
                            instr_order,
                            &mut binding_info,
                            &mut action_buf,
                        );
                        let search_and_apply_time = search_and_apply_timer.elapsed();

                        if action_buf.needs_flush {
                            action_buf.flush(&mut ExecutionState::new(
                                &preds,
                                self.read_only_view(),
                                Default::default(),
                            ));
                        }
                        rule_reports.insert(
                            desc.clone(),
                            RuleReport {
                                search_and_apply_time,
                                num_matches: 0,
                            },
                        );
                    });
                }
            });
        } else {
            let join_state = JoinState::new(self, &preds, &index_cache);
            // Just run all of the plans in order with a single in-place action
            // buffer.
            let mut action_buf = InPlaceActionBuffer {
                rule_set,
                match_counter: &match_counter,
                batches: Default::default(),
            };
            for ((plan, desc, _action), instr_order) in rule_set.plans.vals().zip(instrs.iter_mut())
            {
                let mut binding_info = BindingInfo::default();
                for (id, info) in plan.atoms.iter() {
                    let table = join_state.db.get_table(info.table);
                    binding_info.subsets.insert(id, table.all());
                }

                let search_and_apply_timer = Instant::now();
                join_state.run_header(plan, instr_order, &mut binding_info, &mut action_buf);
                let search_and_apply_time = search_and_apply_timer.elapsed();

                rule_reports.insert(
                    desc.clone(),
                    RuleReport {
                        search_and_apply_time,
                        num_matches: 0,
                    },
                );
            }
            action_buf.flush(&mut ExecutionState::new(
                &preds,
                self.read_only_view(),
                Default::default(),
            ));
        }
        for (_plan, desc, action) in rule_set.plans.vals() {
            let mut reservation = rule_reports.get_mut(desc).unwrap();
            let RuleReport { num_matches, .. } = reservation.value_mut();
            *num_matches = match_counter.read_matches(*action);
        }
        let search_and_apply_time = search_and_apply_timer.elapsed();

        let merge_timer = Instant::now();
        let changed = self.merge_all();
        let merge_time = merge_timer.elapsed();

        RuleSetReport {
            changed,
            rule_reports,
            search_and_apply_time,
            merge_time,
        }
    }
}

#[derive(Default)]
struct ActionState {
    n_runs: usize,
    len: usize,
    bindings: Bindings,
}

type IndexCache = DashMap<(ColumnId, TableId, Subset), Arc<ColumnIndex>>;

struct JoinState<'a> {
    db: &'a Database,
    preds: &'a PredictedVals,
    index_cache: &'a IndexCache,
}

#[derive(Default, Clone)]
struct BindingInfo {
    bindings: DenseIdMap<Variable, Value>,
    subsets: DenseIdMap<AtomId, Subset>,
}

impl<'a> JoinState<'a> {
    fn new(db: &'a Database, preds: &'a PredictedVals, index_cache: &'a IndexCache) -> Self {
        Self {
            db,
            preds,
            index_cache,
        }
    }

    fn get_index(
        &self,
        plan: &Plan,
        atom: AtomId,
        binding_info: &mut BindingInfo,
        cols: impl Iterator<Item = ColumnId>,
    ) -> Prober {
        let cols = SmallVec::<[ColumnId; 4]>::from_iter(cols);
        let subset = binding_info.subsets.unwrap_val(atom);

        let table_id = plan.atoms[atom].table;
        let info = &self.db.tables[table_id];
        let all_cacheable = cols.iter().all(|col| {
            !info
                .spec
                .uncacheable_columns
                .get(*col)
                .copied()
                .unwrap_or(false)
        });
        let whole_table = info.table.all();
        let dyn_index = if all_cacheable
            && subset.is_dense()
            && whole_table.size() / 2 < subset.size()
        {
            // Skip intersecting with the subset if we are just looking at the
            // whole table.
            let intersect_outer =
                !(whole_table.is_dense() && subset.bounds() == whole_table.bounds());
            // heuristic: if the subset we are scanning is somewhat
            // large _or_ it is most of the table, or we already have a cached
            // index for it, then return it.
            if cols.len() != 1 {
                DynamicIndex::Cached {
                    intersect_outer,
                    table: get_index_from_tableinfo(info, &cols).clone(),
                }
            } else {
                DynamicIndex::CachedColumn {
                    intersect_outer,
                    table: get_column_index_from_tableinfo(info, cols[0]).clone(),
                }
            }
        } else if cols.len() != 1 {
            DynamicIndex::Dynamic(info.table.group_by_key(subset.as_ref(), &cols))
        } else {
            DynamicIndex::DynamicColumn(if subset.size() > 16 {
                // NB: we could use the raw api here to avoid cloning the subset
                // on a cache hit.
                let entry = self.index_cache.entry((cols[0], table_id, subset.clone()));
                entry
                    .or_insert_with(|| Arc::new(info.table.group_by_col(subset.as_ref(), cols[0])))
                    .value()
                    .clone()
            } else {
                Arc::new(info.table.group_by_col(subset.as_ref(), cols[0]))
            })
        };
        Prober {
            subset,
            pool: with_pool_set(|ps| ps.get_pool().clone()),
            ix: dyn_index,
        }
    }
    fn get_column_index(
        &self,
        plan: &Plan,
        binding_info: &mut BindingInfo,
        atom: AtomId,
        col: ColumnId,
    ) -> Prober {
        self.get_index(plan, atom, binding_info, iter::once(col))
    }

    /// Runs the free join plan, starting with the header.
    ///
    /// A bit about the `instr_order` parameter: This defines the order in which the [`JoinStage`]
    /// instructions will run. We want to support cached [`Plan`]s that may be based on stale
    /// ordering information. `instr_order` allows us to specify a new ordering of the instructions
    /// without mutating the plan itself: `run_plan` simply executes
    /// `plan.stages.instrs[instr_order[i]]` at stage `i`.
    ///
    /// This is also a stepping stone towards supporting fully dynamic variable ordering.
    fn run_header<'buf, BUF: ActionBuffer<'buf>>(
        &self,
        plan: &'a Plan,
        instr_order: &'a mut [usize],
        binding_info: &mut BindingInfo,
        action_buf: &mut BUF,
    ) where
        'a: 'buf,
    {
        for JoinHeader { atom, subset, .. } in &plan.stages.header {
            if subset.is_empty() {
                return;
            }
            let mut cur = binding_info.subsets.unwrap_val(*atom);
            cur.intersect(subset.as_ref(), &with_pool_set(|ps| ps.get_pool()));
            binding_info.subsets.insert(*atom, cur);
        }

        sort_plan_by_size(instr_order, &plan.stages.instrs, binding_info);
        self.run_plan(plan, instr_order.into(), 0, binding_info, action_buf);
    }

    /// The core method for executing a free join plan.
    ///
    /// This method takes the plan, mutable data-structures for variable binding and staging
    /// actions, and two indexes: `cur` which is the current stage of the plan to run, and `level`
    /// which is the current "fan-out" node we are in. The latter parameter is an experimental
    /// index used to detect if we are at the "top" of a plan rather than the "bottom", and is
    /// currently used as a heuristic to determine if we should increase parallelism more than the
    /// default.
    fn run_plan<'buf, BUF: ActionBuffer<'buf>>(
        &self,
        plan: &'a Plan,
        mut instr_order: Box<[usize]>,
        cur: usize,
        binding_info: &mut BindingInfo,
        action_buf: &mut BUF,
    ) where
        'a: 'buf,
    {
        if cur >= instr_order.len() {
            action_buf.push_bindings(plan.stages.actions, &binding_info.bindings, || {
                ExecutionState::new(self.preds, self.db.read_only_view(), Default::default())
            });
            return;
        }
        let chunk_size = action_buf.morsel_size(cur);
        let cur_size = estimate_size(&plan.stages.instrs[instr_order[cur]], binding_info);
        if cur_size > 32 && cur < instr_order.len() - 1 {
            // If we have a reasonable number of tuples to process, adjust the variable order.
            sort_plan_by_size(&mut instr_order[cur..], &plan.stages.instrs, binding_info);
        }
        // Helper macro (not its own method to appease the borrow checker).
        macro_rules! drain_updates {
            ($updates:expr) => {
                if cur == 0 || cur == 1 {
                    drain_updates_parallel!($updates)
                } else {
                    for mut update in $updates.drain(..) {
                        for (var, val) in update.bindings.drain(..) {
                            binding_info.bindings.insert(var, val);
                        }
                        for (atom, subset) in update.refinements.drain(..) {
                            binding_info.subsets.insert(atom, subset);
                        }
                        self.run_plan(plan, instr_order.clone(), cur + 1, binding_info, action_buf);
                    }
                }
            };
        }
        macro_rules! drain_updates_parallel {
            ($updates:expr) => {{
                let mut updates = mem::take(&mut $updates);
                let predicted = self.preds;
                let index_cache = self.index_cache;
                let db = self.db;
                let next_order = instr_order.clone();
                action_buf.recur(
                    binding_info,
                    move || ExecutionState::new(predicted, db.read_only_view(), Default::default()),
                    move |binding_info, buf| {
                        for mut update in updates.drain(..) {
                            for (var, val) in update.bindings.drain(..) {
                                binding_info.bindings.insert(var, val);
                            }
                            for (atom, subset) in update.refinements.drain(..) {
                                binding_info.subsets.insert(atom, subset);
                            }
                            JoinState {
                                db,
                                preds: predicted,
                                index_cache,
                            }
                            .run_plan(
                                plan,
                                next_order.clone(),
                                cur + 1,
                                binding_info,
                                buf,
                            );
                        }
                    },
                );
            }};
        }

        fn refine_subset(
            sub: Subset,
            constraints: &[Constraint],
            table: &WrappedTableRef,
        ) -> Subset {
            let sub = table.refine_live(sub);
            table.refine(sub, constraints)
        }

        match &plan.stages.instrs[instr_order[cur]] {
            JoinStage::Intersect { var, scans } => match scans.as_slice() {
                [] => {}
                [a] if a.cs.is_empty() => {
                    if binding_info.subsets[a.atom].is_empty() {
                        return;
                    }

                    let prober = self.get_column_index(plan, binding_info, a.atom, a.column);
                    let table = self.db.tables[plan.atoms[a.atom].table].table.as_ref();
                    let mut updates = with_pool_set(|ps| {
                        let mut updates: Pooled<Vec<Pooled<FrameUpdate>>> = ps.get();
                        prober.for_each(|val, x| {
                            let mut update: Pooled<FrameUpdate> = ps.get();
                            update.push_binding(*var, val[0]);
                            let sub = refine_subset(x.to_owned(&ps.get_pool()), &[], &table);
                            if sub.is_empty() {
                                return;
                            }
                            update.refine_atom(a.atom, sub);
                            updates.push(update);
                            if updates.len() >= chunk_size {
                                drain_updates_parallel!(updates);
                            }
                        });
                        updates
                    });
                    drain_updates!(updates);
                    binding_info.subsets.insert(a.atom, prober.subset);
                }
                [a] => {
                    if binding_info.subsets[a.atom].is_empty() {
                        return;
                    }
                    let prober = self.get_column_index(plan, binding_info, a.atom, a.column);
                    let table = self.db.tables[plan.atoms[a.atom].table].table.as_ref();
                    let mut updates = with_pool_set(|ps| {
                        let mut updates: Pooled<Vec<Pooled<FrameUpdate>>> = ps.get();
                        prober.for_each(|val, x| {
                            let mut update: Pooled<FrameUpdate> = ps.get();
                            update.push_binding(*var, val[0]);
                            let sub = refine_subset(x.to_owned(&ps.get_pool()), &a.cs, &table);
                            if sub.is_empty() {
                                return;
                            }
                            update.refine_atom(a.atom, sub);
                            updates.push(update);
                            if updates.len() >= chunk_size {
                                drain_updates_parallel!(updates);
                            }
                        });
                        updates
                    });
                    drain_updates!(updates);
                    binding_info.subsets.insert(a.atom, prober.subset);
                }
                [a, b] => {
                    let mut updates: Pooled<Vec<Pooled<FrameUpdate>>> = with_pool_set(PoolSet::get);
                    let a_prober = self.get_column_index(plan, binding_info, a.atom, a.column);
                    let b_prober = self.get_column_index(plan, binding_info, b.atom, b.column);

                    let ((smaller, smaller_scan), (larger, larger_scan)) =
                        if a_prober.len() < b_prober.len() {
                            ((&a_prober, a), (&b_prober, b))
                        } else {
                            ((&b_prober, b), (&a_prober, a))
                        };

                    let smaller_atom = smaller_scan.atom;
                    let larger_atom = larger_scan.atom;
                    let large_table = self.db.tables[plan.atoms[larger_atom].table].table.as_ref();
                    let small_table = self.db.tables[plan.atoms[smaller_atom].table]
                        .table
                        .as_ref();
                    with_pool_set(|ps| {
                        smaller.for_each(|val, small_sub| {
                            if let Some(mut large_sub) = larger.get_subset(val) {
                                large_sub = refine_subset(large_sub, &larger_scan.cs, &large_table);
                                if large_sub.is_empty() {
                                    return;
                                }
                                let small_sub = refine_subset(
                                    small_sub.to_owned(&ps.get_pool()),
                                    &smaller_scan.cs,
                                    &small_table,
                                );
                                if small_sub.is_empty() {
                                    return;
                                }
                                let mut update: Pooled<FrameUpdate> = ps.get();
                                update.push_binding(*var, val[0]);
                                update.refine_atom(smaller_atom, small_sub);
                                update.refine_atom(larger_atom, large_sub);
                                updates.push(update);
                                if updates.len() >= chunk_size {
                                    drain_updates_parallel!(updates);
                                }
                            }
                        });
                    });
                    drain_updates!(updates);

                    binding_info.subsets.insert(a.atom, a_prober.subset);
                    binding_info.subsets.insert(b.atom, b_prober.subset);
                }
                rest => {
                    let mut updates: Pooled<Vec<Pooled<FrameUpdate>>> = with_pool_set(PoolSet::get);
                    let mut smallest = 0;
                    let mut smallest_size = usize::MAX;
                    let mut probers = Vec::with_capacity(rest.len());
                    for (i, scan) in rest.iter().enumerate() {
                        let prober =
                            self.get_column_index(plan, binding_info, scan.atom, scan.column);
                        let size = prober.len();
                        if size < smallest_size {
                            smallest = i;
                            smallest_size = size;
                        }
                        probers.push(prober);
                    }

                    let main_spec = &rest[smallest];
                    let main_spec_table = self.db.tables[plan.atoms[main_spec.atom].table]
                        .table
                        .as_ref();

                    if smallest_size != 0 {
                        // Smallest leads the scan
                        probers[smallest].for_each(|key, sub| {
                            with_pool_set(|ps| {
                                let mut update: Pooled<FrameUpdate> = ps.get();
                                update.push_binding(*var, key[0]);
                                for (i, scan) in rest.iter().enumerate() {
                                    if i == smallest {
                                        continue;
                                    }
                                    if let Some(mut sub) = probers[i].get_subset(key) {
                                        let table = self.db.tables[plan.atoms[rest[i].atom].table]
                                            .table
                                            .as_ref();
                                        sub = refine_subset(sub, &rest[i].cs, &table);
                                        if sub.is_empty() {
                                            return;
                                        }
                                        update.refine_atom(scan.atom, sub)
                                    } else {
                                        // Empty intersection.
                                        return;
                                    }
                                }
                                let sub = sub.to_owned(&ps.get_pool());
                                let sub = refine_subset(sub, &main_spec.cs, &main_spec_table);
                                if sub.is_empty() {
                                    return;
                                }
                                update.refine_atom(main_spec.atom, sub);
                                updates.push(update);
                                if updates.len() >= chunk_size {
                                    drain_updates_parallel!(updates);
                                }
                            })
                        });
                        drain_updates!(updates);
                    }
                    for (spec, prober) in rest.iter().zip(probers.into_iter()) {
                        binding_info.subsets.insert(spec.atom, prober.subset);
                    }
                }
            },
            JoinStage::FusedIntersect {
                cover,
                bind,
                to_intersect,
            } if to_intersect.is_empty() => {
                let cover_atom = cover.to_index.atom;
                if binding_info.subsets[cover_atom].is_empty() {
                    return;
                }
                let mut updates: Pooled<Vec<Pooled<FrameUpdate>>> = with_pool_set(PoolSet::get);
                let proj = SmallVec::<[ColumnId; 4]>::from_iter(bind.iter().map(|(col, _)| *col));
                let cover_subset = binding_info.subsets.unwrap_val(cover_atom);
                let mut cur = Offset::new(0);
                let mut buffer = TaggedRowBuffer::new(bind.len());
                loop {
                    buffer.clear();
                    let table = &self.db.tables[plan.atoms[cover_atom].table].table;
                    let next = table.scan_project(
                        cover_subset.as_ref(),
                        &proj,
                        cur,
                        chunk_size,
                        &cover.constraints,
                        &mut buffer,
                    );
                    for (row, key) in buffer.non_stale() {
                        let mut update: Pooled<FrameUpdate> = with_pool_set(PoolSet::get);
                        update.refine_atom(
                            cover_atom,
                            Subset::Dense(OffsetRange::new(row, row.inc())),
                        );
                        // bind the values
                        for (i, (_, var)) in bind.iter().enumerate() {
                            update.push_binding(*var, key[i]);
                        }
                        updates.push(update);
                        if updates.len() >= chunk_size {
                            drain_updates_parallel!(updates);
                        }
                    }
                    if let Some(next) = next {
                        cur = next;
                        continue;
                    }
                    break;
                }
                drain_updates!(updates);
                // Restore the subsets we swapped out.
                binding_info.subsets.insert(cover_atom, cover_subset);
            }
            JoinStage::FusedIntersect {
                cover,
                bind,
                to_intersect,
            } => {
                let cover_atom = cover.to_index.atom;
                if binding_info.subsets[cover_atom].is_empty() {
                    return;
                }
                let index_probers = to_intersect
                    .iter()
                    .enumerate()
                    .map(|(i, (spec, _))| {
                        (
                            i,
                            spec.to_index.atom,
                            self.get_index(
                                plan,
                                spec.to_index.atom,
                                binding_info,
                                spec.to_index.vars.iter().copied(),
                            ),
                        )
                    })
                    .collect::<SmallVec<[(usize, AtomId, Prober); 4]>>();
                let mut updates: Pooled<Vec<Pooled<FrameUpdate>>> = with_pool_set(PoolSet::get);
                let proj = SmallVec::<[ColumnId; 4]>::from_iter(bind.iter().map(|(col, _)| *col));
                let cover_subset = binding_info.subsets.unwrap_val(cover_atom);
                let mut cur = Offset::new(0);
                let mut buffer = TaggedRowBuffer::new(bind.len());
                loop {
                    buffer.clear();
                    let table = &self.db.tables[plan.atoms[cover_atom].table].table;
                    let next = table.scan_project(
                        cover_subset.as_ref(),
                        &proj,
                        cur,
                        chunk_size,
                        &cover.constraints,
                        &mut buffer,
                    );
                    let pool: Pool<FrameUpdate> = with_pool_set(PoolSet::get_pool);
                    'mid: for (row, key) in buffer.non_stale() {
                        let mut update: Pooled<FrameUpdate> = pool.get();
                        update.refine_atom(
                            cover_atom,
                            Subset::Dense(OffsetRange::new(row, row.inc())),
                        );
                        // bind the values
                        for (i, (_, var)) in bind.iter().enumerate() {
                            update.push_binding(*var, key[i]);
                        }
                        // now probe each remaining indexes
                        for (i, atom, prober) in &index_probers {
                            // create a key: to_intersect indexes into the key from the cover
                            let index_cols = &to_intersect[*i].1;
                            let index_key = index_cols
                                .iter()
                                .map(|col| key[col.index()])
                                .collect::<SmallVec<[Value; 4]>>();
                            let Some(mut subset) = prober.get_subset(&index_key) else {
                                // There are no possible values for this subset
                                continue 'mid;
                            };
                            // apply any constraints needed in this scan.
                            let table_info = &self.db.tables[plan.atoms[*atom].table];
                            let cs = &to_intersect[*i].0.constraints;
                            subset = refine_subset(subset, cs, &table_info.table.as_ref());
                            if subset.is_empty() {
                                // There are no possible values for this subset
                                continue 'mid;
                            }
                            update.refine_atom(*atom, subset);
                        }
                        updates.push(update);
                        if updates.len() >= chunk_size {
                            drain_updates_parallel!(updates);
                        }
                    }
                    if let Some(next) = next {
                        cur = next;
                        continue;
                    }
                    break;
                }
                // TODO: special-case the scenario when the cover doesn't need
                // deduping (and hence we can do a straight scan: e.g. when the
                // cover is binding a superset of the primary key for the
                // table).
                drain_updates!(updates);
                // Restore the subsets we swapped out.
                binding_info.subsets.insert(cover_atom, cover_subset);
                for (_, atom, prober) in index_probers {
                    binding_info.subsets.insert(atom, prober.subset);
                }
            }
        }
    }
}

#[derive(Default)]
pub(crate) struct FrameUpdate {
    bindings: Vec<(Variable, Value)>,
    refinements: Vec<(AtomId, Subset)>,
}

impl FrameUpdate {
    fn push_binding(&mut self, var: Variable, val: Value) {
        self.bindings.push((var, val));
    }

    fn refine_atom(&mut self, atom: AtomId, subset: Subset) {
        self.refinements.push((atom, subset));
    }
}

impl Clear for FrameUpdate {
    fn clear(&mut self) {
        self.bindings.clear();
        self.refinements.clear();
    }
    fn reuse(&self) -> bool {
        self.bindings.capacity() > 0 || self.refinements.capacity() > 0
    }
    fn bytes(&self) -> usize {
        self.bindings.capacity() * mem::size_of::<(Variable, Value)>()
            + self.refinements.capacity() * mem::size_of::<(AtomId, Subset)>()
    }
}

const VAR_BATCH_SIZE: usize = 128;

/// A trait used to abstract over different ways of buffering actions together
/// before running them.
///
/// This trait exists as a fairly ad-hoc wrapper over its two implementations.
/// It allows us to avoid duplicating the (somewhat monstrous) `run_plan` method
/// for serial and parallel modes.
trait ActionBuffer<'state>: Send {
    type AsLocal<'a>: ActionBuffer<'state>
    where
        'state: 'a;
    /// Push the given bindings to be executed for the specified action. If this
    /// buffer has built up a sufficient batch size, it may execute
    /// `to_exec_state` and then execute the action.
    fn push_bindings(
        &mut self,
        action: ActionId,
        bindings: &DenseIdMap<Variable, Value>,
        to_exec_state: impl FnMut() -> ExecutionState<'state>,
    );

    /// Execute any remaining actions associated with this buffer.
    fn flush(&mut self, exec_state: &mut ExecutionState);

    /// Execute `work`, potentially asynchronously, with a mutable reference to
    /// an action buffer, potentially handed off to a different thread.
    ///
    /// Callers pass a clonable `Local` value that may be modified by work, or
    /// cloned first and then have a separate copy modified by `work`. Callers
    /// should assume that `local` _is_ modified synchronously.
    fn recur<Local: Clone + Send + 'state>(
        &mut self,
        local: &mut Local,
        to_exec_state: impl FnMut() -> ExecutionState<'state> + Send + 'state,
        work: impl for<'a> FnOnce(&mut Local, &mut Self::AsLocal<'a>) + Send + 'state,
    );

    /// The unit at which you should batch updates passed to calls to `recur`,
    /// potentially depending on the current level of recursion.
    ///
    /// As of right now this is just a hard-coded value. We may change it in the
    /// future to fan out more at higher levels though.
    fn morsel_size(&mut self, _level: usize) -> usize {
        1024
    }
}

/// The action buffer we use if we are executing in a single-threaded
/// environment. It builds up local batches and then flushes them inline.
struct InPlaceActionBuffer<'a> {
    rule_set: &'a RuleSet,
    match_counter: &'a MatchCounter,
    batches: DenseIdMap<ActionId, ActionState>,
}

impl<'a, 'outer: 'a> ActionBuffer<'a> for InPlaceActionBuffer<'outer> {
    type AsLocal<'b>
        = Self
    where
        'a: 'b;

    fn push_bindings(
        &mut self,
        action: ActionId,
        bindings: &DenseIdMap<Variable, Value>,
        mut to_exec_state: impl FnMut() -> ExecutionState<'a>,
    ) {
        let action_state = self.batches.get_or_default(action);
        action_state.n_runs += 1;
        action_state.len += 1;
        action_state.bindings.push(bindings);
        if action_state.len > VAR_BATCH_SIZE {
            let mut state = to_exec_state();
            state.run_instrs(&self.rule_set.actions[action], &mut action_state.bindings);
            action_state.bindings.clear();
            action_state.len = 0;
        }
    }

    fn flush(&mut self, exec_state: &mut ExecutionState) {
        flush_action_states(
            exec_state,
            &mut self.batches,
            self.rule_set,
            self.match_counter,
        );
    }
    fn recur<Local: Clone + Send + 'a>(
        &mut self,
        local: &mut Local,
        _to_exec_state: impl FnMut() -> ExecutionState<'a> + Send + 'a,
        work: impl for<'b> FnOnce(&mut Local, &mut Self) + Send + 'a,
    ) {
        work(local, self);
    }
}

/// An Action buffer that hands off batches to of actions to rayon to execute.
struct ScopedActionBuffer<'inner, 'scope> {
    scope: &'inner rayon::Scope<'scope>,
    rule_set: &'scope RuleSet,
    match_counter: &'scope MatchCounter,
    batches: DenseIdMap<ActionId, ActionState>,
    needs_flush: bool,
}

impl<'inner, 'scope> ScopedActionBuffer<'inner, 'scope> {
    fn new(
        scope: &'inner rayon::Scope<'scope>,
        rule_set: &'scope RuleSet,
        match_counter: &'scope MatchCounter,
    ) -> Self {
        Self {
            scope,
            rule_set,
            batches: Default::default(),
            match_counter,
            needs_flush: false,
        }
    }
}

impl<'scope> ActionBuffer<'scope> for ScopedActionBuffer<'_, 'scope> {
    type AsLocal<'a>
        = ScopedActionBuffer<'a, 'scope>
    where
        'scope: 'a;
    fn push_bindings(
        &mut self,
        action: ActionId,
        bindings: &DenseIdMap<Variable, Value>,
        mut to_exec_state: impl FnMut() -> ExecutionState<'scope>,
    ) {
        self.needs_flush = true;
        let action_state = self.batches.get_or_default(action);
        action_state.n_runs += 1;
        action_state.len += 1;
        action_state.bindings.push(bindings);
        if action_state.len > VAR_BATCH_SIZE {
            let mut state = to_exec_state();
            let mut bindings = mem::take(&mut action_state.bindings);
            action_state.len = 0;
            let rule_set = self.rule_set;
            self.scope.spawn(move |_| {
                state.run_instrs(&rule_set.actions[action], &mut bindings);
            });
        }
    }

    fn flush(&mut self, exec_state: &mut ExecutionState) {
        flush_action_states(
            exec_state,
            &mut self.batches,
            self.rule_set,
            self.match_counter,
        );
        self.needs_flush = false;
    }
    fn recur<Local: Clone + Send + 'scope>(
        &mut self,
        local: &mut Local,
        mut to_exec_state: impl FnMut() -> ExecutionState<'scope> + Send + 'scope,
        work: impl for<'a> FnOnce(&mut Local, &mut ScopedActionBuffer<'a, 'scope>) + Send + 'scope,
    ) {
        let rule_set = self.rule_set;
        let match_counter = self.match_counter;
        let mut inner = local.clone();
        self.scope.spawn(move |scope| {
            let mut buf: ScopedActionBuffer<'_, 'scope> = ScopedActionBuffer {
                scope,
                rule_set,
                match_counter,
                needs_flush: false,
                batches: Default::default(),
            };
            work(&mut inner, &mut buf);
            if buf.needs_flush {
                flush_action_states(
                    &mut to_exec_state(),
                    &mut buf.batches,
                    buf.rule_set,
                    buf.match_counter,
                );
            }
        });
    }
    fn morsel_size(&mut self, _level: usize) -> usize {
        // Lower morsel size to increase parallelism.
        256
    }
}

fn flush_action_states(
    exec_state: &mut ExecutionState,
    actions: &mut DenseIdMap<ActionId, ActionState>,
    rule_set: &RuleSet,
    match_counter: &MatchCounter,
) {
    for (action, ActionState { bindings, len, .. }) in actions.iter_mut() {
        if *len > 0 {
            exec_state.run_instrs(&rule_set.actions[action], bindings);
            bindings.clear();
            match_counter.inc_matches(action, *len);
            *len = 0;
        }
    }
}

struct MatchCounter {
    matches: IdVec<ActionId, AtomicUsize>,
}

impl MatchCounter {
    fn new(n_ids: usize) -> Self {
        let mut matches = IdVec::with_capacity(n_ids);
        matches.resize_with(n_ids, || AtomicUsize::new(0));
        Self { matches }
    }

    fn inc_matches(&self, action: ActionId, by: usize) {
        self.matches[action].fetch_add(by, std::sync::atomic::Ordering::Relaxed);
    }
    fn read_matches(&self, action: ActionId) -> usize {
        self.matches[action].load(std::sync::atomic::Ordering::Acquire)
    }
}

fn estimate_size(join_stage: &JoinStage, binding_info: &BindingInfo) -> usize {
    join_stage_order_key(join_stage, binding_info).0
}

fn join_stage_order_key(join_stage: &JoinStage, binding_info: &BindingInfo) -> (usize, i32) {
    // Sort increasing by size of scan, decreasing by number of intersections.
    match join_stage {
        JoinStage::Intersect { scans, .. } => (
            scans
                .iter()
                .map(|scan| binding_info.subsets[scan.atom].size())
                .min()
                .unwrap_or(0),
            -(scans.len() as i32),
        ),
        JoinStage::FusedIntersect {
            cover,
            to_intersect,
            ..
        } => (
            binding_info.subsets[cover.to_index.atom].size(),
            -(to_intersect.len() as i32),
        ),
    }
}

fn sort_plan_by_size(order: &mut [usize], instrs: &[JoinStage], binding_info: &mut BindingInfo) {
    order.sort_by_key(|index| join_stage_order_key(&instrs[*index], binding_info));
}
