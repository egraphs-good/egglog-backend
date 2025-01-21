//! Support for containers
//!
//! Containers behave a lot like primitives in egglog. They are implemented differently because
//! their ids share a space with other Ids in the egraph and as a result, their ids need to be
//! sparse.
//!
//! This is a relatively "eagler" implementation of containers, reflecting egglog's current
//! semantics. One could imagine a variant of containers in which they behave more like egglog
//! functions than primitives.

use std::{
    any::{Any, TypeId},
    hash::{Hash, Hasher},
    ops::Deref,
};

use crossbeam_queue::SegQueue;
use dashmap::SharedValue;
use numeric_id::{define_id, DenseIdMap, IdVec, NumericId};
use rayon::{
    iter::{ParallelBridge, ParallelIterator},
    prelude::*,
};
use rustc_hash::FxHasher;

use crate::{
    common::{DashMap, IndexSet, InternTable, SubsetTracker},
    table_spec::Rewriter,
    ColumnId, CounterId, ExecutionState, Offset, SubsetRef, TableId, TaggedRowBuffer, Value,
    WrappedTable,
};

define_id!(pub ContainerId, u32, "an identifier for containers");

pub type MergeFn = dyn Fn(&mut ExecutionState, Value, Value) -> Value + Send + Sync;

#[derive(Default)]
pub struct Containers {
    subset_tracker: SubsetTracker,
    container_ids: InternTable<TypeId, ContainerId>,
    data: DenseIdMap<ContainerId, Box<dyn DynamicContainerEnv + Send + Sync>>,
}

impl Containers {
    pub fn new() -> Self {
        Default::default()
    }

    fn get<C: Container>(&self) -> Option<&ContainerEnv<C>> {
        let id = self.container_ids.intern(&TypeId::of::<C>());
        let res = self.data.get(id)?.as_any();
        Some(res.downcast_ref::<ContainerEnv<C>>().unwrap())
    }

    /// Iterate over the containers of the given type.
    pub fn for_each<C: Container>(&self, mut f: impl FnMut(&C, Value)) {
        let Some(env) = self.get::<C>() else {
            return;
        };
        for ent in env.to_id.iter() {
            f(ent.key(), *ent.value());
        }
    }

    /// Get the container associated with the value `val` in the database. The caller must know the
    /// type of the container.
    ///
    /// The return type of this function may contain lock guards. Attempts to modify the contents
    /// of the containers database may deadlock if the given guard has not been dropped.
    pub fn get_val<C: Container>(&self, val: Value) -> Option<impl Deref<Target = C> + '_> {
        self.get::<C>()?.get_container(val)
    }

    pub fn register_val<C: Container>(
        &self,
        container: C,
        exec_state: &mut ExecutionState,
    ) -> Value {
        let env = self
            .get::<C>()
            .expect("must register container type before registering a value");
        env.get_or_insert(&container, exec_state)
    }

    /// Apply the given rewrite rule to the contents of each container.
    pub fn rewrite_all(
        &mut self,
        table_id: TableId,
        table: &WrappedTable,
        exec_state: &mut ExecutionState,
    ) -> bool {
        let Some(rewriter) = table.rewriter(&[]) else {
            return false;
        };
        let to_scan = rewriter.hint_col().map(|_| {
            // We may attempt an incremental rewrite.
            self.subset_tracker.recent_updates(table_id, table)
        });
        if do_parallel() {
            self.data
                .iter_mut()
                .zip(std::iter::repeat_with(|| exec_state.new_handle()))
                .par_bridge()
                .map(|((_, env), mut exec_state)| {
                    env.apply_rewrite(
                        table,
                        &*rewriter,
                        to_scan.as_ref().map(|x| x.as_ref()),
                        &mut exec_state,
                    )
                })
                .max()
                .unwrap_or(false)
        } else {
            let mut changed = false;
            for (_, env) in self.data.iter_mut() {
                changed |= env.apply_rewrite(
                    table,
                    &*rewriter,
                    to_scan.as_ref().map(|x| x.as_ref()),
                    exec_state,
                );
            }
            changed
        }
    }

    /// Add a new container type to the given [`Containers`] instance.
    ///
    /// Container types need a meaans of generating fresh ids (`id_counter`) along with a means of
    /// merging conflicting ids (`merge_fn`).
    pub fn register_type<C: Container>(
        &mut self,
        id_counter: CounterId,
        merge_fn: impl Fn(&mut ExecutionState, Value, Value) -> Value + Send + Sync + 'static,
    ) -> ContainerId {
        let id = self.container_ids.intern(&TypeId::of::<C>());
        self.data.get_or_insert(id, || {
            Box::new(ContainerEnv::<C>::new(Box::new(merge_fn), id_counter))
        });
        id
    }
}

/// A trait implemented by container types.
///
/// Containers behave a lot like primitives, but they include extra trait methods to support
/// rebuilding of container contents and merging containers that become equal after a rewrite pass
/// as taken place.
pub trait Container: Hash + Eq + Clone + Send + Sync + 'static {
    /// Rewrite an additional container in place according the the given [`Rewriter`].
    ///
    /// If this method returns `false` then the container must not have been modified (i.e. it must
    /// hash to the same value, and compare equal to a copy of itself before the call).
    fn rewrite_contents(&mut self, rewriter: &dyn Rewriter) -> bool;

    /// Iterate over the contents of the container.
    ///
    /// Note that containers can be more structured than just a sequence of values. This iterator
    /// is used to populate an index that in turn is used to speed up rewrites. If a value in the
    /// container is eligible for a rewrite and it is not mentioned by this iterator, the outer
    /// [`ContainerEnv`] may skip rewriting this container.
    fn iter(&self) -> impl Iterator<Item = Value> + '_;
}

pub trait DynamicContainerEnv: Any + Send + Sync {
    fn as_any(&self) -> &dyn Any;
    fn apply_rewrite(
        &mut self,
        table: &WrappedTable,
        rewriter: &dyn Rewriter,
        subset: Option<SubsetRef>,
        exec_state: &mut ExecutionState,
    ) -> bool;
}

fn hash_container(container: &impl Container) -> u64 {
    let mut hasher = FxHasher::default();
    container.hash(&mut hasher);
    hasher.finish()
}

struct ContainerEnv<C> {
    merge_fn: Box<MergeFn>,
    counter: CounterId,
    to_id: DashMap<C, Value>,
    to_container: DashMap<Value, (usize /* hash code */, usize /* map */)>,
    /// Map from a Value to the set of ids of containers that contain that value.
    val_index: DashMap<Value, IndexSet<Value>>,
}

impl<C: Container> DynamicContainerEnv for ContainerEnv<C> {
    fn as_any(&self) -> &dyn Any {
        self
    }

    fn apply_rewrite(
        &mut self,
        table: &WrappedTable,
        rewriter: &dyn Rewriter,
        subset: Option<SubsetRef>,
        exec_state: &mut ExecutionState,
    ) -> bool {
        if let Some(subset) = subset {
            if incremental_rebuild(subset.size(), self.to_id.len(), do_parallel()) {
                return self.apply_rewrite_incremental(
                    table,
                    rewriter,
                    exec_state,
                    subset,
                    rewriter.hint_col().unwrap(),
                );
            }
        }
        self.apply_rewrite_nonincremental(rewriter, exec_state)
    }
}

impl<C: Container> ContainerEnv<C> {
    pub fn new(merge_fn: Box<MergeFn>, counter: CounterId) -> Self {
        Self {
            merge_fn,
            counter,
            to_id: DashMap::default(),
            to_container: DashMap::default(),
            val_index: DashMap::default(),
        }
    }

    fn get_or_insert(&self, container: &C, exec_state: &mut ExecutionState) -> Value {
        match self.to_id.get(container) {
            Some(value) => *value,
            None => {
                let value = Value::from_usize(exec_state.inc_counter(self.counter));
                self.to_id.insert(container.clone(), value);
                let target_map = self.to_id.determine_map(container);
                // This assertion is here because in parallel rebuilding we use `to_container` to
                // compute the intended shard for to_id, because we have a mutable borrow of
                // `to_container` that means we cannot call `determine_map` on `to_id`.
                debug_assert_eq!(
                    target_map,
                    self.to_container
                        .determine_shard(hash_container(container) as usize)
                );
                self.to_container
                    .insert(value, (hash_container(container) as usize, target_map));
                for val in container.iter() {
                    self.val_index.entry(val).or_default().insert(value);
                }
                value
            }
        }
    }

    fn insert_owned(&self, container: C, value: Value, exec_state: &mut ExecutionState) {
        let hc = hash_container(&container);
        let target_map = self.to_id.determine_map(&container);
        match self.to_id.entry(container) {
            dashmap::Entry::Occupied(mut occ) => {
                let result = (self.merge_fn)(exec_state, *occ.get(), value);
                let old_val = *occ.get();
                if result != old_val {
                    self.to_container.remove(&old_val);
                    self.to_container.insert(result, (hc as usize, target_map));
                    *occ.get_mut() = result;
                    for val in occ.key().iter() {
                        let mut index = self.val_index.entry(val).or_default();
                        index.swap_remove(&old_val);
                        index.insert(result);
                    }
                }
            }
            dashmap::Entry::Vacant(vacant_entry) => {
                self.to_container.insert(value, (hc as usize, target_map));
                for val in vacant_entry.key().iter() {
                    self.val_index.entry(val).or_default().insert(value);
                }
                vacant_entry.insert(value);
            }
        }
    }
    fn apply_rewrite_incremental(
        &mut self,
        table: &WrappedTable,
        rewriter: &dyn Rewriter,
        exec_state: &mut ExecutionState,
        to_scan: SubsetRef,
        search_col: ColumnId,
    ) -> bool {
        // NB: there is no parallel implementation as of now.
        //
        // Implementing one should be straightforward, but we should wait for a real benchmark that
        // requires it. It's possible that incremental rebuilding will only be profitable when the
        // total number of ids to rebuild is small, in which case the overhead of parallelism may
        // not be worth it in the first place.
        let mut changed = false;
        let mut buf = TaggedRowBuffer::new(1);
        table.scan_project(
            to_scan,
            &[search_col],
            Offset::new(0),
            usize::MAX,
            &[],
            &mut buf,
        );
        // For each value in the buffer, rewrite all containers that mention it.
        let mut to_rebuild = IndexSet::<Value>::default();
        for (_, row) in buf.iter() {
            to_rebuild.insert(row[0]);
            let Some(ids) = self.val_index.get(&row[0]) else {
                continue;
            };
            to_rebuild.extend(&*ids);
        }
        for id in to_rebuild {
            let Some((hc, target_map)) = self.to_container.get(&id).map(|x| *x) else {
                continue;
            };
            let shard_mut = self.to_id.shards_mut()[target_map].get_mut();
            let Some((mut container, _)) =
                shard_mut.remove_entry(hc as u64, |(_, v)| *v.get() == id)
            else {
                continue;
            };
            changed |= container.rewrite_contents(rewriter);
            self.insert_owned(container, id, exec_state);
        }
        changed
    }

    fn apply_rewrite_nonincremental(
        &mut self,
        rewriter: &dyn Rewriter,
        exec_state: &mut ExecutionState,
    ) -> bool {
        if do_parallel() {
            return self.apply_rewrite_nonincremental_parallel(rewriter, exec_state);
        }
        let mut changed = false;
        let mut to_reinsert = Vec::new();
        let shards = self.to_id.shards_mut();
        for shard in shards.iter_mut() {
            let shard = shard.get_mut();
            // SAFETY: the iterator does not outlive `shard`.
            for bucket in unsafe { shard.iter() } {
                // SAFETY: the bucket is valid; we just got it from the iterator.
                let (container, val) = unsafe { bucket.as_mut() };
                let old_val = *val.get();
                let new_val = rewriter.rewrite_val(old_val);
                let container_changed = container.rewrite_contents(rewriter);
                if !container_changed && new_val == old_val {
                    // Nothing changed about this entry. Leave it in place.
                    continue;
                }
                changed = true;
                if container_changed {
                    // The container changed. Remove both map entries then reinsert.
                    // SAFETY: This is a valid bucket. Furthermore, iterators remain valid if
                    // buckets they have already yielded have been removed.
                    let ((container, _), _) = unsafe { shard.remove(bucket) };
                    self.to_container.remove(&old_val);
                    to_reinsert.push((container, new_val));
                } else {
                    // Just the value changed. Leave the container in place.
                    *val.get_mut() = new_val;
                    let prev = self.to_container.remove(&old_val).unwrap().1;
                    self.to_container.insert(new_val, prev);
                }
            }
        }
        for (container, val) in to_reinsert {
            self.insert_owned(container, val, exec_state);
        }
        changed
    }

    fn apply_rewrite_nonincremental_parallel(
        &mut self,
        rewriter: &dyn Rewriter,
        exec_state: &mut ExecutionState,
    ) -> bool {
        // This is very similar to the serial variant. The main difference is that
        // `to_reinsert` isn't a flat vector. It's instead a vector of queues - one per
        // destination map shard. This lets us do a bulk insertion in parallel without having
        // to grab a lock per container.
        let mut to_reinsert = IdVec::<usize /* to_id shard */, SegQueue<(C, Value)>>::default();
        to_reinsert.resize_with(self.to_id.shards().len(), Default::default);

        let shards = self.to_id.shards_mut();
        let changed = shards
            .par_iter_mut()
            .map(|shard| {
                let mut changed = false;
                let shard = shard.get_mut();
                // SAFETY: the iterator does not outlive `shard`.
                for bucket in unsafe { shard.iter() } {
                    // SAFETY: the bucket is valid; we just got it from the iterator.
                    let (container, val) = unsafe { bucket.as_mut() };
                    let old_val = *val.get();
                    let new_val = rewriter.rewrite_val(old_val);
                    let container_changed = container.rewrite_contents(rewriter);
                    if !container_changed && new_val == old_val {
                        // Nothing changed about this entry. Leave it in place.
                        continue;
                    }
                    changed = true;
                    if container_changed {
                        // The container changed. Remove both map entries then reinsert.
                        // SAFETY: This is a valid bucket. Furthermore, iterators remain valid if
                        // buckets they have already yielded have been removed.
                        let ((container, _), _) = unsafe { shard.remove(bucket) };
                        self.to_container.remove(&old_val);
                        // Spooky: we're using `to_container` to determine the shard for
                        // `to_id`. We are assuming that the # shards determination is
                        // deterministic here. There is a debug assertion in `get_or_insert`
                        // that attempts to verify this.
                        let shard = self
                            .to_container
                            .determine_shard(hash_container(&container) as usize);
                        to_reinsert[shard].push((container, new_val));
                    } else {
                        // Just the value changed. Leave the container in place.
                        *val.get_mut() = new_val;
                        let prev = self.to_container.remove(&old_val).unwrap().1;
                        self.to_container.insert(new_val, prev);
                    }
                }
                changed
            })
            .max()
            .unwrap_or(false);

        shards
            .iter_mut()
            .enumerate()
            .map(|(i, shard)| (i, shard, exec_state.new_handle()))
            .par_bridge()
            .for_each(|(shard_id, shard, mut exec_state)| {
                // This bit is a real slog. Once Dashmap updates from RawTable to HashTable for
                // the underlying shard, this will get a little better.
                //
                // NB: We are probably leaving some paralellism on the floor with these calls
                // to `to_container` and `val_index`.
                let shard = shard.get_mut();
                let queue = &to_reinsert[shard_id];
                while let Some((container, val)) = queue.pop() {
                    let hc = hash_container(&container);
                    let target_map = self.to_container.determine_shard(hc as usize);
                    match shard.find_or_find_insert_slot(
                        hc,
                        |(c, _)| c == &container,
                        |(c, _)| hash_container(c),
                    ) {
                        Ok(bucket) => {
                            // SAFETY: the bucket is valid; we just got it from the shard and
                            // we have not done any operations that can invalidate the bucket.
                            let (container, val_slot) = unsafe { bucket.as_mut() };
                            let old_val = *val_slot.get();
                            let result = (self.merge_fn)(&mut exec_state, old_val, val);
                            if result != old_val {
                                self.to_container.remove(&old_val);
                                self.to_container.insert(result, (hc as usize, target_map));
                                *val_slot.get_mut() = result;
                                for val in container.iter() {
                                    let mut index = self.val_index.entry(val).or_default();
                                    index.swap_remove(&old_val);
                                    index.insert(result);
                                }
                            }
                        }
                        Err(slot) => {
                            self.to_container.insert(val, (hc as usize, target_map));
                            for v in container.iter() {
                                self.val_index.entry(v).or_default().insert(val);
                            }
                            // SAFETY: We just got this slot from `find_or_find_insert_slot`
                            // and we have not mutated the map at all since then.
                            unsafe {
                                shard.insert_in_slot(hc, slot, (container, SharedValue::new(val)));
                            }
                        }
                    }
                }
            });
        changed
    }

    fn get_container(&self, value: Value) -> Option<impl Deref<Target = C> + '_> {
        let (hc, target_map) = *self.to_container.get(&value)?;
        let shard = &self.to_id.shards()[target_map];
        let read_guard = shard.read();
        let val_ptr: *const (C, _) = shard
            .read()
            .find(hc as u64, |(_, v)| *v.get() == value)?
            .as_ptr();
        struct ValueDeref<'a, T, Guard> {
            _guard: Guard,
            data: &'a T,
        }

        impl<T, Guard> Deref for ValueDeref<'_, T, Guard> {
            type Target = T;

            fn deref(&self) -> &T {
                self.data
            }
        }

        Some(ValueDeref {
            _guard: read_guard,
            // SAFETY: the value will remain valid for as long as `read_guard` is in scope.
            data: unsafe {
                let unwrapped: &(C, _) = &*val_ptr;
                &unwrapped.0
            },
        })
    }
}

// We use debug_assertions to gate the random choice here because most of the test coverage here
// comes from egglog-bridge. And cfg(test) does not propagate between crates.

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

fn incremental_rebuild(_uf_size: usize, _table_size: usize, _parallel: bool) -> bool {
    #[cfg(debug_assertions)]
    {
        use rand::Rng;
        rand::thread_rng().gen_bool(0.5)
    }
    #[cfg(not(debug_assertions))]
    {
        if _parallel {
            _table_size > 1000 && _uf_size * 512 <= _table_size
        } else {
            _table_size > 1000 && _uf_size * 8 <= _table_size
        }
    }
}