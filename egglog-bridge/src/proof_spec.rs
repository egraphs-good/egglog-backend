use std::{iter, rc::Rc, sync::Arc};

use core_relations::{
    BaseValuePrinter, ColumnId, DisplacedTableWithProvenance, ExternalFunctionId,
    ProofReason as UfProofReason, ProofStep, RuleBuilder, Value,
};
use hashbrown::{HashMap, HashSet};
use numeric_id::{define_id, DenseIdMap, NumericId};

use crate::{
    new_syntax::{RuleData2, SourceSyntax},
    rule::{AtomId, Bindings, DstVar, Variable},
    syntax::{Binding, RuleRepresentation, TermFragment},
    term_proof_dag::{BaseValueConstant, EqProof, EqReason, TermProof, TermValue},
    ColumnTy, EGraph, FunctionId, GetFirstMatch, QueryEntry, Result, RuleId, SideChannel,
};

define_id!(pub(crate) ReasonSpecId, u32, "A unique identifier for the step in a proof.");

/// Reasons provide extra provenance information accompanying a term being
/// instantiated, or marked as equal to another term. All reasons are pointed
/// to by a row in a terms table.
///
#[derive(Debug)]
pub(crate) enum ProofReason {
    Rule2(RuleData2),
    /// Congrence reasons contain the "old" term id that the new term is equal
    /// to. Pairwise equalty proofs are rebuilt at proof reconstruction time.
    CongRow,
    /// A row that was created with no added justification (e.g. base values).
    Fiat {
        desc: Arc<str>,
    },
}

impl ProofReason {
    pub(crate) fn arity(&self) -> usize {
        // All start with a proof spec id.
        1 + match self {
            ProofReason::CongRow => 1,
            ProofReason::Rule2(data) => data.n_vars(),
            ProofReason::Fiat { .. } => 0,
        }
    }
}

pub(crate) type SyntaxEnv = HashMap<Variable, Arc<TermFragment<Variable>>>;

type TodoMakeSourceSyntaxFieldInProofBuilderNonOptional = ();

pub(crate) struct ProofBuilder {
    pub(crate) rule_description: Arc<str>,
    pub(crate) rule_id: RuleId,
    lhs_atoms: Vec<Vec<QueryEntry>>,
    /// The atom against which to compare during proofs. Serves as a guide for
    /// generating equality proofs.
    to_compare: Vec<usize>,
    rhs_atoms: Vec<Vec<QueryEntry>>,
    lhs_term_vars: Vec<Variable>,
    rhs_term_vars: Vec<Variable>,
    representatives: HashMap<Variable, usize>,
    // The "syntax" fields are used to build a checker for the proofs in this
    // rule.
    pub(crate) syntax_env: SyntaxEnv,
    pub(crate) syntax: RuleRepresentation,

    source_syntax: Option<SourceSyntax>,
    pub(crate) term_vars: DenseIdMap<AtomId, QueryEntry>,
}

pub(crate) struct RebuildVars {
    pub(crate) new_term: Variable,
    pub(crate) reason: Variable,
    pub(crate) before_term: Variable,
}

impl ProofBuilder {
    pub(crate) fn new(description: &str, rule_id: RuleId) -> ProofBuilder {
        ProofBuilder {
            rule_id,
            rule_description: description.into(),
            lhs_atoms: Default::default(),
            rhs_atoms: Default::default(),
            to_compare: Default::default(),
            lhs_term_vars: Default::default(),
            rhs_term_vars: Default::default(),
            representatives: Default::default(),
            syntax_env: Default::default(),
            syntax: Default::default(),
            source_syntax: None,
            term_vars: Default::default(),
        }
    }

    pub(crate) fn add_lhs(&mut self, entries: &[QueryEntry], term_var: Variable) {
        let id_var = entries.last().expect("entries should be nonempty").var();
        let to_compare = *self
            .representatives
            .entry(id_var)
            .or_insert(self.lhs_atoms.len());
        self.lhs_atoms.push(entries.to_vec());
        self.to_compare.push(to_compare);
        self.lhs_term_vars.push(term_var);
    }
    pub(crate) fn add_rhs(&mut self, entries: &[QueryEntry], term_var: Variable) {
        self.rhs_atoms.push(entries.to_vec());
        self.rhs_term_vars.push(term_var);
    }

    /// Generate a proof for a newly rebuilt row.
    pub(crate) fn rebuild_proof(
        &mut self,
        func: FunctionId,
        after: &[QueryEntry],
        vars: RebuildVars,
        db: &mut EGraph,
    ) -> impl Fn(&mut Bindings, &mut RuleBuilder) -> Result<()> + Clone {
        let reason_spec = ProofReason::CongRow;
        let reason_table = db.reason_table(&reason_spec);
        let reason_spec_id = db.cong_spec;
        let reason_counter = db.reason_counter;
        let func_table = db.funcs[func].table;
        let term_table = db.term_table(func_table);
        let term_counter = db.id_counter;
        let after = after.to_vec();
        move |inner, rb| {
            let old_term = inner.mapping[vars.before_term];
            let reason_id = rb.lookup_or_insert(
                reason_table,
                &[Value::new(reason_spec_id.rep()).into(), old_term],
                &[reason_counter.into()],
                ColumnId::new(2),
            )?;
            let mut entries = Vec::new();
            entries.push(Value::new(func.rep()).into());
            for entry in &after[..after.len() - 1] {
                entries.push(inner.convert(entry));
            }
            // Now get the new term value, inserting it if the term is new.
            let term_result = rb.lookup_or_insert(
                term_table,
                &entries,
                &[term_counter.into(), reason_id.into()],
                ColumnId::from_usize(entries.len()),
            )?;
            inner.mapping.insert(vars.new_term, term_result.into());
            inner.mapping.insert(vars.reason, reason_id.into());
            Ok(())
        }
    }

    /// Construct a reason associated with this rule and bind it to `reason_var`.
    pub(crate) fn make_reason(
        &mut self,
        reason_var: Variable,
        db: &mut EGraph,
    ) -> impl Fn(&mut Bindings, &mut RuleBuilder) -> Result<()> + Clone {
        let syntax = self
            .source_syntax
            .as_ref()
            .cloned()
            .expect("must specify syntax when proofs are enabled");
        let cb = self.create_reason(syntax, db);
        move |bndgs, rb| {
            let res = cb(bndgs, rb)?;
            bndgs.mapping.insert(reason_var, res.into());
            Ok(())
        }
    }

    /// Generate a callback that will add a row to the term database, as well as
    /// a reason for that term existing.
    pub(crate) fn new_row(
        &mut self,
        func: FunctionId,
        entries: Vec<QueryEntry>,
        term_var: Variable,
        reason_var: Variable,
        db: &mut EGraph,
    ) -> impl Fn(&mut Bindings, &mut RuleBuilder) -> Result<()> + Clone {
        let make_reason = self.make_reason(reason_var, db);
        self.add_rhs(&entries, term_var);
        let func_table = db.funcs[func].table;
        let term_table = db.term_table(func_table);
        let func_val = Value::new(func.rep());
        let res_var = entries.last().unwrap().var();
        let rhs_term = Arc::new(TermFragment::App(
            func,
            entries[..entries.len() - 1]
                .iter()
                .map(|e| e.to_syntax(db).unwrap())
                .collect(),
        ));
        self.syntax_env
            .entry(res_var)
            .or_insert_with(|| rhs_term.clone());
        self.syntax.rhs_bindings.push(Binding {
            var: res_var,
            syntax: rhs_term,
        });
        move |inner, rb| {
            if !inner.mapping.contains_key(reason_var) {
                make_reason(inner, rb)?;
            }
            let mut translated = Vec::new();
            translated.push(func_val.into());
            for entry in &entries[0..entries.len() - 1] {
                translated.push(inner.convert(entry));
            }
            translated.push(inner.mapping[term_var]);
            translated.push(inner.mapping[reason_var]);
            rb.insert(term_table, &translated)?;
            Ok(())
        }
    }
    pub(crate) fn register_prim(
        &mut self,
        func: ExternalFunctionId,
        args: &[QueryEntry],
        res: Variable,
        ty: ColumnTy,
        db: &EGraph,
    ) {
        let app = Arc::new(TermFragment::Prim(
            func,
            args.iter().map(|v| v.to_syntax(db).unwrap()).collect(),
            ty,
        ));
        assert!(self.syntax_env.insert(res, app.clone()).is_none());
        self.syntax.rhs_bindings.push(Binding {
            var: res,
            syntax: app,
        });
    }
}

#[derive(Default)]
pub(crate) struct ProofReconstructionState {
    in_progress: HashSet<Value>,
    term_memo: HashMap<Value, Rc<TermProof>>,
    eq_memo: HashMap<(Value, Value), Rc<EqProof>>,

    // maps for "hash-consing" proofs
    id: HashMap<*const TermProof, Rc<EqProof>>,
    backwards: HashMap<*const EqProof, Rc<EqProof>>,
    base: HashMap<(*const TermProof, *const TermProof, *const TermProof), Rc<EqProof>>,
}

impl ProofReconstructionState {
    fn id(&mut self, term: Rc<TermProof>) -> Rc<EqProof> {
        self.id
            .entry(term.as_ref() as *const _)
            .or_insert_with(move || {
                Rc::new(EqProof {
                    lhs: term.clone(),
                    rhs: term.clone(),
                    reason: EqReason::Id(term),
                })
            })
            .clone()
    }

    fn backwards(&mut self, eq: Rc<EqProof>) -> Rc<EqProof> {
        self.backwards
            .entry(eq.as_ref() as *const _)
            .or_insert_with(move || {
                Rc::new(EqProof {
                    lhs: eq.rhs.clone(),
                    rhs: eq.lhs.clone(),
                    reason: EqReason::Backwards(eq),
                })
            })
            .clone()
    }

    fn base(&mut self, term: Rc<TermProof>, lhs: Rc<TermProof>, rhs: Rc<TermProof>) -> Rc<EqProof> {
        self.base
            .entry((
                term.as_ref() as *const _,
                lhs.as_ref() as *const _,
                rhs.as_ref() as *const _,
            ))
            .or_insert_with(move || {
                Rc::new(EqProof {
                    lhs,
                    rhs,
                    reason: EqReason::Base(term),
                })
            })
            .clone()
    }
}

// Proof reconstruction code. A lot of this code assumes that it is running
// outside of the "hot path" for an application; it allocates a lot of small
// vectors, does a good amount of not-exactly-stack-safe recursion, etc.

impl EGraph {
    pub(crate) fn explain_term_inner(
        &mut self,
        term_id: Value,
        state: &mut ProofReconstructionState,
    ) -> Rc<TermProof> {
        if let Some(prev) = state.term_memo.get(&term_id) {
            return prev.clone();
        }
        assert!(
            state.in_progress.insert(term_id),
            "term id {term_id:?} has a cycle in its explanation!"
        );
        let term_row = self.get_term_row(term_id);
        debug_assert_eq!(term_row[term_row.len() - 2], term_id);
        // We have something like (F x y) => `term_id` + `reason`
        // There are two things to do at this juncture:
        // 1. Explain the children (namely `x` and `y`)
        // 2. Explain anything about `reason`.

        let reason = *term_row.last().unwrap();
        let reason_row = self.get_reason(reason);
        let spec = self.proof_specs[ReasonSpecId::new(reason_row[0].rep())].clone();
        let res = match &*spec {
            ProofReason::Rule2(data) => {
                let todo_fill_in = 1;
                todo!()
            }
            ProofReason::CongRow => self.create_cong_proof(reason_row[1], term_id, state),
            ProofReason::Fiat { desc } => {
                let func_id = FunctionId::new(term_row[0].rep());
                let info = &self.funcs[func_id];
                let schema = info.schema.clone();
                let func = info.name.clone();
                let desc = desc.clone();
                let row = self.get_term_values(
                    term_row[1..].iter().zip(schema[0..schema.len() - 1].iter()),
                    state,
                );
                Rc::new(TermProof::Fiat {
                    desc,
                    func,
                    row,
                    func_id,
                })
            }
        };

        state.in_progress.remove(&term_id);
        state.term_memo.insert(term_id, res.clone());
        res
    }

    pub(crate) fn explain_terms_equal_inner(
        &mut self,
        l: Value,
        r: Value,
        state: &mut ProofReconstructionState,
    ) -> Rc<EqProof> {
        if let Some(prev) = state.eq_memo.get(&(l, r)) {
            return prev.clone();
        }
        #[allow(clippy::never_loop)]
        let res = loop {
            // We are using a loop as a block that we can break out of.
            if l == r {
                let term_proof = self.explain_term_inner(l, state);
                break state.id(term_proof);
            }
            let uf_table = self
                .db
                .get_table(self.uf_table)
                .as_any()
                .downcast_ref::<DisplacedTableWithProvenance>()
                .unwrap();

            let Some(steps) = uf_table.get_proof(l, r) else {
                panic!("attempting to explain why two terms ({l:?} and {r:?}) are equal, but they aren't equal");
            };

            assert!(!steps.is_empty(), "empty proof for equality");

            break if steps.len() == 1 {
                let ProofStep { lhs, rhs, reason } = &steps[0];
                assert_eq!(*lhs, l);
                assert_eq!(*rhs, r);
                match reason {
                    UfProofReason::Forward(reason) => {
                        self.create_eq_proof_step(*reason, *lhs, *rhs, state)
                    }
                    UfProofReason::Backward(reason) => {
                        let base = self.create_eq_proof_step(*reason, *rhs, *lhs, state);
                        state.backwards(base)
                    }
                }
            } else {
                assert!(
                    steps
                        .iter()
                        .zip(steps.iter().skip(1))
                        .all(|(x, y)| x.rhs == y.lhs),
                    "malformed proofs out of UF: {steps:?}"
                );
                let subproofs: Vec<_> = steps
                    .into_iter()
                    .map(|ProofStep { lhs, rhs, reason }| match reason {
                        UfProofReason::Forward(reason) => {
                            self.create_eq_proof_step(reason, lhs, rhs, state)
                        }
                        UfProofReason::Backward(reason) => {
                            let base = self.create_eq_proof_step(reason, rhs, lhs, state);
                            state.backwards(base)
                        }
                    })
                    .collect();
                let lhs = subproofs[0].lhs.clone();
                let rhs = subproofs.last().unwrap().rhs.clone();
                Rc::new(EqProof {
                    lhs,
                    rhs,
                    reason: EqReason::Trans(subproofs),
                })
            };
        };
        state.eq_memo.insert((l, r), res.clone());
        res
    }

    fn create_cong_proof(
        &mut self,
        old_term_id: Value,
        new_term_id: Value,
        state: &mut ProofReconstructionState,
    ) -> Rc<TermProof> {
        let old_term = self.get_term_row(old_term_id);
        let old_term_proof = self.explain_term_inner(old_term_id, state);
        let new_term = self.get_term_row(new_term_id);
        let func_id = FunctionId::new(old_term[0].rep());
        let info = &self.funcs[func_id];
        let func: Arc<str> = info.name.clone();
        let schema = info.schema.clone();
        let pairwise_eq = self.lift_to_values(
            old_term[1..]
                .iter()
                .zip(new_term[1..].iter())
                .zip(schema[0..schema.len() - 1].iter()),
            |slf, state, (old, new)| slf.explain_terms_equal_inner(*old, *new, state),
            |(old, new)| {
                assert_eq!(*old, *new, "base values must be equal");
                *old
            },
            state,
        );
        Rc::new(TermProof::Cong {
            func_id,
            func,
            old_term: old_term_proof,
            pairwise_eq,
        })
    }

    fn project_value(&mut self, val: Value, col: usize) -> Value {
        let row = self.get_term_row(val);
        row[col + 1]
    }

    fn create_eq_proof_step(
        &mut self,
        reason_id: Value,
        l: Value,
        r: Value,
        state: &mut ProofReconstructionState,
    ) -> Rc<EqProof> {
        let reason_row = self.get_reason(reason_id);
        let spec = self.proof_specs[ReasonSpecId::new(reason_row[0].rep())].clone();
        let l_term = self.explain_term_inner(l, state);
        match &*spec {
            ProofReason::Rule2(data) => {
                let todo_fill_in = 1;
                todo!()
            }
            ProofReason::CongRow => {
                let l_term = self.explain_term_inner(l, state);
                let proof = self.create_cong_proof(l, r, state);
                state.base(proof.clone(), l_term, proof)
            }
            ProofReason::Fiat { .. } => {
                // NB: we could add this if we wanted to.
                panic!("fiat reason being used to explain equality, rather than a row's existence")
            }
        }
    }

    fn get_term_values<'a, 'b>(
        &mut self,
        term_with_schema: impl Iterator<Item = (&'a Value, &'b ColumnTy)>,
        state: &mut ProofReconstructionState,
    ) -> Vec<TermValue<TermProof>> {
        self.lift_to_values(
            term_with_schema,
            |slf, state, child| slf.explain_term_inner(*child, state),
            |v| *v,
            state,
        )
    }

    fn lift_to_values<'a, 'b, T, R>(
        &mut self,
        term_with_schema: impl Iterator<Item = (T, &'b ColumnTy)>,
        mut f: impl FnMut(&mut EGraph, &mut ProofReconstructionState, T) -> Rc<R>,
        mut to_value: impl FnMut(T) -> Value,
        state: &mut ProofReconstructionState,
    ) -> Vec<TermValue<R>> {
        term_with_schema
            .map(|(child, ty)| match ty {
                ColumnTy::Id => TermValue::SubTerm(f(self, state, child)),
                ColumnTy::Base(p) => {
                    let interned = to_value(child);
                    TermValue::Base(BaseValueConstant {
                        ty: *p,
                        interned,
                        rendered: format!(
                            "{:?}",
                            BaseValuePrinter {
                                base: self.db.base_values(),
                                ty: *p,
                                val: interned,
                            }
                        )
                        .into(),
                    })
                }
            })
            .collect()
    }

    fn get_term_row(&mut self, term_id: Value) -> Vec<Value> {
        let mut atom = Vec::<DstVar>::new();
        let mut cur = 0;
        loop {
            // Iterate over the table by index to avoid borrowing issues with the
            // call to `get_proof`.
            let Some((keys, table)) = self.term_tables.get_index(cur) else {
                panic!("failed to find term with id {term_id:?}")
            };

            let gfm_sc = SideChannel::default();
            let gfm_id = self.db.add_external_function(GetFirstMatch(gfm_sc.clone()));
            {
                let mut rsb = self.db.new_rule_set();
                let mut qb = rsb.new_rule();
                for _ in 0..*keys + 1 {
                    atom.push(qb.new_var().into());
                }
                atom.push(term_id.into());
                atom.push(qb.new_var().into()); // reason
                qb.add_atom(*table, &atom, iter::empty()).unwrap();
                let mut rb = qb.build();
                rb.call_external(gfm_id, &atom).unwrap();
                rb.build();
                let rs = rsb.build();
                atom.clear();
                self.db.run_rule_set(&rs);
            }
            self.db.free_external_function(gfm_id);

            if let Some(vals) = gfm_sc.lock().unwrap().take() {
                return vals;
            }
            cur += 1;
        }
    }

    fn get_reason(&mut self, reason_id: Value) -> Vec<Value> {
        let mut atom = Vec::<DstVar>::new();
        let mut cur = 0;
        loop {
            // Iterate over the table by index to avoid borrowing issues with the
            // call to `get_proof`.
            let (arity, table) = self
                .reason_tables
                .get_index(cur)
                .unwrap_or_else(|| panic!("failed to find reason with id {reason_id:?}"));

            let gfm_sc = SideChannel::default();
            let gfm_id = self.db.add_external_function(GetFirstMatch(gfm_sc.clone()));
            {
                let mut rsb = self.db.new_rule_set();
                let mut qb = rsb.new_rule();
                for _ in 0..*arity {
                    atom.push(qb.new_var().into());
                }
                atom.push(reason_id.into());
                qb.add_atom(*table, &atom, iter::empty()).unwrap();
                let mut rb = qb.build();
                rb.call_external(gfm_id, &atom).unwrap();
                rb.build();
                let rs = rsb.build();
                atom.clear();
                self.db.run_rule_set(&rs);
            }
            self.db.free_external_function(gfm_id);

            if let Some(vals) = gfm_sc.lock().unwrap().take() {
                return vals;
            }
            cur += 1;
        }
    }
}
