//! A proof format for egglog programs, based on the Roq format and checker from Tia Vu, Ryan
//! Doegens, and Oliver Flatt.
use std::rc::Rc;

use core_relations::Value;
use hashbrown::HashMap;
use indexmap::IndexSet;
use numeric_id::{define_id, DenseIdMap, IdVec, NumericId};

use crate::{rule::Variable, FunctionId};

define_id!(pub(crate) ProofId, u32, "an id identifying proofs within a [`ProofStore`]");
define_id!(pub(crate) TermId, u32, "an id identifying terms within a [`TermDag`]");

#[derive(Default, Clone)]
pub struct TermDag {
    store: IndexSet<Term>,
}

impl TermDag {
    pub fn get_or_insert(&self, term: &Term) -> TermId {
        if let Some((index, _)) = self.store.get_full(term) {
            TermId::from_usize(index)
        } else {
            let id = TermId::from_usize(self.store.len());
            self.store.insert(term.clone());
            id
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Var {
        id: Variable,
        sym: Option<Rc<str>>,
    },
    Constant {
        id: Value,
        rendered: Option<Rc<str>>,
    },
    Func {
        id: FunctionId,
        args: Vec<TermId>,
    },
}

#[derive(Clone)]
pub struct ProofStore {
    store: Vec<ProofTerm>,
    memo: HashMap<ProofTerm, ProofId>,
    termdag: TermDag,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Proposition {
    TOk(TermId),
    TEq(TermId, TermId),
}

// todo how to ignore this warning?
#[allow(clippy::enum_variant_names)]
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ProofTerm {
    /// proves a Proposition based on a rule application
    /// the subsitution gives the mapping from variables to terms
    /// the body_pfs gives proofs for each of the conditions in the query of the rule
    /// the act_pf gives a location in the action of the proposition
    PRule {
        rule_name: Rc<str>,
        subst: DenseIdMap<Variable, TermId>,
        body_pfs: Vec<ProofId>,
        result: Proposition,
    },
    /// A term is equal to itself- proves the proposition t = t
    PRefl {
        t_ok_pf: ProofId,
        t: Term,
    },
    /// The symmetric equality of eq_pf
    PSym {
        eq_pf: ProofId,
    },
    PTrans {
        pfxy: ProofId,
        pfyz: ProofId,
    },
    /// get a proof for the child of a term given a proof of a term
    PProj {
        pf_f_args_ok: ProofId,
        arg_idx: usize,
    },
    /// Proves f(x1, y1, ...) = f(x2, y2, ...) where f is fun_sym
    /// A proof via congruence- one proof for each child of the term
    /// pf_f_args_ok is a proof that the term with the lhs children is valid
    ///
    PCong {
        pf_args_eq: Vec<ProofId>,
        pf_f_args_ok: ProofId,
        func: FunctionId,
    },
}
