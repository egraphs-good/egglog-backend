//! A proof format for egglog programs, based on the Roq format and checker from Tia Vu, Ryan
//! Doegens, and Oliver Flatt.
use std::{io, rc::Rc};

use core_relations::Value;
use hashbrown::{hash_map::Entry, HashMap};
use indexmap::IndexSet;
use numeric_id::{define_id, DenseIdMap, IdVec, NumericId};

use crate::{rule::Variable, FunctionId};

define_id!(pub TermProofId, u32, "an id identifying proofs of terms within a [`ProofStore`]");
define_id!(pub EqProofId, u32, "an id identifying proofs of equality between two terms within a [`ProofStore`]");
define_id!(pub TermId, u32, "an id identifying terms within a [`TermDag`]");

#[derive(Default, Clone)]
pub struct TermDag {
    store: IndexSet<Term>,
}

impl TermDag {
    /// Print the term in a human-readable format to the given writer.
    pub fn print_term(&self, term: TermId, writer: &mut impl io::Write) -> io::Result<()> {
        let term = self.store.get_index(term.index()).unwrap();
        match term {
            Term::Constant { id, rendered } => {
                if let Some(rendered) = rendered {
                    write!(writer, "{rendered}")?;
                } else {
                    write!(writer, "c{}", id.index())?;
                }
            }
            Term::Func { id, args } => {
                write!(writer, "({}", id.index())?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(writer, ", ")?;
                    }
                    self.print_term(*arg, writer)?;
                }
                write!(writer, ")")?;
            }
        }
        Ok(())
    }

    /// Add the given [`Term`] to the store, returning its [`TermId`].
    ///
    /// The [`TermId`]s in this term should point into this same [`TermDag`].
    pub fn get_or_insert(&mut self, term: &Term) -> TermId {
        if let Some((index, _)) = self.store.get_full(term) {
            TermId::from_usize(index)
        } else {
            let id = TermId::from_usize(self.store.len());
            self.store.insert(term.clone());
            id
        }
    }

    pub(crate) fn proj(&self, term: TermId, arg_idx: usize) -> TermId {
        let term = self.store.get_index(term.index()).unwrap();
        match term {
            Term::Func { args, .. } => {
                if arg_idx < args.len() {
                    args[arg_idx]
                } else {
                    panic!("Index out of bounds for function arguments")
                }
            }
            _ => panic!("Cannot project a non-function term"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Term {
    Constant {
        id: Value,
        rendered: Option<Rc<str>>,
    },
    Func {
        id: FunctionId,
        args: Vec<TermId>,
    },
}

/// A hash-cons store for proofs and terms related to an egglog program.
#[derive(Clone, Default)]
pub struct ProofStore {
    pub(crate) eq_store: IdVec<EqProofId, EqProof>,
    pub(crate) term_store: IdVec<TermProofId, TermProof>,
    pub(crate) eq_memo: HashMap<EqProof, EqProofId>,
    pub(crate) term_memo: HashMap<TermProof, TermProofId>,
    pub(crate) termdag: TermDag,
}

impl ProofStore {
    fn print_cong(&self, cong_pf: &CongProof, writer: &mut impl io::Write) -> io::Result<()> {
        let CongProof {
            pf_args_eq,
            pf_f_args_ok,
            old_term,
            new_term,
            func,
        } = cong_pf;
        write!(writer, "Cong({func:?}, ")?;
        self.termdag.print_term(*old_term, writer)?;
        write!(writer, " => ")?;
        self.termdag.print_term(*new_term, writer)?;
        write!(writer, " by (")?;
        for (i, pf) in pf_args_eq.iter().enumerate() {
            if i > 0 {
                write!(writer, ", ")?;
            }
            self.print_eq_proof(*pf, writer)?;
        }
        write!(writer, ") , old term exists by: ")?;
        self.print_term_proof(*pf_f_args_ok, writer)?;
        write!(writer, ")")
    }

    /// Print the equality proof in a human-readable format to the given writer.
    pub fn print_eq_proof(&self, eq_pf: EqProofId, writer: &mut impl io::Write) -> io::Result<()> {
        let eq_pf = self.eq_store.get(eq_pf).unwrap();
        match eq_pf {
            EqProof::PRule {
                rule_name,
                subst,
                body_pfs,
                result_lhs,
                result_rhs,
            } => {
                write!(writer, "PRule[Equality]({rule_name:?}, Subst {{")?;
                for (i, (var, term)) in subst.iter().enumerate() {
                    if i > 0 {
                        write!(writer, ", ")?;
                    }
                    write!(writer, "{var:?} => ")?;
                    self.termdag.print_term(*term, writer)?;
                }
                write!(writer, "}}, Body Pfs: [")?;
                for (i, pf) in body_pfs.iter().enumerate() {
                    if i > 0 {
                        write!(writer, ", ")?;
                    }
                    match pf {
                        Premise::TermOk(term_pf) => {
                            write!(writer, "TermOk(")?;
                            self.print_term_proof(*term_pf, writer)?;
                            write!(writer, ")")?;
                        }
                        Premise::Eq(eq_pf) => {
                            write!(writer, "Eq(")?;
                            self.print_eq_proof(*eq_pf, writer)?;
                            write!(writer, ")")?;
                        }
                    }
                }
                write!(writer, "], Result: ")?;
                self.termdag.print_term(*result_lhs, writer)?;
                write!(writer, " = ")?;
                self.termdag.print_term(*result_rhs, writer)?;
                write!(writer, ")")
            }
            EqProof::PRefl { t_ok_pf, t } => {
                write!(writer, "PRefl(")?;
                self.print_term_proof(*t_ok_pf, writer)?;
                write!(writer, ", (term= ")?;
                self.termdag.print_term(*t, writer)?;
                write!(writer, "))")
            }
            EqProof::PSym { eq_pf } => {
                write!(writer, "PSym(")?;
                self.print_eq_proof(*eq_pf, writer)?;
                write!(writer, ")")
            }
            EqProof::PTrans { pfxy, pfyz } => {
                write!(writer, "PTrans(")?;
                self.print_eq_proof(*pfxy, writer)?;
                write!(writer, ", ")?;
                self.print_eq_proof(*pfyz, writer)?;
                write!(writer, ")")
            }
            EqProof::PCong(cong_pf) => {
                write!(writer, "PCong[Equality](")?;
                self.print_cong(cong_pf, writer)?;
                write!(writer, ")")
            }
        }
    }

    /// Print the term proof in a human-readable format to the given writer.
    pub fn print_term_proof(
        &self,
        term_pf: TermProofId,
        writer: &mut impl io::Write,
    ) -> io::Result<()> {
        let term_pf = self.term_store.get(term_pf).unwrap();
        match term_pf {
            TermProof::PRule {
                rule_name,
                subst,
                body_pfs,
                result,
            } => {
                write!(writer, "PRule[Existence]({rule_name:?}, Subst {{")?;
                for (i, (var, term)) in subst.iter().enumerate() {
                    if i > 0 {
                        write!(writer, ", ")?;
                    }
                    write!(writer, "{var:?} => ")?;
                    self.termdag.print_term(*term, writer)?;
                }
                write!(writer, "}}, Body Pfs: [")?;
                for (i, pf) in body_pfs.iter().enumerate() {
                    if i > 0 {
                        write!(writer, ", ")?;
                    }
                    match pf {
                        Premise::TermOk(term_pf) => {
                            write!(writer, "TermOk(")?;
                            self.print_term_proof(*term_pf, writer)?;
                            write!(writer, ")")?;
                        }
                        Premise::Eq(eq_pf) => {
                            write!(writer, "Eq(")?;
                            self.print_eq_proof(*eq_pf, writer)?;
                            write!(writer, ")")?;
                        }
                    }
                }
                write!(writer, "], Result: ")?;
                self.termdag.print_term(*result, writer)?;
                write!(writer, ")")
            }
            TermProof::PProj {
                pf_f_args_ok,
                arg_idx,
            } => {
                write!(writer, "PProj(")?;
                self.print_term_proof(*pf_f_args_ok, writer)?;
                write!(writer, ", {arg_idx})")
            }
            TermProof::PCong(cong_pf) => {
                write!(writer, "PCong[Exists](")?;
                self.print_cong(cong_pf, writer)?;
                write!(writer, ")")
            }
            TermProof::PFiat { desc, term } => {
                write!(writer, "PFiat({desc:?}")?;
                write!(writer, ", ")?;
                self.termdag.print_term(*term, writer)?;
                write!(writer, ")")
            }
        }
    }
    pub(crate) fn intern_term(&mut self, prf: TermProof) -> TermProofId {
        match self.term_memo.entry(prf) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let id = self.term_store.push(entry.key().clone());
                entry.insert(id);
                id
            }
        }
    }
    pub(crate) fn intern_eq(&mut self, prf: EqProof) -> EqProofId {
        match self.eq_memo.entry(prf) {
            Entry::Occupied(entry) => *entry.get(),
            Entry::Vacant(entry) => {
                let id = self.eq_store.push(entry.key().clone());
                entry.insert(id);
                id
            }
        }
    }

    pub(crate) fn refl(&mut self, proof: TermProofId, term: TermId) -> EqProofId {
        self.intern_eq(EqProof::PRefl {
            t_ok_pf: proof,
            t: term,
        })
    }

    pub(crate) fn sym(&mut self, proof: EqProofId) -> EqProofId {
        self.intern_eq(EqProof::PSym { eq_pf: proof })
    }

    pub(crate) fn trans(&mut self, pfxy: EqProofId, pfyz: EqProofId) -> EqProofId {
        self.intern_eq(EqProof::PTrans { pfxy, pfyz })
    }

    pub(crate) fn sequence_proofs(&mut self, pfs: &[EqProofId]) -> EqProofId {
        match pfs {
            [] => panic!("Cannot sequence an empty list of proofs"),
            [pf] => *pf,
            [pf1, rest @ ..] => {
                let mut cur = *pf1;
                for pf in rest {
                    cur = self.trans(cur, *pf);
                }
                cur
            }
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum Premise {
    TermOk(TermProofId),
    Eq(EqProofId),
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct CongProof {
    pub pf_args_eq: Vec<EqProofId>,
    pub pf_f_args_ok: TermProofId,
    pub old_term: TermId,
    pub new_term: TermId,
    pub func: FunctionId,
}

#[allow(clippy::enum_variant_names)]
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum TermProof {
    /// proves a Proposition based on a rule application
    /// the subsitution gives the mapping from variables to terms
    /// the body_pfs gives proofs for each of the conditions in the query of the rule
    /// the act_pf gives a location in the action of the proposition
    PRule {
        rule_name: Rc<str>,
        subst: DenseIdMap<Variable, TermId>,
        body_pfs: Vec<Premise>,
        result: TermId,
    },
    /// get a proof for the child of a term given a proof of a term
    PProj {
        pf_f_args_ok: TermProofId,
        arg_idx: usize,
    },
    PCong(CongProof),
    PFiat {
        desc: Rc<str>,
        term: TermId,
    },
}

#[allow(clippy::enum_variant_names)]
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum EqProof {
    /// proves a Proposition based on a rule application
    /// the subsitution gives the mapping from variables to terms
    /// the body_pfs gives proofs for each of the conditions in the query of the rule
    /// the act_pf gives a location in the action of the proposition
    PRule {
        rule_name: Rc<str>,
        subst: DenseIdMap<Variable, TermId>,
        body_pfs: Vec<Premise>,
        result_lhs: TermId,
        result_rhs: TermId,
    },
    /// A term is equal to itself- proves the proposition t = t
    PRefl {
        t_ok_pf: TermProofId,
        t: TermId,
    },
    /// The symmetric equality of eq_pf
    PSym {
        eq_pf: EqProofId,
    },
    PTrans {
        pfxy: EqProofId,
        pfyz: EqProofId,
    },
    /// Proves f(x1, y1, ...) = f(x2, y2, ...) where f is fun_sym
    /// A proof via congruence- one proof for each child of the term
    /// pf_f_args_ok is a proof that the term with the lhs children is valid
    ///
    PCong(CongProof),
}

#[allow(clippy::enum_variant_names)]
#[derive(Clone, PartialEq, Eq, Hash)]
pub enum ProofTerm {}
