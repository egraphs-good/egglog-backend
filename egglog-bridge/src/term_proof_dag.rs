use core_relations::{BaseValueId, Value};
use thiserror::Error;

use std::{
    fmt,
    io::{self, Write},
    rc::Rc,
    sync::Arc,
};

use hashbrown::{hash_map::Entry, HashMap};

use crate::{new_syntax::RuleData2, rule::Variable, syntax::TermFragment, FunctionId, Result};

#[derive(Debug)]
pub enum TermValue<Prf> {
    Base(BaseValueConstant),
    SubTerm(Rc<Prf>),
}

impl<Prf> Clone for TermValue<Prf> {
    fn clone(&self) -> Self {
        match self {
            TermValue::Base(p) => TermValue::Base(p.clone()),
            TermValue::SubTerm(p) => TermValue::SubTerm(p.clone()),
        }
    }
}

#[derive(Debug)]
pub struct EqProof {
    pub lhs: Rc<TermProof>,
    pub rhs: Rc<TermProof>,
    pub reason: EqReason,
}

#[derive(Debug)]
pub enum EqReason {
    /// The (trivial) proof that a row equals itself.
    Id(Rc<TermProof>),
    /// An explanation of the existence of a row in the union-find.
    Base(Rc<TermProof>),
    /// A proof that `x = y` by way of `y = x`.
    Backwards(Rc<EqProof>),
    /// A proof that `x = z` by way of `x = y`, `y = z` (for any number of
    /// intermediate `y`s).
    Trans(Vec<Rc<EqProof>>),
}

pub enum TermProof {
    /// A proof that a term `r'` exists because:
    /// * Another term `r` exists, and
    /// * Each argument in `r` is equal to `r'`.
    Cong {
        func_id: FunctionId,
        func: Arc<str>,
        old_term: Rc<TermProof>,
        pairwise_eq: Vec<TermValue<EqProof>>,
    },
    /// The base case of a proof. Terms that were added as base values to the
    /// database.
    Fiat {
        desc: Arc<str>,
        func: Arc<str>,
        func_id: FunctionId,
        row: Vec<TermValue<TermProof>>,
    },

    /// A proof of the existence of a term by applying a rule to the databse.
    FromRule {
        rule_data: RuleData2,
        /// There's one [`TermValue`] for every [`TopLevelLhsExpr`] in the syntax stored in
        /// `rule_data`.
        ///
        /// [`TopLevelLhsExpr`]: crate::new_syntax::TopLevelLhsExpr
        premises: Vec<TermValue<TermProof>>,
        final_term: Rc<Term>,
    },
}

impl fmt::Debug for TermProof {
    /// We have a custom impl of fmt::Debug for TermProof as the default
    /// implementaiton can easily cause exponential blowup by printing out the
    /// tree for a DAG proof with lots of redundancy.
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TermProof::Cong { func, .. } => write!(f, "(cong {func} ...)"),
            TermProof::Fiat { desc, func, .. } => write!(f, "(fiat {desc} ({func} ... ))"),
            TermProof::FromRule { rule_data, .. } => {
                write!(f, "(from rule {rule_data:?} ...)")
            }
        }
    }
}

impl TermProof {
    pub fn dump_explanation(&self, writer: &mut impl Write) -> io::Result<()> {
        let mut printer = Printer::default();
        printer.print_term(self, "", writer)
    }
}

#[derive(Default)]
struct Printer {
    ids: HashMap<usize, usize>,
}

impl Printer {
    /// Get the id associated with the given pointer, creating a new one if one
    /// does not exist.
    ///
    /// The second value in the tuple is `true` if a new id was created.
    fn get_id<T>(&mut self, node: &T) -> (usize, bool) {
        let len = self.ids.len();
        match self.ids.entry(node as *const T as *const () as usize) {
            Entry::Occupied(o) => (*o.get(), false),
            Entry::Vacant(v) => (*v.insert(len), true),
        }
    }

    fn get_term_id(&mut self, term: &TermProof, writer: &mut impl Write) -> io::Result<String> {
        let (id, is_new) = self.get_id(term);
        if is_new {
            self.print_term(term, &format!("let t{id} = "), writer)?;
        }
        Ok(format!("t{id}"))
    }

    fn get_eq_id(&mut self, eq: &EqProof, writer: &mut impl Write) -> io::Result<String> {
        let (id, is_new) = self.get_id(eq);
        if is_new {
            self.print_eq(eq, &format!("let e{id} = "), writer)?;
        }
        Ok(format!("e{id}"))
    }

    fn print_term(
        &mut self,
        term: &TermProof,
        prefix: &str,
        writer: &mut impl Write,
    ) -> io::Result<()> {
        match term {
            TermProof::Cong {
                func,
                old_term,
                pairwise_eq,
                ..
            } => {
                let old_term = self.get_term_id(old_term.as_ref(), writer)?;
                let eq_subproofs = DisplayList(
                    try_collect(pairwise_eq.iter().map(|t| match t {
                        TermValue::Base(s) => Ok(format!("{s}")),
                        TermValue::SubTerm(subterm) => self.get_eq_id(subterm.as_ref(), writer),
                    }))?,
                    " ",
                );
                writeln!(
                    writer,
                    "{prefix}Cong {{ {old_term} => [{func} {eq_subproofs}] }}"
                )?;
            }
            TermProof::Fiat {
                desc, func, row, ..
            } => {
                let term = DisplayList(
                    try_collect(row.iter().map(|t| match t {
                        TermValue::Base(s) => Ok(format!("{s}")),
                        TermValue::SubTerm(subterm) => self.get_term_id(subterm.as_ref(), writer),
                    }))?,
                    " ",
                );
                writeln!(writer, "{prefix}Fiat {{ {desc}, ({func} {term}) }}")?;
            }
            TermProof::FromRule {
                rule_data,
                premises,
                final_term,
            } => {
                todo!()
            }
        }
        Ok(())
    }

    fn print_eq(
        &mut self,
        EqProof { lhs, rhs, reason }: &EqProof,
        prefix: &str,
        writer: &mut impl Write,
    ) -> io::Result<()> {
        match reason {
            EqReason::Id(row) => {
                let id = self.get_term_id(row.as_ref(), writer)?;
                writeln!(writer, "{prefix}Id {{ {id} }}")?;
            }
            EqReason::Base(b) => {
                let lhs = self.get_term_id(lhs, writer)?;
                let rhs = self.get_term_id(rhs, writer)?;
                let id = self.get_term_id(b.as_ref(), writer)?;
                writeln!(writer, "{prefix}Union-from-rule {{ {id} }} ({lhs} = {rhs})")?;
            }
            EqReason::Backwards(b) => {
                let lhs = self.get_term_id(lhs, writer)?;
                let rhs = self.get_term_id(rhs, writer)?;
                let id = self.get_eq_id(b.as_ref(), writer)?;
                writeln!(writer, "{prefix}Backwards {{ {id} }} ({lhs} = {rhs})")?;
            }
            EqReason::Trans(eqs) => {
                let lhs = self.get_term_id(lhs, writer)?;
                let rhs = self.get_term_id(rhs, writer)?;
                let eqs = DisplayList(
                    try_collect(eqs.iter().map(|e| self.get_eq_id(e.as_ref(), writer)))?,
                    " -> ",
                );
                writeln!(writer, "{prefix}Transitivity {{ {eqs} }} ({lhs} = {rhs})")?;
            }
        }
        Ok(())
    }
}

fn try_collect<T, E, I>(iter: I) -> std::result::Result<Vec<T>, E>
where
    I: Iterator<Item = std::result::Result<T, E>>,
{
    iter.collect()
}

/// A basic helper for display-formatting lists of items.
pub(crate) struct DisplayList<T>(pub Vec<T>, pub &'static str);

impl<T: std::fmt::Display> std::fmt::Display for DisplayList<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut iter = self.0.iter();
        if let Some(first) = iter.next() {
            write!(f, "{first}")?;
            for item in iter {
                write!(f, "{}{item}", self.1)?;
            }
        }
        Ok(())
    }
}

struct ByPtr<T>(Rc<T>);

impl std::cmp::PartialEq for ByPtr<TermProof> {
    fn eq(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.0, &other.0)
    }
}

impl std::cmp::Eq for ByPtr<TermProof> {}

impl std::hash::Hash for ByPtr<TermProof> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        Rc::as_ptr(&self.0).hash(state)
    }
}

#[derive(Default)]
pub(crate) struct TermEnv {
    terms: HashMap<ByPtr<TermProof>, Rc<Term>>,
    check_cache: HashMap<usize, CacheState>,
}

enum CacheState {
    Marked,
    Checked,
}

impl TermEnv {
    /// Get the underlying term for a given proof.
    pub fn get_term(&mut self, term: Rc<TermProof>) -> Rc<Term> {
        let by_ptr = ByPtr(term);
        if let Some(term) = self.terms.get(&by_ptr) {
            return term.clone();
        }
        let res = match by_ptr.0.as_ref() {
            TermProof::Cong {
                func,
                pairwise_eq,
                func_id,
                ..
            } => {
                let new_subterms = Vec::from_iter(pairwise_eq.iter().map(|t| match t {
                    TermValue::Base(p) => Rc::new(Term::Base(p.clone())),
                    TermValue::SubTerm(eq) => self.get_term(eq.rhs.clone()),
                }));
                Rc::new(Term::Expr {
                    func_id: *func_id,
                    func: func.clone(),
                    subterms: new_subterms,
                })
            }
            TermProof::Fiat {
                func_id, func, row, ..
            } => Rc::new(Term::Expr {
                func_id: *func_id,
                func: func.clone(),
                subterms: row
                    .iter()
                    .map(|t| match t {
                        TermValue::Base(p) => Rc::new(Term::Base(p.clone())),
                        TermValue::SubTerm(rc) => self.get_term(rc.clone()),
                    })
                    .collect(),
            }),
            TermProof::FromRule { final_term, .. } => final_term.clone(),
        };
        self.terms.insert(by_ptr, res.clone());
        res
    }

    fn get_term_from_val(&mut self, tv: &TermValue<TermProof>) -> Rc<Term> {
        match tv {
            TermValue::Base(p) => Rc::new(Term::Base(p.clone())),
            TermValue::SubTerm(rc) => self.get_term(rc.clone()),
        }
    }

    fn start_check<T>(&mut self, elt: &T) -> Result<bool> {
        let num = elt as *const T as *const () as usize;
        match self.check_cache.entry(num) {
            Entry::Occupied(o) => {
                if let CacheState::Marked = o.get() {
                    return Err(ProofCheckError::CyclicDependency.into());
                }
                Ok(true)
            }
            Entry::Vacant(v) => {
                v.insert(CacheState::Marked);
                Ok(false)
            }
        }
    }

    fn finish_check<T>(&mut self, elt: &T) {
        let num = elt as *const T as *const () as usize;
        self.check_cache.insert(num, CacheState::Checked);
    }
}

/// A base value constant in a term.
#[derive(Clone, Eq, PartialEq, Debug, PartialOrd, Ord)]
pub struct BaseValueConstant {
    /// The type of the base value.
    pub(crate) ty: BaseValueId,
    /// The underlying (interned) value of the base value, to be looked up in the
    /// `BaseValues` associated with an egraph.
    pub(crate) interned: Value,
    /// The string representation of the base value.
    pub(crate) rendered: Arc<str>,
}

impl fmt::Display for BaseValueConstant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.rendered)
    }
}

/// A pointer-based representation of a term.
///
/// This is mostly used in printing routines. It is a less efficient
/// representation than something like Egg's RecExpr.
#[derive(Debug, PartialEq, Eq)]
// NB: my read of the standard library is that `Rc::eq` uses `ptr_eq` to
// short-circuit. When there is a lot of sharing between two terms, checking
// equality should be pretty quick.
pub enum Term {
    Base(BaseValueConstant),
    Expr {
        func_id: FunctionId,
        func: Arc<str>,
        subterms: Vec<Rc<Term>>,
    },
}

impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Term::Base(c) => write!(f, "{c}"),
            Term::Expr { func, subterms, .. } => {
                write!(f, "({func}")?;
                for subterm in subterms {
                    write!(f, " {subterm}")?;
                }
                write!(f, ")")
            }
        }
    }
}

// NB: why strings?
// `Error` needs to be Send, but Rc (which we use for deduping) is not. So we
// format the terms before returning an error.

#[derive(Debug, Error)]
pub(crate) enum ProofCheckError {
    #[error("Ran into a cyclic dependency while checking proof")]
    CyclicDependency,
    #[error("Mismatched endpoints in backward equality proof {x} != {y}")]
    BackwardEndpointMismatch { x: String, y: String },
    #[error("Mismatched endpoints in transitive equality proof: {x} != {y}")]
    TransitiveEndpointMismatch { x: String, y: String },
    #[error("Expected endpoints for an id proof don't match the term proof={proof}, lhs={lhs}, rhs={rhs}")]
    IdProofTermDisagreement {
        proof: String,
        lhs: String,
        rhs: String,
    },

    #[error("Failed to build a consistent substitution {var:?} used in both {t1} and {t2}")]
    UnificationFailure {
        var: Variable,
        t1: String,
        t2: String,
    },

    #[error("Found mismatched constants {p1} and {p2}")]
    MismatchedConstants { p1: String, p2: String },

    #[error("Found mismatched syntax variants {pat} vs. {term}")]
    PatternVariantMismatch { pat: String, term: String },

    #[error("Found mismatch between functions {func1} vs. {func2}")]
    PatternFunctionMismatch { func1: String, func2: String },

    #[error("Unbound variable {var:?}")]
    UnboundVariable { var: Variable },

    #[error("Expected terms {lhs} and {rhs} to be equal")]
    AssertEqFailure { lhs: String, rhs: String },

    #[error("Non-base-value argument to primitive function {arg}")]
    NonBaseValueArg { arg: String },

    #[error("Failed to construct term {term}")]
    TermNotConstructed { term: String },

    #[error("Failed to prove equality {lhs} = {rhs}")]
    TermsNotUnioned { lhs: String, rhs: String },

    #[error("Proof of equality from a rule unioning {lhs_actual} and {rhs_actual} intended to prove {lhs_expected} = {rhs_expected}")]
    MisalignedUnion {
        lhs_expected: String,
        lhs_actual: String,
        rhs_expected: String,
        rhs_actual: String,
    },

    #[error(
        "Rule {rule} is being used as a proof of equality when `union` is not the  target function"
    )]
    NonUnionProofOfEquality { rule: String },
}

// Cleanups:
// * use named variants of FunctionId and Variable

// These custom impls here are to provide fairly fast map lookups on terms
// without implementing a full hashcons for them. This is a bit of a hack /
// half-measure: but this part of proof checking probably isn't going to be the
// most performance-sensitive either. Worth revisiting if we notice an issue.

impl PartialOrd for Term {
    fn le(&self, other: &Self) -> bool {
        if self == other {
            return true;
        }
        match (self, other) {
            (Term::Base(p1), Term::Base(p2)) => p1 <= p2,
            (
                Term::Expr {
                    func_id: f1,
                    subterms: s1,
                    ..
                },
                Term::Expr {
                    func_id: f2,
                    subterms: s2,
                    ..
                },
            ) => (f1, s1) <= (f2, s2),
            (Term::Base(_), Term::Expr { .. }) => true,
            (Term::Expr { .. }, Term::Base(_)) => false,
        }
    }

    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Term {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if self == other {
            return std::cmp::Ordering::Equal;
        }
        match (self, other) {
            (Term::Base(p1), Term::Base(p2)) => p1.cmp(p2),
            (
                Term::Expr {
                    func_id: f1,
                    subterms: s1,
                    ..
                },
                Term::Expr {
                    func_id: f2,
                    subterms: s2,
                    ..
                },
            ) => (f1, s1).cmp(&(f2, s2)),
            (Term::Base(_), Term::Expr { .. }) => std::cmp::Ordering::Less,
            (Term::Expr { .. }, Term::Base(_)) => std::cmp::Ordering::Greater,
        }
    }
}
