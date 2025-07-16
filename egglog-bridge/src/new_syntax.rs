//! A new replacement for the `syntax` module. We eventually want to replace `syntax.rs` with this
//! module.

use crate::Result;
use core_relations::{ExternalFunctionId, Value};
use numeric_id::{define_id, IdVec};

use crate::{
    proof_spec::ProofBuilder,
    rule::{AtomId, Bindings, Variable},
    ColumnTy, FunctionId, RuleBuilder, RuleId,
};

define_id!(pub(crate) SyntaxId, u32, "an offset into a Syntax DAG.");

/// Representative source syntax for _one line_ of an egglog query, namely, the left-hand-side of
/// an egglog rule.
pub enum SourceExpr {
    /// A constant.
    Const { ty: ColumnTy, val: Value },
    /// A single variable.
    Var { id: Variable, name: String },
    /// An assertion that some syntax is equal to some other syntax.
    Eq { lhs: SyntaxId, rhs: SyntaxId },
    /// A call to an external (aka primitive) function.
    ExternalCall {
        func: ExternalFunctionId,
        args: Vec<SyntaxId>,
    },
    /// A query of an egglog-level function (i.e. a table).
    FunctionCall {
        /// The egglog function being bound.
        func: FunctionId,
        /// The atom in the _destination_ query (i.e. at the egglog-bridge level) to which this
        /// call corresponds.
        atom: AtomId,
        /// Arguments to the function.
        args: Vec<SyntaxId>,
    },
}

/// A data-structure representing an egglog query. Essentially, multiple [`SourceExpr`]s, one per
/// line, along with a backing store accounting for subterms indexed by [`SyntaxId].
pub struct SourceSyntax {
    backing: IdVec<SyntaxId, SourceExpr>,
    roots: Vec<SyntaxId>,
}

type TodoRenameRuleData2ToRuleData = ();

/// The data associated with a proof of a given term whose premises are given by a
/// [`SourceSyntax`].
pub(crate) struct RuleData2 {
    rule: RuleId,
    syntax: SourceSyntax,
    // That's it?
}

impl RuleData2 {
    fn arity(&self) -> usize {
        1 + self.syntax.roots.len()
    }
}

impl ProofBuilder {
    pub(crate) fn create_reason(
        &mut self,
        syntax: &SourceSyntax,
    ) -> impl Fn(&mut Bindings, &mut RuleBuilder) -> Result<core_relations::Variable> {
        |bngs, rb| todo!()
    }
}

// Concrete next steps:
// [ ] fill in create_reason (this will be the hard bit, building a term, inserting a reason).
// * Process for each `FunctionCall`
//   - We'll have a term that's like "look up term or else call this external function which will
//   insert a reason and also a term"
// [ ] - That external function needs its own instruction (LookupOrCallFallbackExternal)
// [ ] - That external function just needs to take the old term id, the new term, + insert a cong.
//       It can be one global external func.
// =====
// Now how do we put this all together?
//
//
// Still rewrite a set => lookup+union
// [ ] Set and Lookup and Union all need to take a &SourceSyntax arg when proofs are enabled.
// [ ] With that arg, they create_reason unconditionally and then lookup_or_insert accordinly. This
// is wasteful. We could do some sort of recursive fallback thing maybe but it's complicated.
// (doable with more sophisticated branching in the IR but kinda tricky right now).
// [ ] That should get us back to parity and we can send a PR + delete some old proofs code.
//
// =====
// What happens after parity?
//
// [ ] figure out what to do about non-constructor functions
// [ ]     "log of operations" semantics, somehow. Each row is a proof that (f ...) "may equal" t
// [ ] containers (conceptually easier)
