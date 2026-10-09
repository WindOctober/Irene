//! Exact Shannon cofactors of a bound Boolean sum.
//!
//! Both complete contributions must be added coherently: sum_y F(y) = F(0) + F(1).
//! No averaging, squaring, or existential interpretation is introduced here.
use super::{KernelBooleanPolynomial, KernelVariable, WorkingTerm};

/// Charges one split from the shared recursive budget before visiting children.
pub(super) fn claim_split(splits: &mut usize, depth: usize, depth_limit: usize) -> Option<()> {
    if depth >= depth_limit || *splits == 0 {
        return None;
    }
    *splits -= 1;
    Some(())
}

/// Visits the complete zero and one cofactors in order, retaining all free indices.
/// The caller supplies representation admission and subsequent reduction/collection.
/// Success requires BOTH visits to succeed. On refusal, the caller must discard
/// any partial collected result; consume may already have processed the zero branch.
pub(super) fn visit_bound_cofactors(
    term: &WorkingTerm,
    variable: &KernelVariable,
    mut admit: impl FnMut(&KernelBooleanPolynomial) -> bool,
    mut consume: impl FnMut(WorkingTerm) -> Option<()>,
) -> Option<()> {
    if !variable.is_bound_path() || !term.paths.contains(variable) {
        return None;
    }
    for value in [false, true] {
        let replacement = KernelBooleanPolynomial::from(value);
        if !admit(&replacement) {
            return None;
        }
        let mut child = term.clone();
        child.substitute(variable, &replacement);
        child.paths.remove(variable);
        consume(child)?;
    }
    Some(())
}

#[cfg(test)]
#[path = "../../../tests/unit/equivalence/aggregate/shannon/tests.rs"]
mod tests;
