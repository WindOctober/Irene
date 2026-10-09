//! Exact Shannon cofactors of a bound Boolean sum.
//!
//! Both complete contributions must be added coherently: sum_y F(y) = F(0) + F(1).
//! No averaging, squaring, or existential interpretation is introduced here.
use crate::equivalence::density::aggregate::{
    KernelBooleanPolynomial, KernelVariable, Reduction, WorkingTerm, graph, reduce_working_term,
};

/// Charges one split from the shared recursive budget before visiting children.
pub(in crate::equivalence::density::aggregate) fn claim_split(
    splits: &mut usize,
    depth: usize,
    depth_limit: usize,
) -> Option<()> {
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
pub(in crate::equivalence::density::aggregate) fn visit_bound_cofactors(
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

// Prefer the last bound coordinate; this is scheduling, not a semantic premise.
fn children(t: &WorkingTerm, v: &KernelVariable) -> Option<[Reduction; 2]> {
    let mut result = Vec::new();
    visit_bound_cofactors(
        t,
        v,
        |rhs| !graph::is_algebraic(t) || t.substitution_within_budget(v, rhs),
        |child| {
            result.push(reduce_working_term(child));
            Some(())
        },
    )?;
    result.try_into().ok()
}

pub(in crate::equivalence::density::aggregate) fn split(t: &WorkingTerm) -> Option<[Reduction; 2]> {
    let variable = t.paths.last()?.clone();
    children(t, &variable)
}
