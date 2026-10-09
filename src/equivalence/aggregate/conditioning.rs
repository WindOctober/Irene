//! Coherent Shannon scheduling, not min-fill variable elimination.
//!
//! Prefer later bound path coordinates: on the retained regression suite this
//! exposes useful exact cofactors earlier than input-order splitting. This is
//! a heuristic, not an invariant about circuit semantics or a case-name rule.
//! Both COMPLETE cofactors are always summed; free coordinates are never split.
use super::*;

fn children(t: &WorkingTerm, v: &KernelVariable) -> Option<[Reduction; 2]> {
    let mut result = Vec::new();
    shannon::visit_bound_cofactors(
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

pub(super) fn split(t: &WorkingTerm) -> Option<[Reduction; 2]> {
    let variable = t.paths.last()?.clone();
    children(t, &variable)
}

#[cfg(test)]
#[path = "../../../tests/unit/equivalence/aggregate/conditioning/tests.rs"]
mod tests;
