//! HPS adapter for exact XOR row-space inference over shared Boolean factors.
//! Product columns retain their original meaning. A derived singleton pivot is
//! substitutable only if it is an owned path absent from the entire remainder.

use super::simplify::substitute_component;
use crate::symbolic::{BooleanPolynomial, Component, Variable};
use crate::utils::constraint_rows::{self, Error, Limits};
use std::collections::BTreeSet;

const MAX_MATRIX_CELLS: usize = 1_000_000;

/// Ok(true): one binder eliminated; Ok(false): refused/no usable relation.
/// Err(()): exact contradiction. Budget refusals and contradictions do not
/// mutate. An empty exact row space also removes tautological guards.
/// This preserves full amplitudes, not just density, and needs no history or
/// single-component precondition. No factor 2 or sqrt(2) accompanies a unique
/// assignment; all residual guards are retained and substituted.
pub(super) fn eliminate_guard_path(component: &mut Component) -> Result<bool, ()> {
    let summands = component
        .guard
        .iter()
        .map(BooleanPolynomial::xor_terms)
        .collect::<Vec<_>>();
    let rows: Vec<_> = summands
        .iter()
        .map(|r| r.iter().collect::<Vec<_>>())
        .collect();
    let reduced = match constraint_rows::reduce(
        &rows,
        &BooleanPolynomial::one(),
        Limits {
            rows: usize::MAX,
            terms: usize::MAX,
            cells: MAX_MATRIX_CELLS,
        },
        |a, b| {
            // Eliminate formal products first, exposing affine combinations such
            // as v+w from v+av+aw+bc and w+av+aw+bc. This is only a column
            // permutation; neither products nor free inputs become new paths.
            let rank = |m: &BooleanPolynomial| {
                if singleton(m).is_none() {
                    0
                } else if matches!(singleton(m), Some(Variable::Path(_))) {
                    1
                } else {
                    2
                }
            };
            rank(a)
                .cmp(&rank(b))
                .then_with(|| if rank(a) == 1 { b.cmp(a) } else { a.cmp(b) })
        },
    ) {
        Ok(rows) => rows,
        Err(Error::Contradiction) => return Err(()),
        Err(Error::BudgetExceeded) => return Ok(false),
    };
    if reduced.is_empty() {
        component.guard.clear();
        return Ok(false);
    }
    for row in reduced {
        let coupled: BTreeSet<_> = row
            .iter()
            .filter(|m| singleton(m).is_none())
            .flat_map(BooleanPolynomial::variables)
            .collect();
        let mut pivots: Vec<_> = row
            .iter()
            .filter_map(|m| {
                let v = singleton(m)?;
                (matches!(&v, Variable::Path(p) if component.path_support.contains(p))
                    && !coupled.contains(&v))
                .then(|| v.clone())
            })
            .collect();
        pivots.sort_by(|a, b| b.cmp(a));
        if let Some(variable) = pivots.into_iter().next() {
            let pivot = BooleanPolynomial::variable(variable.clone());
            let replacement = row
                .iter()
                .filter(|term| **term != pivot)
                .fold(BooleanPolynomial::zero(), |sum, term| sum.xor(term));
            let mut candidate = component.clone();
            substitute_component(&mut candidate, &variable, &replacement);
            *component = candidate;
            return Ok(true);
        }
    }
    Ok(false)
}

fn singleton(p: &BooleanPolynomial) -> Option<Variable> {
    p.as_variable().cloned()
}

#[cfg(test)]
mod tests;
