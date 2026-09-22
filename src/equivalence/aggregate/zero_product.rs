//! Sufficient exact-zero proof for a product of complete path-free factors.
//! Factors are never divided out or distributed. Every free Boolean cofactor
//! must contain a certified zero factor, possibly a different one per branch.
//! False includes unsupported syntax and budget refusal; it never proves NEQ.
//! Inputs must be well-defined expressions from the validated kernel pipeline.
use std::collections::BTreeMap;

use super::KernelVariable;
use super::collection::ExactAggregate;
use super::free_split::{remove_common_phase, restrict_aggregate};
use super::phase_unit::charge_cells;
use super::scalar::scalar_conditions_within_budget;
use super::witness;

/// After a COMPLETE factor bijection, equality reduces to
/// (C_left-C_right) * product(F_i) = 0. Never cancel/divide by an F_i:
/// it may vanish exactly where the common coefficients disagree.
pub(super) fn prove(
    factors: Vec<ExactAggregate>,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
    cells: &mut usize,
    depth: usize,
    depth_limit: usize,
) -> bool {
    let mut normalized = Vec::new();
    for factor in factors {
        if charge_cells(&factor, cells).is_none() {
            return false;
        }
        let Some(factor) = remove_common_phase(factor) else {
            return false;
        };
        if factor.is_empty() || witness::constant_is_zero(&factor, algebra) {
            return true;
        }
        normalized.push(factor);
    }
    if depth >= depth_limit || *free == 0 {
        return false;
    }
    // The first factor is the coefficient difference. Start with its
    // support so irrelevant coordinates in other factors do not dominate.
    let mut selected = None;
    for factor in &normalized {
        let mut variables = BTreeMap::<KernelVariable, usize>::new();
        for (entry, coefficients) in factor {
            for row in &entry.constraints {
                for variable in row.variables() {
                    *variables.entry(variable).or_default() += 1;
                }
            }
            for (phase, scalar) in coefficients {
                for (monomial, _) in phase.terms() {
                    for variable in monomial.variables() {
                        *variables.entry(variable.clone()).or_default() += 1;
                    }
                }
                if !scalar_conditions_within_budget(scalar, |row| {
                    for variable in row.variables() {
                        *variables.entry(variable).or_default() += 1;
                    }
                    true
                }) {
                    return false;
                }
            }
        }
        // Repeated coordinates often gate the whole coefficient difference.
        // Choose the most frequent one, preserving the old least-variable
        // tie order. This is scheduling only: BOTH whole-product cofactors
        // must still vanish, and no possibly zero factor is canceled.
        if let Some((variable, _)) = variables
            .into_iter()
            .min_by_key(|(variable, count)| (std::cmp::Reverse(*count), variable.clone()))
        {
            selected = Some(variable);
            break;
        }
    }
    let Some(variable) = selected else {
        return false;
    };
    if variable.is_bound_path() {
        return false;
    }
    *free -= 1;
    for value in [false, true] {
        let Some(children) = normalized
            .iter()
            .map(|factor| restrict_aggregate(factor, &variable, value))
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        if !prove(children, free, algebra, cells, depth + 1, depth_limit) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests;
