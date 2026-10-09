//! EQ-only case analysis of a complete, path-free kernel difference.
//! Every free cofactor must vanish separately; they are never added together.
//! The supplied constant checker must prove exact zero. False is inconclusive,
//! including when a budget is exhausted or a sufficient simplification fails.
use num_bigint::BigInt;
use std::collections::{BTreeMap, BTreeSet};

use super::collection::{ExactAggregate, ExactTerm, accumulate_exact_term};
use super::scalar::{normalize_scalar, scalar_conditions_within_budget};
use super::{KernelBooleanPolynomial, KernelVariable, MAX_AFFINE_MATRIX_CELLS};

pub(super) fn prove_zero(
    difference: ExactAggregate,
    budget: &mut usize,
    depth: usize,
    depth_limit: usize,
    constant_is_zero: &mut impl FnMut(&ExactAggregate) -> bool,
) -> bool {
    // D = [G] F implies D=0 whenever F=0. Removing a selector common to
    // every term is a sufficient proof obligation, never an inequality rule.
    // In particular, variables used only by G need no free case split.
    let Some(difference) = forget_common_selector(difference) else {
        return false;
    };
    let Some(difference) = remove_common_phase(difference) else {
        return false;
    };
    if difference.is_empty() {
        return true;
    }
    if depth >= depth_limit || *budget == 0 {
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!("aggregate free-split refusal: depth={depth} budget={budget}");
            let phases = difference
                .values()
                .flat_map(BTreeMap::keys)
                .collect::<Vec<_>>();
            let variables = phases
                .iter()
                .flat_map(|phase| phase.variables())
                .collect::<BTreeSet<_>>();
            eprintln!(
                "aggregate refused phase support: atoms={} variables={variables:?}",
                phases.len()
            );
        }
        return false;
    }
    let mut variables = BTreeSet::new();
    for (entry, coefficients) in &difference {
        for equation in &entry.constraints {
            variables.extend(equation.variables());
        }
        for (phase, coefficient) in coefficients {
            variables.extend(phase.variables());
            if !scalar_conditions_within_budget(coefficient, |condition| {
                variables.extend(condition.variables());
                true
            }) {
                return false;
            }
        }
    }
    let Some(variable) = variables.into_iter().next() else {
        // A nonzero formal coefficient can still cancel exactly in the
        // supported cyclotomic field. Failure of this check is inconclusive.
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "aggregate constant residual: entries={} atoms={}",
                difference.len(),
                difference.values().map(BTreeMap::len).sum::<usize>()
            );
        }
        return constant_is_zero(&difference);
    };
    if variable.is_bound_path() {
        return false;
    }
    *budget -= 1;
    for value in [false, true] {
        let Some(child) = restrict_aggregate(&difference, &variable, value) else {
            return false;
        };
        if !prove_zero(child, budget, depth + 1, depth_limit, constant_is_zero) {
            return false;
        }
    }
    true
}

pub(super) fn forget_common_selector(source: ExactAggregate) -> Option<ExactAggregate> {
    let Some(first) = source.keys().next() else {
        return Some(source);
    };
    if first.constraints.len().saturating_mul(source.len()) > MAX_AFFINE_MATRIX_CELLS {
        return Some(source);
    }
    let common = first
        .constraints
        .iter()
        .filter(|row| {
            source
                .keys()
                .all(|entry| entry.constraints.binary_search(row).is_ok())
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    if common.is_empty() {
        return Some(source);
    }
    let mut result = ExactAggregate::new();
    let mut atoms = 0;
    for (entry, coefficients) in source {
        let constraints = entry
            .constraints
            .into_iter()
            .filter(|row| !common.contains(row))
            .collect::<Vec<_>>();
        for (phase, coefficient) in coefficients {
            accumulate_exact_term(
                ExactTerm {
                    constraints: constraints.clone(),
                    coefficient,
                    phase,
                },
                &mut result,
                &mut atoms,
            )?;
        }
    }
    result.retain(|_, coefficients| !coefficients.is_empty());
    Some(result)
}

/// D = exp(2*pi*i*P) F is zero whenever F is zero, including when P
/// depends on free coordinates. Remove only monomials with the same exact
/// coefficient in every atom. This cannot expand a phase polynomial and
/// avoids splitting coordinates used solely by the common phase factor.
pub(super) fn remove_common_phase(source: ExactAggregate) -> Option<ExactAggregate> {
    let Some(first) = source.values().flat_map(BTreeMap::keys).next() else {
        return Some(source);
    };
    let atom_count: usize = source.values().map(BTreeMap::len).sum();
    if first.term_count().saturating_mul(atom_count) > MAX_AFFINE_MATRIX_CELLS {
        return Some(source);
    }
    let common = first
        .terms()
        .filter(|(monomial, coefficient)| {
            source
                .values()
                .flat_map(BTreeMap::keys)
                .all(|phase| phase.coefficient(monomial) == **coefficient)
        })
        .map(|(monomial, coefficient)| (monomial.clone(), coefficient.scaled(BigInt::from(-1))))
        .collect::<Vec<_>>();
    if common.is_empty() {
        return Some(source);
    }
    let mut result = ExactAggregate::new();
    let mut atoms = 0;
    for (entry, coefficients) in source {
        for (mut phase, coefficient) in coefficients {
            for (monomial, negative) in &common {
                phase.add_boolean(
                    &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                    negative.clone(),
                );
            }
            accumulate_exact_term(
                ExactTerm {
                    constraints: entry.constraints.clone(),
                    coefficient,
                    phase,
                },
                &mut result,
                &mut atoms,
            )?;
        }
    }
    result.retain(|_, coefficients| !coefficients.is_empty());
    Some(result)
}

pub(super) fn restrict_aggregate(
    source: &ExactAggregate,
    variable: &KernelVariable,
    value: bool,
) -> Option<ExactAggregate> {
    let replacement = KernelBooleanPolynomial::from(value);
    let mut result = ExactAggregate::new();
    let mut atoms = 0;
    for (entry, coefficients) in source {
        let mut constraints = entry
            .constraints
            .iter()
            .map(|row| row.substitute(variable, &replacement))
            .collect::<Vec<_>>();
        if constraints.iter().any(KernelBooleanPolynomial::is_one) {
            continue;
        }
        constraints.retain(|row| !row.is_zero());
        constraints.sort();
        constraints.dedup();
        for (phase, coefficient) in coefficients {
            let mut phase = phase.clone();
            phase.substitute(variable, &replacement);
            let coefficient = normalize_scalar(coefficient.substitute(variable, &replacement));
            accumulate_exact_term(
                ExactTerm {
                    constraints: constraints.clone(),
                    coefficient,
                    phase,
                },
                &mut result,
                &mut atoms,
            )?;
        }
    }
    result.retain(|_, coefficients| !coefficients.is_empty());
    Some(result)
}
