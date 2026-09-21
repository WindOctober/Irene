//! Exact decomposition of independent bound sums and multiplication of their results.
use std::collections::{BTreeMap, BTreeSet};

use super::collection::{ExactAggregate, ExactTerm, accumulate_exact_term};
use super::scalar::{
    integer, normalize_scalar, scalar_conditions_within_budget, scalar_within_budget,
};
use super::{
    KernelBooleanPolynomial, KernelPhasePolynomial, KernelScalar, MAX_AFFINE_MATRIX_CELLS,
    MAX_BOOLEAN_TERMS, MAX_CONSTRAINTS, MAX_PHASE_TERMS, WorkingTerm,
};

/// Every complete guard and phase selector connects all its bound variables.
/// Free coordinates may be shared between groups. The scalar must be path-free
/// and is retained exactly once, together with the common guards and phase.
pub(super) fn factor(term: &WorkingTerm, guard_phase_cells: usize) -> Option<Vec<WorkingTerm>> {
    if term.paths.len() < 2 || term.paths.len() > MAX_BOOLEAN_TERMS {
        return None;
    }
    let path_free = |polynomial: &KernelBooleanPolynomial| {
        polynomial
            .variables()
            .iter()
            .all(|variable| !term.paths.contains(variable))
    };
    if !scalar_conditions_within_budget(&term.coefficient, path_free) {
        return None;
    }
    // Guard-aware decomposition is optional and restricted by the actual
    // combined guard/phase syntax scanned and copied, not phase term count
    // alone. The previous phase-only admission remains unchanged.
    if !term.constraints.iter().all(path_free)
        && (term.paths.len() > 256
            || term.constraints.len() > 64
            || term
                .constraints
                .iter()
                .map(KernelBooleanPolynomial::variables)
                .chain(term.phase.selectors().map(|(p, _)| p.variables()))
                .try_fold(0usize, |cells, variables| {
                    cells
                        .checked_add(1 + variables.len())
                        .filter(|n| *n <= guard_phase_cells)
                })
                .is_none())
    {
        return None;
    }
    let positions = term
        .paths
        .iter()
        .enumerate()
        .map(|(index, variable)| (variable.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut parents = (0..positions.len()).collect::<Vec<_>>();
    fn root(parents: &mut [usize], mut index: usize) -> usize {
        while parents[index] != index {
            parents[index] = parents[parents[index]];
            index = parents[index];
        }
        index
    }
    let mut occurrences = 0usize;
    for (selector, _) in term.phase.selectors() {
        let mut first = None;
        for variable in &selector.variables() {
            occurrences = occurrences.checked_add(1)?;
            if occurrences > MAX_AFFINE_MATRIX_CELLS {
                return None;
            }
            let Some(&position) = positions.get(variable) else {
                continue;
            };
            let current = root(&mut parents, position);
            if let Some(previous) = first {
                let previous = root(&mut parents, previous);
                parents[current] = previous;
            } else {
                first = Some(current);
            }
        }
    }
    for equation in &term.constraints {
        let mut first = None;
        // An XOR equation is ONE indicator, not a product of indicators for
        // its monomials. All bound variables in the entire row must connect.
        for variable in &equation.variables() {
            occurrences = occurrences.checked_add(1)?;
            if occurrences > MAX_AFFINE_MATRIX_CELLS {
                return None;
            }
            let Some(&position) = positions.get(variable) else {
                continue;
            };
            let current = root(&mut parents, position);
            if let Some(previous) = first {
                let previous = root(&mut parents, previous);
                parents[current] = previous;
            } else {
                first = Some(current);
            }
        }
    }
    let mut groups = BTreeMap::new();
    for (variable, &position) in &positions {
        groups
            .entry(root(&mut parents, position))
            .or_insert_with(BTreeSet::new)
            .insert(variable.clone());
    }
    if groups.len() < 2 {
        return None;
    }
    let mut factors = groups
        .into_iter()
        .map(|(id, paths)| {
            (
                id,
                WorkingTerm {
                    constraints: Vec::new(),
                    paths,
                    coefficient: KernelScalar::Rational(integer(1)),
                    phase: KernelPhasePolynomial::default(),
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut common = WorkingTerm {
        constraints: Vec::new(),
        paths: BTreeSet::new(),
        coefficient: term.coefficient.clone(),
        phase: KernelPhasePolynomial::default(),
    };
    for equation in &term.constraints {
        let owner = equation
            .variables()
            .into_iter()
            .find_map(|variable| positions.get(&variable))
            .map(|&position| root(&mut parents, position));
        match owner {
            Some(owner) => factors.get_mut(&owner)?.constraints.push(equation.clone()),
            None => common.constraints.push(equation.clone()),
        }
    }
    for (selector, coefficient) in term.phase.selectors() {
        let owner = selector
            .variables()
            .into_iter()
            .find_map(|variable| positions.get(&variable))
            .map(|&position| root(&mut parents, position));
        let destination = match owner {
            Some(owner) => &mut factors.get_mut(&owner)?.phase,
            None => &mut common.phase,
        };
        destination.add_boolean(&selector, coefficient.clone());
    }
    Some(
        std::iter::once(common)
            .chain(factors.into_values())
            .collect(),
    )
}

/// Multiplies complete formal aggregates, preserving selectors, phases and weights.
/// The reducer returns Some(None) for an exact zero and None for refusal.
/// Any refusal discards the entire product, never exposing a successful prefix.
pub(super) fn multiply(
    left: ExactAggregate,
    right: ExactAggregate,
    products: &mut usize,
    phase_budget: &mut usize,
    mut reduce: impl FnMut(WorkingTerm) -> Option<Option<ExactTerm>>,
) -> Option<ExactAggregate> {
    if left
        .values()
        .chain(right.values())
        .flat_map(BTreeMap::keys)
        .any(|phase| !phase.is_algebraic())
    {
        return None;
    }
    let left_atoms: usize = left.values().map(BTreeMap::len).sum();
    let right_atoms: usize = right.values().map(BTreeMap::len).sum();
    // Atom count alone does not bound the large monomial sets copied by
    // convolution. Charge an upper bound on all copied phase terms and
    // variable occurrences before constructing any product phase.
    fn phase_cells(aggregate: &ExactAggregate) -> Option<usize> {
        aggregate
            .values()
            .flat_map(BTreeMap::keys)
            .try_fold(0usize, |total, phase| {
                phase.terms().try_fold(total, |total, (monomial, _)| {
                    total
                        .checked_add(1)?
                        .checked_add(monomial.variables().count())
                })
            })
    }
    let cells = phase_cells(&left)?
        .checked_mul(right_atoms)?
        .checked_add(phase_cells(&right)?.checked_mul(left_atoms)?)?;
    *phase_budget = phase_budget.checked_sub(cells)?;
    *products = products.checked_sub(left_atoms.checked_mul(right_atoms)?)?;
    let mut result = ExactAggregate::new();
    let mut atoms = 0;
    for (left_entry, left_coefficients) in &left {
        for (right_entry, right_coefficients) in &right {
            if left_entry
                .constraints
                .len()
                .saturating_add(right_entry.constraints.len())
                > MAX_CONSTRAINTS
            {
                return None;
            }
            let constraints = left_entry
                .constraints
                .iter()
                .chain(&right_entry.constraints)
                .cloned()
                .collect::<Vec<_>>();
            for (left_phase, left_coefficient) in left_coefficients {
                for (right_phase, right_coefficient) in right_coefficients {
                    if left_phase
                        .term_count()
                        .saturating_add(right_phase.term_count())
                        > MAX_PHASE_TERMS
                    {
                        return None;
                    }
                    let coefficient = KernelScalar::Mul(
                        Box::new(left_coefficient.clone()),
                        Box::new(right_coefficient.clone()),
                    );
                    if !scalar_within_budget(&coefficient) {
                        return None;
                    }
                    let mut phase = left_phase.clone();
                    for (monomial, coefficient) in right_phase.terms() {
                        phase.add_boolean(
                            &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                            coefficient.clone(),
                        );
                    }
                    let product = reduce(WorkingTerm {
                        constraints: constraints.clone(),
                        paths: BTreeSet::new(),
                        coefficient: normalize_scalar(coefficient),
                        phase,
                    })?;
                    if let Some(exact) = product {
                        accumulate_exact_term(exact, &mut result, &mut atoms)?;
                    }
                }
            }
        }
    }
    result.retain(|_, coefficients| !coefficients.is_empty());
    Some(result)
}

#[cfg(test)]
mod tests;
