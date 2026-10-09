//! Reconstruct a guarded, nonzero constant-magnitude phase function.
//! Every free Boolean cofactor is evaluated exactly; no sampling or division
//! by a potentially zero factor is used. Refusal preserves the original sum.
use std::collections::{BTreeMap, BTreeSet};

use num_rational::BigRational;

use super::collection::{ExactAggregate, ExactEntry, ExactTerm, accumulate_exact_term};
use super::free_split::restrict_aggregate;
use super::scalar::scalar_conditions_within_budget;
use super::witness;
use super::{KernelBooleanPolynomial, KernelPhasePolynomial, KernelScalar, KernelVariable};

/// All leaves, not selected points: reconstruct a single phase function by
/// Boolean interpolation only when every leaf has the SAME positive rational
/// magnitude. Preserve the source's identical selector outside this proof.
pub(super) fn collapse(
    source: &ExactAggregate,
    cells: &mut usize,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
) -> Option<ExactAggregate> {
    if source.len() != 1 {
        return None;
    }
    charge_cells(source, cells)?;
    let (entry, coefficients) = source.first_key_value()?;
    let mut variables = BTreeSet::new();
    for (phase, scalar) in coefficients {
        variables.extend(phase.variables());
        if !scalar_conditions_within_budget(scalar, |condition| {
            variables.extend(condition.variables());
            variables.len() <= 8
        }) {
            return None;
        }
    }
    if variables.len() > 8 || variables.iter().any(KernelVariable::is_bound_path) {
        return None;
    }
    let unguarded = BTreeMap::from([(
        ExactEntry {
            constraints: Vec::new(),
        },
        coefficients.clone(),
    )]);
    let (scalar, phase) = interpolate_phase_unit(
        unguarded,
        &variables.into_iter().collect::<Vec<_>>(),
        cells,
        free,
        algebra,
    )?;
    let mut result = ExactAggregate::new();
    accumulate_exact_term(
        ExactTerm {
            constraints: entry.constraints.clone(),
            coefficient: KernelScalar::Rational(scalar),
            phase,
        },
        &mut result,
        &mut 0,
    )?;
    Some(result)
}

fn interpolate_phase_unit(
    source: ExactAggregate,
    variables: &[KernelVariable],
    cells: &mut usize,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
) -> Option<(BigRational, KernelPhasePolynomial)> {
    charge_cells(&source, cells)?;
    let Some((variable, rest)) = variables.split_first() else {
        let (scalar, turns) = witness::constant_monomial(&source, algebra)?;
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(
            &KernelBooleanPolynomial::one(),
            crate::symbolic::PhaseCoefficient::rational(turns),
        );
        return Some((scalar, phase));
    };
    *free = free.checked_sub(1)?;
    let (a, mut p) = interpolate_phase_unit(
        restrict_aggregate(&source, variable, false)?,
        rest,
        cells,
        free,
        algebra,
    )?;
    let (b, q) = interpolate_phase_unit(
        restrict_aggregate(&source, variable, true)?,
        rest,
        cells,
        free,
        algebra,
    )?;
    if a != b {
        return None;
    }
    // p + x*(q-p), modulo full turns, equals the entire phase function
    // on both Boolean branches. Multiplication uses only the literal x.
    charge_phase(&p, cells)?;
    charge_phase(&q, cells)?;
    let difference = KernelPhasePolynomial::difference(&q, &p);
    let literal = KernelBooleanPolynomial::variable(variable.clone());
    for (monomial, coefficient) in difference.terms() {
        *cells = cells.checked_sub(2 + monomial.variables().count())?;
        p.add_boolean(
            &literal.and(&KernelBooleanPolynomial::from_monomial(monomial.clone())),
            coefficient.clone(),
        );
    }
    Some((a, p))
}

pub(super) fn charge_cells(sum: &ExactAggregate, cells: &mut usize) -> Option<()> {
    for (entry, coefficients) in sum {
        for row in &entry.constraints {
            if !row.is_algebraic() {
                return None;
            }
            for monomial in row.terms() {
                *cells = cells.checked_sub(1 + monomial.variables().count())?;
            }
        }
        for phase in coefficients.keys() {
            if !phase.is_algebraic() {
                return None;
            }
            // Charge even constant atoms so repeated constant products are
            // bounded independently of their empty variable support.
            *cells = cells.checked_sub(1)?;
            for (monomial, _) in phase.terms() {
                *cells = cells.checked_sub(1 + monomial.variables().count())?;
            }
        }
    }
    Some(())
}

pub(super) fn charge_phase(phase: &KernelPhasePolynomial, cells: &mut usize) -> Option<()> {
    if !phase.is_algebraic() {
        return None;
    }
    *cells = cells.checked_sub(1)?;
    for (monomial, _) in phase.terms() {
        *cells = cells.checked_sub(1 + monomial.variables().count())?;
    }
    Some(())
}
