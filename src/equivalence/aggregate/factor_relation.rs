//! Exact factor relations F = u*G, with a nonzero rational/phase unit u.
//! Fixed binomial identities are proved algebraically. Other candidates must
//! pass the caller's complete equality check with the original selectors.
//! None is inconclusive; no possibly-zero factor is divided out.
use super::collection::{ExactAggregate, ExactEntry, ExactTerm, accumulate_exact_term};
use super::free_split::restrict_aggregate;
use super::phase_unit::{charge_cells, charge_phase};
use super::scalar::{integer, scalar_conditions_within_budget};
use super::witness;
use super::{
    KernelBooleanPolynomial, KernelPhasePolynomial, KernelScalar, KernelVariable, MAX_PHASE_TERMS,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::collections::{BTreeMap, BTreeSet};

const MAX_ORIENTATION_LEFT_TERMS: usize = 512;

/// Propose a nonzero monomial unit from atom pivots, then prove the WHOLE
/// factor equation left = unit * right. Pivot syntax alone proves nothing.
/// The unit is multiplied into the left common coefficient, so phases and
/// scales remain accounted for after matching. All probes share one budget.
/// `verify` must prove left = unit * right on the COMPLETE original pair,
/// including all selectors. None aborts after a resource/admission refusal;
/// Some(false) declines the candidate without certifying inequality.
pub(super) fn matching_unit(
    left: &ExactAggregate,
    right: &ExactAggregate,
    cells: &mut usize,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
    probes: &mut usize,
    verify: &mut impl FnMut(
        &ExactAggregate,
        &mut usize,
        &mut usize,
        &mut witness::ConstantBudget,
    ) -> Option<bool>,
) -> Option<ExactAggregate> {
    if let Some(unit) = conditional_binomial_unit(left, right, cells) {
        *probes = probes.checked_sub(1)?;
        return Some(unit);
    }
    if let Some(unit) = relative_phase_unit(left, right, cells, free, algebra) {
        *probes = probes.checked_sub(1)?;
        // Replay the reconstructed unit against the entire original pair,
        // including every selector, even after exhaustive interpolation.
        if verify(&unit, cells, free, algebra)? {
            return Some(unit);
        }
    }
    for (left_phase, left_scalar) in left.values().flat_map(BTreeMap::iter).take(4) {
        let KernelScalar::Rational(left_scalar) = left_scalar else {
            continue;
        };
        for (right_phase, right_scalar) in right.values().flat_map(BTreeMap::iter).take(4) {
            let KernelScalar::Rational(right_scalar) = right_scalar else {
                continue;
            };
            if *left_scalar == integer(0)
                || *right_scalar == integer(0)
                || left_scalar.numer().bits() > 4096
                || left_scalar.denom().bits() > 4096
                || right_scalar.numer().bits() > 4096
                || right_scalar.denom().bits() > 4096
            {
                continue;
            }
            let phase = KernelPhasePolynomial::difference(left_phase, right_phase);
            let scalar = left_scalar / right_scalar;
            if phase.term_count() == 0 && scalar == integer(1) {
                continue;
            }
            *probes = probes.checked_sub(1)?;
            let mut unit = ExactAggregate::new();
            accumulate_exact_term(
                ExactTerm {
                    constraints: Vec::new(),
                    coefficient: KernelScalar::Rational(scalar),
                    phase,
                },
                &mut unit,
                &mut 0,
            )?;
            if verify(&unit, cells, free, algebra)? {
                return Some(unit);
            }
        }
    }
    None
}

/// Exhaustive bounded relative-unit interpolation. On every Boolean leaf,
/// either BOTH values are zero, or both are nonzero rational/root monomials
/// whose ratio has a common positive magnitude. Zero leaves do not license
/// cancellation: they are explicitly checked on both sides and merely leave
/// the unit unconstrained there. A caller also replays the full equation.
pub(super) fn relative_phase_unit(
    left: &ExactAggregate,
    right: &ExactAggregate,
    cells: &mut usize,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
) -> Option<ExactAggregate> {
    let mut admission = 4096;
    for source in [left, right] {
        if source.values().map(BTreeMap::len).sum::<usize>() > 32 {
            return None;
        }
        charge_cells(source, &mut admission)?;
        charge_cells(source, cells)?;
        for (entry, coefficients) in source {
            if entry
                .constraints
                .iter()
                .any(|row| row.variables().iter().any(KernelVariable::is_bound_path))
                || coefficients
                    .keys()
                    .any(|phase| phase.variables().iter().any(KernelVariable::is_bound_path))
                || coefficients.values().any(|scalar| {
                    !scalar_conditions_within_budget(scalar, |row| {
                        row.variables()
                            .iter()
                            .all(|variable| !variable.is_bound_path())
                    })
                })
            {
                return None;
            }
        }
    }
    // Removing an identical selector from BOTH sides strengthens the
    // equality obligation; it does not identify differently guarded terms.
    let common = left
        .keys()
        .next()?
        .constraints
        .iter()
        .filter(|row| {
            left.keys()
                .chain(right.keys())
                .all(|entry| entry.constraints.contains(row))
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    let unguard = |source: &ExactAggregate| -> Option<ExactAggregate> {
        let mut result = ExactAggregate::new();
        for (entry, coefficients) in source {
            let constraints = entry
                .constraints
                .iter()
                .filter(|row| !common.contains(*row))
                .cloned()
                .collect::<Vec<_>>();
            for (phase, coefficient) in coefficients {
                accumulate_exact_term(
                    ExactTerm {
                        constraints: constraints.clone(),
                        coefficient: coefficient.clone(),
                        phase: phase.clone(),
                    },
                    &mut result,
                    &mut 0,
                )?;
            }
        }
        Some(result)
    };
    let left = unguard(left)?;
    let right = unguard(right)?;
    let mut variables = BTreeSet::new();
    for source in [&left, &right] {
        for (entry, coefficients) in source {
            for row in &entry.constraints {
                variables.extend(row.variables());
            }
            for (phase, scalar) in coefficients {
                variables.extend(phase.variables());
                if !scalar_conditions_within_budget(scalar, |row| {
                    variables.extend(row.variables());
                    variables.len() <= 8
                }) {
                    return None;
                }
            }
        }
    }
    if variables.len() > 8 || variables.iter().any(KernelVariable::is_bound_path) {
        return None;
    }
    let (scalar, phase) = interpolate_relative_unit(
        left,
        right,
        &variables.into_iter().collect::<Vec<_>>(),
        cells,
        free,
        algebra,
    )?;
    let mut unit = ExactAggregate::new();
    accumulate_exact_term(
        ExactTerm {
            constraints: Vec::new(),
            coefficient: KernelScalar::Rational(scalar.unwrap_or_else(|| integer(1))),
            phase,
        },
        &mut unit,
        &mut 0,
    )?;
    Some(unit)
}

fn interpolate_relative_unit(
    left: ExactAggregate,
    right: ExactAggregate,
    variables: &[KernelVariable],
    cells: &mut usize,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
) -> Option<(Option<BigRational>, KernelPhasePolynomial)> {
    charge_cells(&left, cells)?;
    charge_cells(&right, cells)?;
    let Some((variable, rest)) = variables.split_first() else {
        let Some((a, p)) = witness::constant_monomial(&left, algebra) else {
            return (witness::constant_is_zero(&left, algebra)
                && witness::constant_is_zero(&right, algebra))
            .then_some((None, KernelPhasePolynomial::default()));
        };
        let (b, q) = witness::constant_monomial(&right, algebra)?;
        let scalar = a / b;
        if scalar.numer().bits() > 4096 || scalar.denom().bits() > 4096 {
            return None;
        }
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(
            &KernelBooleanPolynomial::one(),
            crate::symbolic::PhaseCoefficient::rational(p - q),
        );
        return Some((Some(scalar), phase));
    };
    *free = free.checked_sub(1)?;
    let (a, mut p) = interpolate_relative_unit(
        restrict_aggregate(&left, variable, false)?,
        restrict_aggregate(&right, variable, false)?,
        rest,
        cells,
        free,
        algebra,
    )?;
    let (b, q) = interpolate_relative_unit(
        restrict_aggregate(&left, variable, true)?,
        restrict_aggregate(&right, variable, true)?,
        rest,
        cells,
        free,
        algebra,
    )?;
    if matches!((&a, &b), (Some(a), Some(b)) if a != b) {
        return None;
    }
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
    Some((a.or(b), p))
}

/// For Boolean f and L=(1-2f)R, exactly
/// 1+exp(2*pi*i*L) = exp(-2*pi*i*f*R) (1+exp(2*pi*i*R)).
/// Check the complete phase identity, coefficients and selector, not just
/// a pivot. No division by a possibly zero binomial occurs.
pub(super) fn conditional_binomial_unit(
    left: &ExactAggregate,
    right: &ExactAggregate,
    cells: &mut usize,
) -> Option<ExactAggregate> {
    fn binomial(sum: &ExactAggregate) -> Option<(&ExactEntry, &KernelPhasePolynomial)> {
        if sum.len() != 1 {
            return None;
        }
        let (entry, coefficients) = sum.first_key_value()?;
        if coefficients.len() != 2
            || coefficients.first_key_value()?.0.term_count() != 0
            || coefficients
                .values()
                .any(|coefficient| *coefficient != KernelScalar::Rational(integer(1)))
        {
            return None;
        }
        let phase = coefficients.last_key_value()?.0;
        phase.is_algebraic().then_some((entry, phase))
    }
    let (left_entry, left_phase) = binomial(left)?;
    let (right_entry, right_phase) = binomial(right)?;
    if left_entry != right_entry || right_phase.term_count() > 256 {
        return None;
    }
    if let Some(phase) = parity_orientation_phase(left_phase, right_phase, cells)
        .or_else(|| large_parity_orientation_phase(left_phase, right_phase, cells))
        .or_else(|| orientation_phase(left_phase, right_phase, cells, 0))
    {
        let mut unit = ExactAggregate::new();
        accumulate_exact_term(
            ExactTerm {
                constraints: Vec::new(),
                coefficient: KernelScalar::Rational(integer(1)),
                phase,
            },
            &mut unit,
            &mut 0,
        )?;
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!("aggregate factored cofactored orientation verified");
        }
        return Some(unit);
    }
    let difference = KernelPhasePolynomial::difference(left_phase, right_phase);
    let variables = difference
        .variables()
        .into_iter()
        .take(8)
        .collect::<Vec<_>>();
    if variables.iter().any(KernelVariable::is_bound_path) {
        return None;
    }
    // At most eight literals and 28 two-literal parities.
    for index in 0..variables.len() {
        for other in index..variables.len() {
            let mut flip = KernelBooleanPolynomial::variable(variables[index].clone());
            if other != index {
                flip = flip.xor(&KernelBooleanPolynomial::variable(variables[other].clone()));
            }
            let unit_phase = negative_gated_phase(right_phase, &flip, cells)?;
            let mut expected = right_phase.clone();
            add_phase(&mut expected, &unit_phase)?;
            add_phase(&mut expected, &unit_phase)?;
            if expected != *left_phase {
                continue;
            }
            let mut unit = ExactAggregate::new();
            accumulate_exact_term(
                ExactTerm {
                    constraints: Vec::new(),
                    coefficient: KernelScalar::Rational(integer(1)),
                    phase: unit_phase,
                },
                &mut unit,
                &mut 0,
            )?;
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!("aggregate factored conditional orientation verified");
            }
            return Some(unit);
        }
    }
    None
}

/// Propose just one three-literal parity when those coordinates dominate a
/// large expanded phase. Frequency only schedules the proposal: the entire
/// modular identity L=R-2*f*R must hold before its unit can be returned.
pub(super) fn parity_orientation_phase(
    left: &KernelPhasePolynomial,
    right: &KernelPhasePolynomial,
    cells: &mut usize,
) -> Option<KernelPhasePolynomial> {
    if left.term_count() > MAX_ORIENTATION_LEFT_TERMS
        || right.term_count() > 256
        || left.term_count() < right.term_count().saturating_mul(4)
    {
        return None;
    }
    for phase in [left, right] {
        charge_phase(phase, cells)?;
    }
    let difference = KernelPhasePolynomial::difference(left, right);
    let mut counts = BTreeMap::<KernelVariable, usize>::new();
    for (monomial, _) in difference.terms() {
        for variable in monomial.variables() {
            if variable.is_bound_path() {
                return None;
            }
            *counts.entry(variable.clone()).or_default() += 1;
        }
    }
    let maximum = *counts.values().max()?;
    let variables = counts
        .into_iter()
        .filter(|(_, count)| *count * 2 >= maximum)
        .map(|(variable, _)| variable)
        .take(4)
        .collect::<Vec<_>>();
    if variables.len() != 3 {
        return None;
    }
    let flip = variables
        .into_iter()
        .fold(KernelBooleanPolynomial::zero(), |sum, variable| {
            sum.xor(&KernelBooleanPolynomial::variable(variable))
        });
    let unit = negative_gated_phase(right, &flip, cells)?;
    let mut expected = right.clone();
    add_phase(&mut expected, &unit)?;
    add_phase(&mut expected, &unit)?;
    (*left == expected).then_some(unit)
}

/// A distinct bounded proposal for an expanded parity-controlled orientation.
/// Unlike the four-deep cofactor tree, this checks ONE whole polynomial
/// identity. Support frequencies only propose up to six literal XOR inputs.
/// No ordinary phase/tree cap is lifted and all work is charged as before.
pub(super) fn large_parity_orientation_phase(
    left: &KernelPhasePolynomial,
    right: &KernelPhasePolynomial,
    cells: &mut usize,
) -> Option<KernelPhasePolynomial> {
    if !(513..=2048).contains(&left.term_count()) || right.term_count() > 256 {
        return None;
    }
    let mut admission_cells = 32768usize;
    for phase in [left, right] {
        for (m, c) in phase.terms() {
            admission_cells = admission_cells.checked_sub(1 + m.variables().count())?;
            if m.variables().any(KernelVariable::is_bound_path) {
                return None;
            }
            let r = c.as_rational()?;
            if r.numer().bits() > 256 || r.denom().bits() > 256 {
                return None;
            }
        }
        charge_phase(phase, cells)?;
    }
    let difference = KernelPhasePolynomial::difference(left, right);
    let mut counts = BTreeMap::<KernelVariable, usize>::new();
    for (m, _) in difference.terms() {
        for v in m.variables() {
            *counts.entry(v.clone()).or_default() += 1;
        }
    }
    let maximum = *counts.values().max()?;
    let variables = counts
        .iter()
        .filter(|(_, count)| **count * 2 >= maximum)
        .take(7)
        .map(|(v, _)| v.clone())
        .collect::<Vec<_>>();
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate large parity proposal: left={} right={} variables={variables:?} remaining={}",
            left.term_count(),
            right.term_count(),
            cells
        );
    }
    if !(1..=6).contains(&variables.len()) {
        return None;
    }
    let flip = variables
        .into_iter()
        .fold(KernelBooleanPolynomial::zero(), |p, v| {
            p.xor(&KernelBooleanPolynomial::variable(v))
        });
    let unit = negative_gated_phase_bounded(right, &flip, cells, 6)?;
    // Replay ALL coefficients. This is L=(1-2*f)R, not an inference from
    // size, dominant support or any free-coordinate sample.
    let mut expected = right.clone();
    add_phase(&mut expected, &unit)?;
    add_phase(&mut expected, &unit)?;
    (*left == expected).then_some(unit)
}

/// A complete bounded proof tree for binomial orientation. Each leaf proves
/// L=R or L=-R as a full phase polynomial; the returned unit is respectively
/// 0 or -R. Recombine the two FREE cofactors by Shannon interpolation,
/// never summing or discarding a branch. No atom/selector cancellation.
pub(super) fn orientation_phase(
    left: &KernelPhasePolynomial,
    right: &KernelPhasePolynomial,
    cells: &mut usize,
    depth: usize,
) -> Option<KernelPhasePolynomial> {
    if left.term_count() > MAX_ORIENTATION_LEFT_TERMS || right.term_count() > 256 {
        return None;
    }
    for phase in [left, right] {
        charge_phase(phase, cells)?;
    }
    if left == right {
        return Some(KernelPhasePolynomial::default());
    }
    let negative = KernelPhasePolynomial::difference(&KernelPhasePolynomial::default(), right);
    if *left == negative {
        return Some(negative);
    }
    if depth >= 4 {
        return None;
    }
    let difference = KernelPhasePolynomial::difference(left, right);
    let mut counts = BTreeMap::<KernelVariable, usize>::new();
    for (monomial, _) in difference.terms() {
        for variable in monomial.variables() {
            if variable.is_bound_path() {
                return None;
            }
            *counts.entry(variable.clone()).or_default() += 1;
        }
    }
    let (variable, _) = counts.into_iter().max_by_key(|(_, count)| *count)?;
    let mut units = Vec::new();
    for value in [false, true] {
        let mut l = left.clone();
        let mut r = right.clone();
        let replacement = KernelBooleanPolynomial::from(value);
        l.substitute(&variable, &replacement);
        r.substitute(&variable, &replacement);
        units.push(orientation_phase(&l, &r, cells, depth + 1)?);
    }
    let delta = KernelPhasePolynomial::difference(&units[0], &units[1]);
    let gate = negative_gated_phase(&delta, &KernelBooleanPolynomial::variable(variable), cells)?;
    let mut result = units.remove(0);
    add_phase(&mut result, &gate)?;
    Some(result)
}

pub(super) fn negative_gated_phase(
    phase: &KernelPhasePolynomial,
    flip: &KernelBooleanPolynomial,
    cells: &mut usize,
) -> Option<KernelPhasePolynomial> {
    negative_gated_phase_bounded(phase, flip, cells, 3)
}

fn negative_gated_phase_bounded(
    phase: &KernelPhasePolynomial,
    flip: &KernelBooleanPolynomial,
    cells: &mut usize,
    max_flip: usize,
) -> Option<KernelPhasePolynomial> {
    // Original callers propose <=3 ANF monomials (<=7 lift products).
    // The separately admitted large-parity proposal uses <=6 (<=63).
    // Charge the entire upper bound before constructing each product.
    if !flip.is_algebraic() || !phase.is_algebraic() {
        return None;
    }
    let flip_variables = flip
        .terms()
        .map(|monomial| monomial.variables().count())
        .sum::<usize>();
    if max_flip > 6
        || flip.term_count() > max_flip
        || phase.term_count() > 256
        || flip_variables > max_flip
    {
        return None;
    }
    // A literal has one product, not the three needed for a two-term XOR.
    // Each lifted product contains only source variables and variables of
    // flip. Collisions/Boolean idempotence can only reduce this upper bound.
    let products_per_term = (1usize << flip.term_count()) - 1;
    let mut result = KernelPhasePolynomial::default();
    for (monomial, coefficient) in phase.terms() {
        let cost = products_per_term * (1 + flip_variables + monomial.variables().count());
        *cells = cells.checked_sub(cost)?;
        result.add_boolean(
            &flip.and(&KernelBooleanPolynomial::from_monomial(monomial.clone())),
            coefficient.scaled(BigInt::from(-1)),
        );
    }
    Some(result)
}

pub(super) fn add_phase(
    destination: &mut KernelPhasePolynomial,
    source: &KernelPhasePolynomial,
) -> Option<()> {
    if !destination.is_algebraic() || !source.is_algebraic() {
        return None;
    }
    if destination.term_count().saturating_add(source.term_count()) > MAX_PHASE_TERMS {
        return None;
    }
    for (monomial, coefficient) in source.terms() {
        destination.add_boolean(
            &KernelBooleanPolynomial::from_monomial(monomial.clone()),
            coefficient.clone(),
        );
    }
    Some(())
}

#[cfg(test)]
#[path = "../../../tests/unit/equivalence/aggregate/factor_relation/tests.rs"]
mod tests;
