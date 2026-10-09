//! Match every factor once and accumulate certified units for an EQ proof.
//! This is EQ-only: a missed match, failed arithmetic or exhausted budget is
//! inconclusive. Support similarity ranks proposals but cannot certify one.
use super::collection::{ExactAggregate, ExactTerm, accumulate_exact_term, aggregate_difference};
use super::factor_relation::add_phase;
use super::free_split::{forget_common_selector, remove_common_phase};
use super::phase_unit::charge_cells;
use super::product_form::Product;
use super::scalar::integer;
use super::{KernelPhasePolynomial, KernelScalar, KernelVariable};
use num_rational::BigRational;
use std::collections::{BTreeMap, BTreeSet};

/// Every accepted relation is exact and covers the WHOLE factor:
/// unit(F,G) returns u only after proving F=uG; pair returns a<b and a unit
/// proving F=u*G[a]*G[b]. Returned units must also pass collect_unit admission.
/// Arithmetic and proof budgets remain shared across all calls.
pub(super) trait Proof {
    fn probes(&mut self) -> &mut usize;
    fn phase_cells(&mut self) -> &mut usize;
    fn equal(&mut self, left: &ExactAggregate, right: &ExactAggregate) -> bool;
    fn unit(&mut self, left: &ExactAggregate, right: &ExactAggregate) -> Option<ExactAggregate>;
    fn pair(
        &mut self,
        factor: &ExactAggregate,
        remaining: &[&ExactAggregate],
    ) -> Option<(usize, usize, ExactAggregate)>;
    fn multiply(&mut self, left: ExactAggregate, right: ExactAggregate) -> Option<ExactAggregate>;
    fn zero_product(&mut self, factors: Vec<ExactAggregate>) -> bool;
}

pub(super) fn matches(
    left: &Product,
    right: &Product,
    backend: &mut impl Proof,
    relevant: &mut BTreeSet<KernelVariable>,
) -> bool {
    if right.factors.len() < left.factors.len() || right.factors.len() > left.factors.len() + 1 {
        return false;
    }
    let mut common = left.common.clone();
    let mut unit_scalar = integer(1);
    let mut unit_phase = KernelPhasePolynomial::default();
    let mut remaining = right.factors.iter().collect::<Vec<_>>();
    for (position, factor) in left.factors.iter().enumerate() {
        let mut matched = remaining.iter().position(|other| *other == factor);
        if matched.is_none()
            && remaining.len() > left.factors.len() - position
            && let Some((a, b, unit)) = backend.pair(factor, &remaining)
        {
            if a >= b || b >= remaining.len() {
                return false;
            }
            if collect_unit(
                &unit,
                &mut unit_scalar,
                &mut unit_phase,
                backend.phase_cells(),
            )
            .is_none()
            {
                return false;
            }
            // Each right factor is consumed exactly once; the final
            // obligation still contains the entire original right product.
            remaining.remove(b);
            remaining.remove(a);
            continue;
        }
        if matched.is_none() {
            // Input support is usually a stable anchor across phase
            // orientation changes. Rank proposals, but never accept or
            // reject equality from support alone; prove every chosen pair.
            let support = |sum: &ExactAggregate| {
                sum.values()
                    .flat_map(BTreeMap::keys)
                    .flat_map(KernelPhasePolynomial::variables)
                    .collect::<BTreeSet<_>>()
            };
            let variables = support(factor);
            let mut candidates = remaining
                .iter()
                .enumerate()
                .map(|(index, other)| {
                    let other_variables = support(other);
                    let difference = variables
                        .symmetric_difference(&other_variables)
                        .collect::<Vec<_>>();
                    let inputs = difference
                        .iter()
                        .filter(|variable| {
                            matches!(
                                variable,
                                KernelVariable::InputKet(_) | KernelVariable::InputBra(_)
                            )
                        })
                        .count();
                    ((inputs, difference.len(), index), index, *other)
                })
                .collect::<Vec<_>>();
            candidates.sort_by_key(|(rank, _, _)| *rank);
            for (_, index, other) in candidates {
                if *backend.probes() == 0 {
                    return false;
                }
                *backend.probes() -= 1;
                if backend.equal(factor, other) {
                    matched = Some(index);
                    break;
                }
                if let Some(unit) = backend.unit(factor, other) {
                    if collect_unit(
                        &unit,
                        &mut unit_scalar,
                        &mut unit_phase,
                        backend.phase_cells(),
                    )
                    .is_none()
                    {
                        return false;
                    }
                    matched = Some(index);
                    break;
                }
            }
        }
        let Some(index) = matched else {
            relevant.extend(
                factor
                    .values()
                    .flat_map(BTreeMap::keys)
                    .flat_map(KernelPhasePolynomial::variables),
            );
            return false;
        };
        remaining.remove(index);
    }
    if unit_scalar != integer(1) || unit_phase.term_count() != 0 {
        let mut unit = ExactAggregate::new();
        if accumulate_exact_term(
            ExactTerm {
                constraints: Vec::new(),
                coefficient: KernelScalar::Rational(unit_scalar),
                phase: unit_phase,
            },
            &mut unit,
            &mut 0,
        )
        .is_none()
        {
            return false;
        }
        let Some(updated) = backend.multiply(common, unit) else {
            return false;
        };
        common = updated;
    }
    let common_equal = backend.equal(&common, &right.common);
    let proved = common_equal
        || aggregate_difference(common, right.common.clone()).is_some_and(|difference| {
            let Some(difference) = forget_common_selector(difference).and_then(remove_common_phase)
            else {
                return false;
            };
            let mut factors = vec![difference];
            factors.extend(right.factors.iter().cloned());
            backend.zero_product(factors)
        });
    proved && remaining.is_empty()
}

/// Collect only certified, unguarded, nonzero rational/exponential units.
/// Associativity lets us multiply their product into the large common term
/// once. No selector or non-unit factor may enter this accumulator.
pub(super) fn collect_unit(
    unit: &ExactAggregate,
    scalar: &mut BigRational,
    phase: &mut KernelPhasePolynomial,
    cells: &mut usize,
) -> Option<()> {
    if unit.len() != 1 {
        return None;
    }
    let (entry, coefficients) = unit.first_key_value()?;
    if !entry.constraints.is_empty() || coefficients.len() != 1 {
        return None;
    }
    let (next_phase, KernelScalar::Rational(next_scalar)) = coefficients.first_key_value()? else {
        return None;
    };
    if *next_scalar == integer(0)
        || next_scalar.numer().bits() > 4096
        || next_scalar.denom().bits() > 4096
    {
        return None;
    }
    charge_cells(unit, cells)?;
    let next = &*scalar * next_scalar;
    if next.numer().bits() > 4096 || next.denom().bits() > 4096 {
        return None;
    }
    add_phase(phase, next_phase)?;
    *scalar = next;
    Some(())
}

#[cfg(test)]
#[path = "../../../tests/unit/equivalence/aggregate/factor_match/tests.rs"]
mod tests;
