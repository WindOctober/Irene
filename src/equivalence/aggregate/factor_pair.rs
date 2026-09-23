//! Bounded one-to-two factor search; similarity only schedules exact proofs.
use super::collection::{ExactAggregate, ExactTerm, accumulate_exact_term};
use super::factor_match::Proof;
use super::phase_unit::charge_cells;
use super::scalar::integer;
use super::{KernelPhasePolynomial, KernelScalar, KernelVariable};
use std::collections::{BTreeMap, BTreeSet};

const MAX_FACTORS: usize = 128;

/// One left factor may represent two right factors. Rank all distinct pair
/// proposals and try at most 16, proving the FULL product equation, optionally
/// up to a certified nonzero unit. Support/counts alone prove nothing.
pub(super) fn find(
    factor: &ExactAggregate,
    remaining: &[&ExactAggregate],
    backend: &mut impl Proof,
) -> Option<(usize, usize, ExactAggregate)> {
    if *backend.probes() == 0 || remaining.len() > MAX_FACTORS {
        return None;
    }
    charge_cells(factor, backend.phase_cells())?;
    for sum in remaining {
        charge_cells(sum, backend.phase_cells())?;
    }
    let support = |sum: &ExactAggregate| {
        sum.values()
            .flat_map(BTreeMap::keys)
            .flat_map(KernelPhasePolynomial::variables)
            .collect::<BTreeSet<_>>()
    };
    let target = support(factor);
    let supports = remaining.iter().map(|sum| support(sum)).collect::<Vec<_>>();
    let mut candidates = Vec::new();
    for a in 0..remaining.len() {
        for b in a + 1..remaining.len() {
            *backend.phase_cells() = backend
                .phase_cells()
                .checked_sub(1 + target.len() + supports[a].len() + supports[b].len())?;
            let union = supports[a]
                .union(&supports[b])
                .cloned()
                .collect::<BTreeSet<_>>();
            let difference = target.symmetric_difference(&union).collect::<Vec<_>>();
            let inputs = difference
                .iter()
                .filter(|v| matches!(v, KernelVariable::InputKet(_) | KernelVariable::InputBra(_)))
                .count();
            candidates.push(((inputs, difference.len(), a, b), a, b));
        }
    }
    candidates.sort_by_key(|(rank, _, _)| *rank);
    for (_, a, b) in candidates.into_iter().take(16) {
        *backend.probes() = backend.probes().checked_sub(1)?;
        let product = backend.multiply(remaining[a].clone(), remaining[b].clone())?;
        if backend.equal(factor, &product) {
            let mut unit = ExactAggregate::new();
            accumulate_exact_term(
                ExactTerm {
                    constraints: Vec::new(),
                    coefficient: KernelScalar::Rational(integer(1)),
                    phase: KernelPhasePolynomial::default(),
                },
                &mut unit,
                &mut 0,
            )?;
            return Some((a, b, unit));
        }
        if let Some(unit) = backend.unit(factor, &product) {
            return Some((a, b, unit));
        }
    }
    None
}

#[cfg(test)]
mod tests;
