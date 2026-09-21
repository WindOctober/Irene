//! Exact collection of selector-bearing, path-free kernel contributions.
//! Distinct formal atoms are not assumed to denote distinct complex values.
use std::collections::BTreeMap;

use super::scalar::{normalize_scalar, ratio, scalar_within_budget};
use super::{KernelBooleanPolynomial, KernelMonomial, KernelPhasePolynomial, KernelScalar};

const MAX_AGGREGATE_ATOMS: usize = 100_000;

/// A path-free density term in a sufficient exact normal form.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ExactTerm {
    pub(super) constraints: Vec<KernelBooleanPolynomial>,
    pub(super) coefficient: KernelScalar,
    pub(super) phase: KernelPhasePolynomial,
}

/// One symbolic density-kernel entry after every bound path was eliminated.
///
/// Constraints remain part of the entry selector.  Treating differently
/// guarded contributions as equal without a canonical Boolean decision
/// procedure would be unsound, so this sufficient form combines only
/// structurally identical selectors and output indices.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ExactEntry {
    pub(super) constraints: Vec<KernelBooleanPolynomial>,
}

/// An exact formal complex coefficient.
///
/// The outer key denotes `exp(2*pi*i*phase)` and the value is its exact real
/// scalar coefficient.  Equal phase atoms are added coherently.  Keeping
/// distinct phase polynomials separate is incomplete but sound: this pass
/// never assumes two different roots of unity or symbolic phases are unequal.
pub(super) type ExactCoefficient = BTreeMap<KernelPhasePolynomial, KernelScalar>;
pub(super) type ExactAggregate = BTreeMap<ExactEntry, ExactCoefficient>;

pub(super) fn aggregate_difference(
    mut left: ExactAggregate,
    right: ExactAggregate,
) -> Option<ExactAggregate> {
    let mut atoms = left.values().map(BTreeMap::len).sum();
    for (entry, coefficients) in right {
        for (phase, coefficient) in coefficients {
            accumulate_exact_term(
                ExactTerm {
                    constraints: entry.constraints.clone(),
                    phase,
                    coefficient: normalize_scalar(KernelScalar::Neg(Box::new(coefficient))),
                },
                &mut left,
                &mut atoms,
            )?;
        }
    }
    left.retain(|_, coefficients| !coefficients.is_empty());
    Some(left)
}

/// Adds a complete term; on refusal the caller must discard the whole aggregate.
/// The in-place map and atom counter may already have changed when None is returned.
pub(super) fn accumulate_exact_term(
    mut exact: ExactTerm,
    aggregate: &mut ExactAggregate,
    atoms: &mut usize,
) -> Option<()> {
    // exp(2*pi*i*(p+1/2)) = -exp(2*pi*i*p). This is an exact
    // coefficient identity, not a claim that different phase atoms differ.
    if exact
        .phase
        .coefficient(&KernelMonomial::one())
        .rational_part()
        >= ratio(1, 2)
    {
        exact.phase.add_boolean(
            &KernelBooleanPolynomial::one(),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
        exact.coefficient = normalize_scalar(KernelScalar::Neg(Box::new(exact.coefficient)));
    }
    let ExactTerm {
        constraints,
        coefficient,
        phase,
    } = exact;
    if coefficient.is_zero() {
        return Some(());
    }
    let coefficient_map = aggregate.entry(ExactEntry { constraints }).or_default();
    let had_atom = coefficient_map.contains_key(&phase);
    let combined = coefficient_map
        .remove(&phase)
        .map_or(coefficient.clone(), |current| {
            normalize_scalar(KernelScalar::Add(Box::new(current), Box::new(coefficient)))
        });
    if !scalar_within_budget(&combined) {
        return None;
    }
    if !combined.is_zero() {
        if !had_atom {
            *atoms = atoms.checked_add(1)?;
            if *atoms > MAX_AGGREGATE_ATOMS {
                return None;
            }
        }
        coefficient_map.insert(phase, combined);
    } else if had_atom {
        *atoms = atoms.saturating_sub(1);
    }
    Some(())
}

#[cfg(test)]
mod tests;
