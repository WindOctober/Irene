//! Factor out a nonzero rational scale and a phase from a complete aggregate.
//! The candidate is accepted only if multiplying it back reconstructs the
//! original formal aggregate. This is a sufficient normalization, not a
//! canonical form for all semantically equal functions. None is inconclusive.
use super::collection::{ExactAggregate, ExactTerm, accumulate_exact_term};
use super::factor_relation::add_phase;
use super::scalar::{integer, normalize_scalar};
use super::{KernelPhasePolynomial, KernelScalar};
use num_rational::BigRational;
use std::collections::BTreeMap;

/// Extract only an explicitly nonzero rational times an exponential. Try at
/// most eight atom pivots and choose a sufficient canonical representative.
/// Replay the exact inverse transformation and require the original formal
/// aggregate back; unit extraction is not trusted without reconstruction.
pub(super) fn normalize(
    source: ExactAggregate,
) -> Option<(ExactAggregate, BigRational, KernelPhasePolynomial)> {
    let mut best: Option<(ExactAggregate, BigRational, KernelPhasePolynomial)> = None;
    for (common, pivot) in source.values().flat_map(BTreeMap::iter).take(8) {
        let KernelScalar::Rational(scalar) = pivot else {
            continue;
        };
        if scalar == &integer(0) || scalar.numer().bits() > 4096 || scalar.denom().bits() > 4096 {
            continue;
        }
        let mut normalized = ExactAggregate::new();
        let mut atoms = 0;
        for (entry, coefficients) in &source {
            for (phase, coefficient) in coefficients {
                accumulate_exact_term(
                    ExactTerm {
                        constraints: entry.constraints.clone(),
                        phase: KernelPhasePolynomial::difference(phase, common),
                        coefficient: normalize_scalar(
                            coefficient
                                .clone()
                                .multiply(KernelScalar::Rational(scalar.recip())),
                        ),
                    },
                    &mut normalized,
                    &mut atoms,
                )?;
            }
        }
        if best
            .as_ref()
            .is_none_or(|(current, _, _)| normalized < *current)
        {
            best = Some((normalized, scalar.clone(), common.clone()));
        }
    }
    let (normalized, scalar, common) = best?;
    // TODO: Once the forward transformation and its helper preconditions
    // independently guarantee exact preservation of every scalar, phase and
    // selector (including refusal without partial results), make replay an
    // opt-in validation/debug check rather than a default runtime requirement.
    // Retain this check until those guarantees no longer depend on replay.
    let mut replay = ExactAggregate::new();
    let mut atoms = 0;
    for (entry, coefficients) in &normalized {
        for (phase, coefficient) in coefficients {
            let mut phase = phase.clone();
            add_phase(&mut phase, &common)?;
            accumulate_exact_term(
                ExactTerm {
                    constraints: entry.constraints.clone(),
                    phase,
                    coefficient: normalize_scalar(
                        coefficient
                            .clone()
                            .multiply(KernelScalar::Rational(scalar.clone())),
                    ),
                },
                &mut replay,
                &mut atoms,
            )?;
        }
    }
    (replay == source).then_some((normalized, scalar, common))
}

#[cfg(test)]
#[path = "../../../tests/unit/equivalence/aggregate/factor_normalize/tests.rs"]
mod tests;
