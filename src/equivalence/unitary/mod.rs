//! Stage 1: exact circuit rewriting and unitary trace certificates.
//! Interval distance proofs are an optional public route, not an exact verdict.
use crate::equivalence::{Analysis, EquivalenceConfig, Evidence, Verdict};
use crate::ir::Program;

pub mod dependency;
pub mod interval;
pub mod miter;
pub(in crate::equivalence) mod numeric;
pub(in crate::equivalence) mod operator;
pub(in crate::equivalence) mod rewrite;
mod trace;

pub(super) fn compare(
    left: &Program,
    right: &Program,
    config: &EquivalenceConfig,
) -> Option<Analysis> {
    let norm = trace::certificate(left, right, config)?;
    Some(if norm.is_one() {
        Analysis::new(Verdict::Equivalent, Evidence::UnitaryTraceExact, (0, 0))
    } else {
        let evidence = match norm {
            trace::TraceNorm::Rational(norm) => Evidence::UnitaryTraceMismatch {
                normalized_trace_norm_squared: norm,
            },
            trace::TraceNorm::Cyclotomic(norm) => Evidence::UnitaryTraceCyclotomicMismatch {
                normalized_trace_norm_squared: norm,
            },
        };
        Analysis::new(Verdict::NotEquivalent, evidence, (0, 0))
    })
}

/// Both miter routes require the same complete, declaration-order quantum interface.
/// Partial initialization, permuted pairings, classical outputs and numeric inputs
/// must fall through to the general channel checker.
fn full_quantum_interface(left: &Program, right: &Program, config: &EquivalenceConfig) -> bool {
    use crate::equivalence::{Endpoint, InputPair, OutputPair};
    let l = crate::equivalence::qubits(left);
    let r = crate::equivalence::qubits(right);
    l.len() == r.len()
        && config.numeric_input_pairs.is_empty()
        && config.input_pairs
            == l.iter()
                .cloned()
                .zip(r.iter().cloned())
                .map(|(l, r)| InputPair::quantum(l, r))
                .collect::<Vec<_>>()
        && config.output_pairs
            == l.into_iter()
                .zip(r)
                .map(|(l, r)| OutputPair {
                    left: Endpoint::Quantum(l),
                    right: Endpoint::Quantum(r),
                })
                .collect::<Vec<_>>()
}

/// Keep the shorter circuit on the inverse side, preserving the existing tie rule.
fn orient_pair<'a>(left: &'a Program, right: &'a Program) -> (&'a Program, &'a Program) {
    if left.operation_count() >= right.operation_count() {
        (left, right)
    } else {
        (right, left)
    }
}
