//! Stage 1 equivalence analysis: validated full-unitary trace certificates.
//!
//! Cases outside this certificate return Unknown. HPS structural comparison,
//! density-kernel aggregation, and SMT are not yet connected to this entry point.

use std::fmt;

use num_rational::BigRational;

use crate::ir::{ClassicalBit, Program, Qubit, SymbolId};
use crate::symbolic::{HistoryEntry, HybridPathSum};

mod aggregate;
mod canonical;
mod interface;
mod kernel;
mod smt;
mod tuning;
mod unitary_rewrite;
mod unitary_trace;

pub use kernel::{DensityKernel, KernelBuildError};

pub use interface::{
    Endpoint, EquivalenceConfig, InputPair, InterfaceError, NumericInputPair, OutputPair,
    PreparedComparison, PreparedOutput, PreparedOutputKind, PreparedSide, PreparedTerminal, Side,
    UnsupportedInterface, prepare_comparison,
};

fn qubits(program: &Program) -> Vec<Qubit> {
    program
        .quantum_registers
        .iter()
        .flat_map(|register| {
            (0..register.width).map(|index| Qubit {
                register: register.id,
                index,
            })
        })
        .collect()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    Equivalent,
    NotEquivalent,
    Unknown,
}

impl fmt::Display for Verdict {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::Equivalent => "equivalent",
            Self::NotEquivalent => "not-equivalent",
            Self::Unknown => "unknown",
        };
        formatter.write_str(text)
    }
}

/// Exact evidence supporting a verdict, or the boundary that made it unknown.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Evidence {
    /// A validated full-unitary miter has exact normalized trace modulus one.
    UnitaryTraceExact,
    /// The complete squared trace modulus is rational and different from one.
    UnitaryTraceMismatch {
        normalized_trace_norm_squared: BigRational,
    },
    /// The complete squared trace modulus is nonrational, hence not one.
    /// Canonical power-basis coefficients in Q(zeta_(2^62)), powers below 2^61.
    UnitaryTraceCyclotomicMismatch {
        normalized_trace_norm_squared: Vec<(u64, BigRational)>,
    },
    /// The requested symbolic interface is not supported soundly.
    UnsupportedInterface(UnsupportedInterface),
    /// No complete Stage 1 certificate; later proof stages are not connected.
    Stage1Inconclusive,
}

/// Result of one analysis. A trace mismatch is an exact operator-level
/// certificate, not a sampled input or a solver-generated counterexample.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Analysis {
    pub verdict: Verdict,
    pub evidence: Evidence,
}

/// Checks two programs under an explicit paired interface.
///
/// Malformed endpoint configurations are errors. Valid but unsupported
/// interfaces, inapplicable trace checks, and incomplete exact evaluations
/// yield Unknown, never NotEquivalent. This entry point currently implements
/// only Stage 1; a trace refusal does not run HPS/kernel/SMT fallback stages.
pub fn analyze(
    left: &Program,
    right: &Program,
    config: &EquivalenceConfig,
) -> Result<Analysis, InterfaceError> {
    unitary_rewrite::strategy().map_err(InterfaceError::InvalidConfiguration)?;
    // These exact operator rewrites preserve declarations and interface IDs.
    let rewritten_left = unitary_rewrite::preprocess(left);
    let rewritten_right = unitary_rewrite::preprocess(right);
    let left = rewritten_left.as_ref().unwrap_or(left);
    let right = rewritten_right.as_ref().unwrap_or(right);
    let Some(norm) = unitary_trace::certificate(left, right, config) else {
        return Ok(Analysis {
            verdict: Verdict::Unknown,
            evidence: Evidence::Stage1Inconclusive,
        });
    };
    if norm.is_one() {
        return Ok(Analysis {
            verdict: Verdict::Equivalent,
            evidence: Evidence::UnitaryTraceExact,
        });
    }
    let evidence = match norm {
        unitary_trace::TraceNorm::Rational(norm) => Evidence::UnitaryTraceMismatch {
            normalized_trace_norm_squared: norm,
        },
        unitary_trace::TraceNorm::Cyclotomic(norm) => Evidence::UnitaryTraceCyclotomicMismatch {
            normalized_trace_norm_squared: norm,
        },
    };
    Ok(Analysis {
        verdict: Verdict::NotEquivalent,
        evidence,
    })
}

/// Completes the exact fast-path snapshot with canonical visible outputs.
///
/// History targets are internal names; once current classical outputs are
/// stored separately, their ket/bra equality constraints determine coherence.
/// Classical terminal values impose their own equality constraints, including
/// the terminal Z observation required by mixed quantum/classical pairs.
fn complete_snapshot(side: &PreparedSide) -> HybridPathSum {
    let mut snapshot = side.hps.clone();
    debug_assert_eq!(snapshot.components.len(), 1);
    for (component, terminal) in snapshot.components.iter_mut().zip(&side.terminals) {
        // A constant term multiplies the complete HPS by one global phase.
        // It is irrelevant to the compared density operator even when bound
        // paths remain. The one-component precondition is essential: removing
        // constants separately from multiple components would erase their
        // observable relative phases.
        component.phase.remove_global_phase();
        let classical_outputs = terminal
            .outputs
            .iter()
            .filter(|output| output.kind == PreparedOutputKind::Classical)
            .map(|output| &output.value)
            .collect::<Vec<_>>();
        component.output.history = component
            .output
            .history
            .iter()
            .filter_map(|entry| {
                let value = entry.value().clone();
                // With one component, every kernel term pairs it only with
                // itself. Constant equalities are tautologies, while a
                // history equality repeated by a visible classical output is
                // an idempotent conjunct.
                (!value.is_zero() && !value.is_one() && !classical_outputs.contains(&&value))
                    .then_some(HistoryEntry::Discard { value })
            })
            .collect();
        // At the terminal density boundary, hidden history contributes only
        // the conjunction of ket/bra equalities. Conjunction is commutative
        // and idempotent, so independent measurements may be sorted and
        // duplicate dephasing constraints removed before exact comparison.
        component.output.history.sort();
        component.output.history.dedup();
        for (position, output) in terminal.outputs.iter().enumerate() {
            match output.kind {
                PreparedOutputKind::Quantum => {
                    component.output.quantum.insert(
                        Qubit {
                            register: SymbolId(0),
                            index: position,
                        },
                        output.value.clone(),
                    );
                }
                PreparedOutputKind::Classical => {
                    component.output.classical.insert(
                        ClassicalBit {
                            register: SymbolId(0),
                            index: position,
                        },
                        output.value.clone(),
                    );
                }
            }
        }
    }
    snapshot
}

#[cfg(test)]
mod snapshot_tests;

#[cfg(test)]
mod stage1_tests;
