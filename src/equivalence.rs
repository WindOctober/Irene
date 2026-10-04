//! Equivalence analysis by trace, exact HPS, and affine output-support certificates.
//!
//! Cases outside these certificates return Unknown. Density-kernel aggregation
//! and SMT are not yet connected to this entry point.

use bitgauss::BitMatrix;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use num_rational::BigRational;

use crate::ir::{ClassicalBit, Program, Qubit, SymbolId};
use crate::symbolic::{
    BooleanPolynomial, HistoryEntry, HybridPathSum, Monomial, PhasePolynomial, Scalar, Variable,
};

mod aggregate;
mod canonical;
mod interface;
mod input_recovery;
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
    /// A path-free, unit-weight fragment has the same classical observations;
    /// phase erasure is justified and complete snapshots match exactly.
    DeterministicExact,
    /// Exact affine computational-basis output supports differ at a checked input.
    OutputSupportMismatch,
    /// Complete single-component snapshots agree under checked path renaming.
    ExactHps,
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
    /// The trace, structural, and support certificates did not apply; kernel reasoning
    /// would be required, but is not yet connected to this entry point.
    KernelAggregationRequired,
}

/// Result of one analysis. A trace mismatch is an exact operator-level
/// certificate, not a sampled input or a solver-generated counterexample.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Analysis {
    pub verdict: Verdict,
    pub evidence: Evidence,
    pub counterexample: Option<Counterexample>,
}

/// Boolean input assignment in the explicit interface's paired-input order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Counterexample {
    pub ket_inputs: Vec<bool>,
    /// Absent for an output-support witness, which uses one basis input.
    pub bra_inputs: Option<Vec<bool>>,
}

/// Checks two programs under an explicit paired interface.
///
/// Malformed endpoint configurations are errors. Valid but unsupported
/// interfaces and incomplete proofs yield Unknown, never NotEquivalent.
/// A trace refusal falls through to execution, exact HPS comparison, and
/// affine output-support comparison;
/// execution errors propagate as errors. Structural mismatch is inconclusive,
/// not a negative certificate. Kernel/SMT fallback stages are not connected.
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
    if let Some(norm) = unitary_trace::certificate(left, right, config) {
        if norm.is_one() {
            return Ok(Analysis {
                verdict: Verdict::Equivalent,
                evidence: Evidence::UnitaryTraceExact,
                counterexample: None,
            });
        }
        let evidence = match norm {
            unitary_trace::TraceNorm::Rational(norm) => Evidence::UnitaryTraceMismatch {
                normalized_trace_norm_squared: norm,
            },
            unitary_trace::TraceNorm::Cyclotomic(norm) => {
                Evidence::UnitaryTraceCyclotomicMismatch {
                    normalized_trace_norm_squared: norm,
                }
            }
        };
        return Ok(Analysis {
            verdict: Verdict::NotEquivalent,
            evidence,
            counterexample: None,
        });
    }

    let prepared = match prepare_comparison(left, right, config) {
        Ok(prepared) => prepared,
        Err(InterfaceError::Unsupported(reason)) => {
            return Ok(Analysis {
                verdict: Verdict::Unknown,
                evidence: Evidence::UnsupportedInterface(reason),
                counterexample: None,
            });
        }
        Err(error) => return Err(error),
    };
    if exact_hps_certificate(&prepared) {
        return Ok(Analysis {
            verdict: Verdict::Equivalent,
            evidence: Evidence::ExactHps,
            counterexample: None,
        });
    }
    if let Some(analysis) = compare_affine_output_support(&prepared) {
        return Ok(analysis);
    }
    Ok(Analysis {
        verdict: Verdict::Unknown,
        evidence: Evidence::KernelAggregationRequired,
        counterexample: None,
    })
}

/// Detects unequal affine output supports without evaluating amplitudes.
/// Joint (output, history) injectivity prevents cancellation between paths;
/// equal supports are inconclusive, not a proof of channel equality.
fn compare_affine_output_support(prepared: &PreparedComparison) -> Option<Analysis> {
    let left = exact_output_support(&prepared.left)?;
    let right = exact_output_support(&prepared.right)?;
    let witness =
        output_support_witness(&left, &right, prepared.left.quantum_input_positions.len())?;

    let mut analysis = Analysis {
        verdict: Verdict::NotEquivalent,
        evidence: Evidence::OutputSupportMismatch,
        counterexample: None,
    };
    analysis.counterexample = Some(Counterexample {
        ket_inputs: witness,
        bra_inputs: None,
    });
    Some(analysis)
}

struct ExactOutputSupport {
    width: usize,
    path_columns: Vec<Vec<bool>>,
    rank: usize,
    offset: Vec<bool>,
    input_columns: BTreeMap<Qubit, Vec<bool>>,
}

fn exact_output_support(side: &PreparedSide) -> Option<ExactOutputSupport> {
    let [component] = side.hps.components.as_slice() else {
        return None;
    };
    let [terminal] = side.terminals.as_slice() else {
        return None;
    };
    if !component.guard.is_empty() || !scalar_is_definitely_nonzero(&component.scalar) {
        return None;
    }
    let outputs = terminal
        .outputs
        .iter()
        .map(|output| &output.value)
        .collect::<Vec<_>>();
    if outputs.iter().any(|output| !output.is_affine()) {
        return None;
    }
    let history = component
        .output
        .history
        .iter()
        .map(HistoryEntry::value)
        .collect::<Vec<_>>();
    if history.iter().any(|value| !value.is_affine()) {
        return None;
    }

    let paths = component.path_support.iter().copied().collect::<Vec<_>>();
    let path_columns = paths
        .iter()
        .map(|path| coefficient_vector(&outputs, &Monomial::variable(Variable::Path(*path))))
        .collect::<Vec<_>>();
    let joint_columns = paths
        .iter()
        .map(|path| {
            let monomial = Monomial::variable(Variable::Path(*path));
            coefficient_vector(&outputs, &monomial)
                .into_iter()
                .chain(coefficient_vector(&history, &monomial))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    if column_rank(outputs.len() + history.len(), &joint_columns) != paths.len() {
        return None;
    }

    let inputs = outputs
        .iter()
        .flat_map(|output| output.variables())
        .filter_map(|variable| match variable {
            Variable::Input(qubit) => Some(qubit),
            Variable::Path(_) => None,
        })
        .collect::<BTreeSet<_>>();
    let input_columns = inputs
        .into_iter()
        .map(|qubit| {
            let column = coefficient_vector(
                &outputs,
                &Monomial::variable(Variable::Input(qubit.clone())),
            );
            (qubit, column)
        })
        .collect();
    Some(ExactOutputSupport {
        width: outputs.len(),
        rank: column_rank(outputs.len(), &path_columns),
        path_columns,
        offset: coefficient_vector(&outputs, &Monomial::one()),
        input_columns,
    })
}

/// Returns a basis input whose two affine output-support cosets differ.
fn output_support_witness(
    left: &ExactOutputSupport,
    right: &ExactOutputSupport,
    input_count: usize,
) -> Option<Vec<bool>> {
    if left.rank != right.rank
        || column_rank(
            left.width,
            &left
                .path_columns
                .iter()
                .chain(&right.path_columns)
                .cloned()
                .collect::<Vec<_>>(),
        ) != left.rank
    {
        return Some(vec![false; input_count]);
    }

    let offset = xor_vectors(&left.offset, &right.offset);
    if !column_span_contains(left.width, &left.path_columns, &offset) {
        return Some(vec![false; input_count]);
    }

    let inputs = left
        .input_columns
        .keys()
        .chain(right.input_columns.keys())
        .cloned()
        .collect::<BTreeSet<_>>();
    for input in inputs {
        let zero = vec![false; left.width];
        let difference = xor_vectors(
            left.input_columns.get(&input).unwrap_or(&zero),
            right.input_columns.get(&input).unwrap_or(&zero),
        );
        if !column_span_contains(left.width, &left.path_columns, &difference) {
            let mut witness = vec![false; input_count];
            witness[input.index] = true;
            return Some(witness);
        }
    }
    None
}

fn coefficient_vector(outputs: &[&BooleanPolynomial], monomial: &Monomial) -> Vec<bool> {
    outputs
        .iter()
        .map(|output| {
            output
                .affine_coefficient(monomial)
                .expect("support check accepts only affine leaves")
        })
        .collect()
}

fn xor_vectors(left: &[bool], right: &[bool]) -> Vec<bool> {
    left.iter()
        .zip(right)
        .map(|(left, right)| left ^ right)
        .collect()
}

fn column_span_contains(width: usize, columns: &[Vec<bool>], value: &[bool]) -> bool {
    let rank = column_rank(width, columns);
    let mut extended = columns.to_vec();
    extended.push(value.to_vec());
    column_rank(width, &extended) == rank
}

fn column_rank(width: usize, columns: &[Vec<bool>]) -> usize {
    let mut matrix = BitMatrix::build(width, columns.len(), |row, column| columns[column][row]);
    matrix.gauss(false);
    (0..width)
        .filter(|row| (0..columns.len()).any(|column| matrix.bit(*row, column)))
        .count()
}

fn scalar_is_definitely_nonzero(scalar: &Scalar) -> bool {
    match scalar {
        Scalar::Rational(value) => value != &BigRational::from_integer(0.into()),
        Scalar::Sqrt(value) => {
            matches!(value.as_ref(), Scalar::Rational(value) if value > &BigRational::from_integer(0.into()))
        }
        Scalar::Mul(left, right) => {
            scalar_is_definitely_nonzero(left) && scalar_is_definitely_nonzero(right)
        }
        Scalar::Neg(value) | Scalar::Inverse(value) => scalar_is_definitely_nonzero(value),
        Scalar::Select {
            when_true,
            when_false,
            ..
        } => scalar_is_definitely_nonzero(when_true) && scalar_is_definitely_nonzero(when_false),
        Scalar::Sin(_) | Scalar::Cos(_) | Scalar::Add(_, _) => false,
    }
}

/// Snapshot normalization drops only a SINGLE summand's global phase and
/// canonicalizes its self-paired history constraints. Doing so independently
/// on multiple summands could erase observable relative phases/coherence.
fn exact_hps_certificate(prepared: &PreparedComparison) -> bool {
    if prepared.left.hps.components.len() != 1
        || prepared.right.hps.components.len() != 1
    {
        return false;
    }
    // Terminal observations live outside hps: comparing hps alone would omit
    // outputs. The same path bijection must align every field of both snapshots.
    let left = complete_snapshot(&prepared.left);
    let right = complete_snapshot(&prepared.right);
    matches!(
        canonical::exact_match(&left, &right),
        canonical::ExactMatch::Match { .. }
    )
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

#[cfg(test)]
mod stage2_tests;

#[cfg(test)]
mod support_tests;
