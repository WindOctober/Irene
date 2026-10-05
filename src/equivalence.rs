//! Equivalence checking for normalized hybrid path sums.
//!
//! Full-unitary trace and exact HPS certificates can finish before density
//! kernel construction. Remaining comparisons use exact term reduction and
//! coefficient aggregation, with SMT for admitted complete expressions.
//! Unsupported encodings and incomplete proofs return `Unknown`, not NEQ.

use aggregate::{AggregateComparison, compare_kernels};
use bitgauss::BitMatrix;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use num_rational::BigRational;

use crate::ir::{ClassicalBit, Program, Qubit, SymbolId};
use crate::symbolic::{
    BooleanPolynomial, HistoryEntry, HybridPathSum, Monomial, PhasePolynomial, Scalar, Variable,
};

use canonical::{ExactMatch, exact_match};

mod aggregate;
mod boolean_query;
mod canonical;
pub mod dependency_miter;
mod deterministic;
mod graph_compare;
mod input_recovery;
mod interface;
pub mod interval_hps;
mod kernel;
mod model_witness;
mod numeric;
mod operator;
mod phase_compare;
mod smt;
mod solver_query;
mod tuning;
mod unitary_rewrite;
mod unitary_trace;

pub use smt::{
    PortfolioConsensus, PortfolioResult, SOLVER_TIMEOUT, Solver, SolverDisagreement, SolverResult,
    SolverStatus,
};

pub use kernel::{DensityKernel, KernelBuildError};
use kernel::{KernelInput, KernelTerminalInput, build_kernel};

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
        formatter.write_str(match self {
            Self::Equivalent => "equivalent",
            Self::NotEquivalent => "not-equivalent",
            Self::Unknown => "unknown",
        })
    }
}

/// Exact evidence supporting a verdict, or the boundary that made it unknown.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Evidence {
    // ---------------------------------------------------------------------
    //                         Equivalent proofs
    // ---------------------------------------------------------------------
    /// Complete single-component snapshots agree under checked path renaming.
    ExactHps,
    /// A fixed path bijection preserves all outputs and phase modulo one.
    PathwiseGraph,
    /// A path-free, unit-weight fragment has equal observable outputs and
    /// satisfies the applicable history and relative-phase obligations.
    DeterministicExact,
    /// Both density kernels reduce exactly after constrained path elimination.
    DensityKernelExact,
    /// A validated full-unitary miter has exact normalized trace modulus one.
    UnitaryTraceExact,

    // ---------------------------------------------------------------------
    //                     Not-equivalent witnesses
    // ---------------------------------------------------------------------
    /// Exact output-difference SMT query is SAT.
    OutputCounterexample,
    /// Exact relative-phase query is SAT after proving injectivity.
    PhaseCounterexample,
    /// The two programs have different exact affine computational-basis supports.
    OutputSupportMismatch,
    /// A complete density-kernel entry difference was evaluated exactly and is nonzero.
    DensityEntryCounterexample,
    /// The complete normalized trace of a validated full-unitary miter has
    /// this exact squared modulus, different from one (no tolerance).
    UnitaryTraceMismatch {
        normalized_trace_norm_squared: BigRational,
    },
    /// Exact nonrational squared trace modulus in Q(zeta_(2^62)), encoded as
    /// canonical (power, rational coefficient) pairs with power below 2^61.
    UnitaryTraceCyclotomicMismatch {
        normalized_trace_norm_squared: Vec<(u64, BigRational)>,
    },

    // ---------------------------------------------------------------------
    //                 Unsupported or incomplete analyses
    // ---------------------------------------------------------------------
    /// The requested symbolic interface is not supported soundly.
    UnsupportedInterface(UnsupportedInterface),
    /// The exact fast paths did not apply; kernel coefficient aggregation is required.
    KernelAggregationRequired,

    // ---------------------------------------------------------------------
    //                         Analysis failures
    // ---------------------------------------------------------------------
    /// The exact density kernel could not be constructed.
    KernelBuild(KernelBuildError),
    /// A required SMT obligation had no sufficient definitive answer.
    SolverInconclusive,
}

/// Exact channel-matrix entry witnessing a difference between two programs.
///
/// Output vectors use quantum-only / classical-only terminal-pair order.
/// The difference is
/// `sum_j (c_j + sqrt(3)*d_j) zeta^j`, multiplied by every `exact_factors`
/// entry, with zeta = exp(2*pi*i/root_order).
/// The root order is a power of two. Exponents are below root_order/2;
/// x^(root_order/2)+1 is irreducible over Q, so a nonempty
/// normalized coefficient vector certifies a genuinely nonzero complex value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DensityCounterexample {
    pub ket_inputs: Vec<bool>,
    pub bra_inputs: Vec<bool>,
    pub ket_outputs: Vec<bool>,
    pub bra_outputs: Vec<bool>,
    pub classical_outputs: Vec<bool>,
    pub root_of_unity_order: u64,
    pub difference_coefficients: Vec<(u64, BigRational)>,
    /// Coefficients of sqrt(3) times the same cyclotomic basis, independent
    /// over the power-of-two cyclotomic field. Empty for the dyadic fragment.
    pub sqrt_three_coefficients: Vec<(u64, BigRational)>,
    /// Additional nonzero exact factors multiplying the two vectors above.
    pub exact_factors: Vec<DensityExactFactor>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DensityExactFactor {
    pub coefficients: Vec<(u64, BigRational)>,
    pub sqrt_three_coefficients: Vec<(u64, BigRational)>,
}

/// Result of one equivalence analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Analysis {
    pub verdict: Verdict,
    pub evidence: Evidence,
    pub counterexample: Option<Counterexample>,
    pub density_counterexample: Option<DensityCounterexample>,
    /// Exact query evidence, recording either a designated backend or portfolio.
    pub solver_queries: Vec<PortfolioResult>,
    /// Sizes of the exact, unaggregated left and right density kernels.
    /// `(0, 0)` also denotes a graph-native proof that needed no kernel build.
    pub kernel_terms: (usize, usize),
}

impl Analysis {
    fn new(verdict: Verdict, evidence: Evidence, kernel_terms: (usize, usize)) -> Self {
        Self {
            verdict,
            evidence,
            counterexample: None,
            density_counterexample: None,
            solver_queries: Vec::new(),
            kernel_terms,
        }
    }
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
/// not a negative certificate. Restricted path-free SMT comparison follows;
/// Remaining comparisons use exact term reduction and coefficient aggregation.
pub fn analyze(
    left: &Program,
    right: &Program,
    config: &EquivalenceConfig,
) -> Result<Analysis, InterfaceError> {
    crate::symbolic::representation_stats::run_if_requested(|| analyze_inner(left, right, config))
}

fn analyze_inner(
    left: &Program,
    right: &Program,
    config: &EquivalenceConfig,
) -> Result<Analysis, InterfaceError> {
    unitary_rewrite::strategy().map_err(InterfaceError::InvalidConfiguration)?;
    // Exact operator rewrites are also safe for a single unitary side of a
    // channel comparison. Keep each side's declarations and paired interface.
    let rewritten_left = unitary_rewrite::preprocess(left);
    let rewritten_right = unitary_rewrite::preprocess(right);
    let left = rewritten_left.as_ref().unwrap_or(left);
    let right = rewritten_right.as_ref().unwrap_or(right);
    if let Some(norm) = unitary_trace::certificate(left, right, config) {
        return Ok(if norm.is_one() {
            Analysis::new(Verdict::Equivalent, Evidence::UnitaryTraceExact, (0, 0))
        } else {
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
            Analysis::new(Verdict::NotEquivalent, evidence, (0, 0))
        });
    }
    let prepared = match prepare_comparison(left, right, config) {
        Ok(prepared) => prepared,
        Err(InterfaceError::Unsupported(reason)) => {
            return Ok(Analysis::new(
                Verdict::Unknown,
                Evidence::UnsupportedInterface(reason),
                (0, 0),
            ));
        }
        Err(error) => return Err(error),
    };

    // Graph-native certificates must run before the optional bounded
    // polynomial backend. No ANF expansion is needed for these proofs.
    let kernel_terms = (0, 0);

    // Terminal values are stored outside `PreparedSide::hps`. Reinsert them
    // under canonical keys before applying the exact HPS certificate; omitting
    // them here would prove equality of programs with different outputs.
    //
    // This certificate is deliberately limited to one component on each
    // side. A component is an amplitude summand, not an independently
    // normalized state: in a multi-component HPS, coherence between two
    // summands depends on their histories being positionally compatible.
    // `complete_snapshot` canonicalizes the self-pairing constraints that
    // remain for a single component, so applying it component-by-component
    // would erase precisely that cross-component information.
    let snapshots =
        if prepared.left.hps.components.len() == 1 && prepared.right.hps.components.len() == 1 {
            let left_snapshot = complete_snapshot(&prepared.left);
            let right_snapshot = complete_snapshot(&prepared.right);
            let exact = exact_match(&left_snapshot, &right_snapshot);
            if matches!(exact, ExactMatch::Match { .. }) {
                return Ok(Analysis::new(
                    Verdict::Equivalent,
                    Evidence::ExactHps,
                    kernel_terms,
                ));
            }
            Some((left_snapshot, right_snapshot))
        } else {
            None
        };

    if let Some(analysis) = compare_affine_output_support(&prepared, kernel_terms) {
        return Ok(analysis);
    }

    if let Some(analysis) = deterministic::compare(&prepared, kernel_terms, snapshots) {
        return analysis.map_err(InterfaceError::from);
    }

    if let Some(result) = graph_compare::compare(&prepared) {
        return result.map_err(InterfaceError::from);
    }

    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!("comparison prepared; kernel build start");
    }
    let left_kernel = match kernel_for(&prepared.left) {
        Ok(kernel) => kernel,
        Err(error) => {
            return Ok(Analysis::new(
                Verdict::Unknown,
                Evidence::KernelBuild(error),
                (0, 0),
            ));
        }
    };
    let right_kernel = match kernel_for(&prepared.right) {
        Ok(kernel) => kernel,
        Err(error) => {
            return Ok(Analysis::new(
                Verdict::Unknown,
                Evidence::KernelBuild(error),
                (left_kernel.terms.len(), 0),
            ));
        }
    };
    let kernel_terms = (left_kernel.terms.len(), right_kernel.terms.len());
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!("kernel build finished; polynomial aggregation start");
    }

    match compare_kernels(&left_kernel, &right_kernel) {
        AggregateComparison::Equivalent => {
            return Ok(Analysis::new(
                Verdict::Equivalent,
                Evidence::DensityKernelExact,
                kernel_terms,
            ));
        }
        AggregateComparison::SmtEquivalent(query) => {
            let mut analysis = Analysis::new(
                Verdict::Equivalent,
                Evidence::DensityKernelExact,
                kernel_terms,
            );
            analysis.solver_queries.push(query);
            return Ok(analysis);
        }
        AggregateComparison::Different(witness, query) => {
            let mut analysis = Analysis::new(
                Verdict::NotEquivalent,
                Evidence::DensityEntryCounterexample,
                kernel_terms,
            );
            analysis.density_counterexample = Some(*witness);
            analysis.solver_queries.push(query);
            return Ok(analysis);
        }
        AggregateComparison::Unknown => {}
    }

    Ok(Analysis::new(
        Verdict::Unknown,
        Evidence::KernelAggregationRequired,
        kernel_terms,
    ))
}

/// Preserve canonical input order and per-kind terminal order when lowering
/// one prepared program. Hidden history stays in the HPS for ket/bra pairing.
fn kernel_for(side: &PreparedSide) -> Result<DensityKernel, KernelBuildError> {
    let input_variables = side.hps.input.quantum.keys().cloned().collect();
    let terminals = side
        .terminals
        .iter()
        .map(|terminal| {
            let mut input = KernelTerminalInput::default();
            for output in &terminal.outputs {
                match output.kind {
                    PreparedOutputKind::Quantum => input.quantum.push(output.value.clone()),
                    PreparedOutputKind::Classical => input.classical.push(output.value.clone()),
                }
            }
            input
        })
        .collect();
    build_kernel(&KernelInput::new(&side.hps, input_variables, terminals))
}

/// Detects unequal affine output supports without evaluating amplitudes.
/// Joint (output, history) injectivity prevents cancellation between paths;
/// equal supports are inconclusive, not a proof of channel equality.
fn compare_affine_output_support(
    prepared: &PreparedComparison,
    kernel_terms: (usize, usize),
) -> Option<Analysis> {
    let left = exact_output_support(&prepared.left)?;
    let right = exact_output_support(&prepared.right)?;
    let witness =
        output_support_witness(&left, &right, prepared.left.quantum_input_positions.len())?;

    let mut analysis = Analysis::new(
        Verdict::NotEquivalent,
        Evidence::OutputSupportMismatch,
        kernel_terms,
    );
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
    if !column_span_contains(left.width, &left.path_columns, left.rank, &offset) {
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
        if !column_span_contains(left.width, &left.path_columns, left.rank, &difference) {
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

fn column_span_contains(width: usize, columns: &[Vec<bool>], rank: usize, value: &[bool]) -> bool {
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

#[cfg(test)]
mod kernel_adapter_tests;
