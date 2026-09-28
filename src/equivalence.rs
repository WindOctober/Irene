//! Equivalence checking for normalized hybrid path sums.
//!
//! Full-unitary trace and exact HPS certificates can finish before density
//! kernel construction. Remaining comparisons use exact term reduction and
//! coefficient aggregation, with SMT for admitted complete expressions.
//! Unsupported encodings and incomplete proofs return `Unknown`, not NEQ.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use bitgauss::BitMatrix;
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::ir::{ClassicalBit, Program, Qubit, SymbolId};
use crate::symbolic::{
    BooleanPolynomial, HistoryEntry, HybridPathSum, Monomial, PhasePolynomial, Scalar, Variable,
};

mod aggregate;
mod canonical;
mod graph_compare;
mod interface;
mod kernel;
mod smt;
mod tuning;
mod unitary_rewrite;
mod unitary_trace;
pub mod interval_hps;
pub mod dependency_miter;

pub use interface::{
    Endpoint, EquivalenceConfig, InputPair, InterfaceError, NumericInputPair, OutputPair,
    PreparedComparison, PreparedOutput, PreparedOutputKind, PreparedSide, PreparedTerminal, Side,
    UnsupportedInterface, prepare_comparison,
};
pub use kernel::{DensityKernel, KernelBuildError};
pub use smt::{
    PortfolioConsensus, PortfolioResult, SOLVER_TIMEOUT, Solver, SolverDisagreement, SolverResult,
    SolverStatus,
};

use aggregate::{AggregateComparison, compare_kernels};
use canonical::{ExactMatch, exact_match};
use kernel::{KernelInput, KernelTerminalInput, build_kernel};

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
    /// Both normalized HPS values are identical after certified path alpha-renaming.
    ExactHps,
    /// Complete output/phase equality under a checked bound-path bijection.
    PathwiseGraph,
    /// A deterministic channel has the same observed Boolean map and phase up to a constant.
    DeterministicExact,
    /// Both density kernels reduce exactly after constrained path elimination.
    DensityKernelExact,
    /// A validated full-unitary miter has exact normalized trace modulus one.
    UnitaryTraceExact,

    // ---------------------------------------------------------------------
    //                     Not-equivalent witnesses
    // ---------------------------------------------------------------------
    /// A solver found and Irene rechecked an input with different outputs.
    OutputCounterexample,
    /// A solver found and Irene rechecked an input pair with different relative phase.
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
    /// Solvers disagreed, or none produced a conclusive answer.
    SolverInconclusive,
}

/// A Boolean counterexample over the canonical paired inputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Counterexample {
    pub ket_inputs: Vec<bool>,
    /// Present for a phase/coherence witness, absent for an output witness.
    pub bra_inputs: Option<Vec<bool>>,
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

/// Checks two programs under an explicit paired interface.
///
/// Invalid endpoint configurations and contradictory solver answers are
/// returned as errors. A valid but
/// unsupported symbolic interface or an incomplete proof procedure produces
/// an ordinary [`Verdict::Unknown`] analysis.
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
    }

    if let Some(analysis) = compare_affine_output_support(&prepared, kernel_terms) {
        return Ok(analysis);
    }

    if let Some(analysis) = compare_deterministic(&prepared, kernel_terms) {
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

/// Detects unequal output-support cardinalities without summing amplitudes.
///
/// For one unguarded component, an affine `(visible output, hidden history)`
/// map with full column rank distinguishes every path assignment. Paths with
/// the same visible output are therefore orthogonal environment states rather
/// than interfering amplitudes. The visible support is exactly the affine
/// image of the output map, independently of phase.
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
        Scalar::Rational(value) => value != &rational_zero(),
        Scalar::Sqrt(value) => {
            matches!(value.as_ref(), Scalar::Rational(value) if value > &rational_zero())
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

/// Completes the exact fast-path snapshot with canonical visible outputs.
///
/// History targets are internal names; once current classical outputs are
/// stored separately, only the ordered history values determine which paths
/// remain coherent.  Classical terminal values are also recorded as hidden
/// values, which is exactly the terminal Z dephasing required by Q/C pairs.
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

/// Decides the path-free, history-free, unit-amplitude fragment.
fn compare_deterministic(
    prepared: &PreparedComparison,
    kernel_terms: (usize, usize),
) -> Option<Result<Analysis, SolverDisagreement>> {
    let left = prepared.left.hps.components.first()?;
    let right = prepared.right.hps.components.first()?;
    if prepared.left.hps.components.len() != 1
        || prepared.right.hps.components.len() != 1
        || !left.path_support.is_empty()
        || !right.path_support.is_empty()
        || !left.guard.is_empty()
        || !right.guard.is_empty()
        || left.scalar != Scalar::one()
        || right.scalar != Scalar::one()
    {
        return None;
    }

    let inputs: Vec<_> = prepared.left.hps.input.quantum.keys().cloned().collect();
    let positions = inputs
        .iter()
        .cloned()
        .enumerate()
        .map(|(position, qubit)| (qubit, position))
        .collect::<BTreeMap<_, _>>();
    let left_outputs = &prepared.left.terminals[0].outputs;
    let right_outputs = &prepared.right.terminals[0].outputs;
    let differences = left_outputs
        .iter()
        .zip(right_outputs)
        .map(|(left, right)| left.value.xor(&right.value))
        .filter(|difference| !difference.is_zero())
        .collect::<Vec<_>>();

    let mut solver_queries = Vec::new();
    if !differences.is_empty() {
        let query = boolean_miter(&differences, &positions, "x")?;
        let portfolio = match run_miter(&query, &variable_names(positions.len(), "x")) {
            Ok(result) => result,
            Err(error) => return Some(Err(error)),
        };
        match portfolio.consensus {
            PortfolioConsensus::Sat => {
                // This miter is an exact output-difference encoding. SAT is
                // the certificate; a checked concrete assignment is optional.
                let ket_inputs = validated_model(&portfolio, &differences, &positions, "x");
                let mut analysis = Analysis::new(
                    Verdict::NotEquivalent,
                    Evidence::OutputCounterexample,
                    kernel_terms,
                );
                analysis.counterexample = ket_inputs.map(|ket_inputs| Counterexample {
                    ket_inputs,
                    bra_inputs: None,
                });
                analysis.solver_queries.push(portfolio);
                return Some(Ok(analysis));
            }
            // Structural inequality of XAG roots is not semantic inequality.
            // The exact graph miter being UNSAT proves all outputs identical;
            // continue with the independent history/phase obligations.
            PortfolioConsensus::Unsat => {
                solver_queries.push(portfolio);
            }
            PortfolioConsensus::Inconclusive => {
                let mut analysis =
                    Analysis::new(Verdict::Unknown, Evidence::SolverInconclusive, kernel_terms);
                analysis.solver_queries.push(portfolio);
                return Some(Ok(analysis));
            }
        }
    }

    let all_classical = prepared
        .output_kinds
        .iter()
        .all(|kind| *kind == PreparedOutputKind::Classical);
    if all_classical {
        // For a path-free basis transformer followed only by classical Z
        // observations, phase is unobservable.  Histories still matter: erase
        // only phase and require the complete canonical snapshots to match.
        let mut left_snapshot = complete_snapshot(&prepared.left);
        let mut right_snapshot = complete_snapshot(&prepared.right);
        left_snapshot.components[0].phase = PhasePolynomial::zero();
        right_snapshot.components[0].phase = PhasePolynomial::zero();
        // Output equality was proved above, not merely guessed from syntax.
        // Align only those certified terminal fields; preserve every residual
        // history/dephasing constraint and all other snapshot fields.
        for (position, output) in left_outputs.iter().enumerate() {
            right_snapshot.components[0].output.classical.insert(
                ClassicalBit {
                    register: SymbolId(0),
                    index: position,
                },
                output.value.clone(),
            );
        }
        if !matches!(
            exact_match(&left_snapshot, &right_snapshot),
            ExactMatch::Match { .. }
        ) {
            return None;
        }
        let mut analysis = Analysis::new(
            Verdict::Equivalent,
            Evidence::DeterministicExact,
            kernel_terms,
        );
        analysis.solver_queries = solver_queries;
        return Some(Ok(analysis));
    }

    if !left.output.history.is_empty() || !right.output.history.is_empty() {
        return None;
    }
    if phases_equal_up_to_global(&left.phase, &right.phase) {
        let mut analysis = Analysis::new(
            Verdict::Equivalent,
            Evidence::DeterministicExact,
            kernel_terms,
        );
        analysis.solver_queries = solver_queries;
        return Some(Ok(analysis));
    }

    // Relative phase is observable only when the selected quantum output is a
    // one-to-one image of every input basis state.  The injectivity and phase
    // variation obligations are separate Boolean/bit-vector SMT queries.
    if prepared
        .output_kinds
        .contains(&PreparedOutputKind::Classical)
        || left_outputs.len() != inputs.len()
    {
        return None;
    }
    let output_values = left_outputs
        .iter()
        .map(|output| output.value.clone())
        .collect::<Vec<_>>();
    if !triangular_injectivity(&output_values, &positions) {
        let injectivity = injectivity_query(&output_values, &positions)?;
        let injectivity_result = match run_graph_query(&injectivity) {
            Ok(result) => result,
            Err(error) => return Some(Err(error)),
        };
        if injectivity_result.consensus != PortfolioConsensus::Unsat {
            let mut analysis =
                Analysis::new(Verdict::Unknown, Evidence::SolverInconclusive, kernel_terms);
            analysis.solver_queries = solver_queries;
            analysis.solver_queries.push(injectivity_result);
            return Some(Ok(analysis));
        }
        solver_queries.push(injectivity_result);
    }

    let delta = rational_phase_difference(&left.phase, &right.phase)?;
    let query = phase_variation_query(&delta, &positions)?;
    let names = variable_names(positions.len(), "x")
        .into_iter()
        .chain(variable_names(positions.len(), "z"))
        .collect::<Vec<_>>();
    let portfolio = match run_miter(&query, &names) {
        Ok(result) => result,
        Err(error) => return Some(Err(error)),
    };
    match portfolio.consensus {
        PortfolioConsensus::Sat => {
            // Injectivity and the exact rational phase encoding were checked
            // above, so model availability is not another proof obligation.
            let inputs = validated_phase_model(&portfolio, &delta, &positions);
            let mut analysis = Analysis::new(
                Verdict::NotEquivalent,
                Evidence::PhaseCounterexample,
                kernel_terms,
            );
            analysis.counterexample = inputs.map(|(ket_inputs, bra_inputs)| Counterexample {
                ket_inputs,
                bra_inputs: Some(bra_inputs),
            });
            analysis.solver_queries = solver_queries;
            analysis.solver_queries.push(portfolio);
            Some(Ok(analysis))
        }
        PortfolioConsensus::Unsat => {
            let mut analysis = Analysis::new(
                Verdict::Equivalent,
                Evidence::DeterministicExact,
                kernel_terms,
            );
            analysis.solver_queries = solver_queries;
            analysis.solver_queries.push(portfolio);
            Some(Ok(analysis))
        }
        PortfolioConsensus::Inconclusive => {
            let mut analysis =
                Analysis::new(Verdict::Unknown, Evidence::SolverInconclusive, kernel_terms);
            analysis.solver_queries = solver_queries;
            analysis.solver_queries.push(portfolio);
            Some(Ok(analysis))
        }
    }
}

/// A sufficient injectivity proof by recovering inputs from output values.
/// If an output is `x xor f(K)`, where every variable in K is already
/// recoverable, then x is recoverable too. Constants do not affect the rule.
/// Importantly, x must occur only as a singleton: `x xor x*y` is not a
/// recovery equation. Failure (including the work cap) merely defers to SMT.
fn triangular_injectivity(outputs: &[BooleanPolynomial], inputs: &BTreeMap<Qubit, usize>) -> bool {
    let mut budget = 1_000_000usize;
    let mut rows = Vec::new();
    for output in outputs {
        let Some(remaining) = budget.checked_sub(1) else {
            return false;
        };
        budget = remaining;
        let mut linear = BTreeSet::new();
        let mut nonlinear = BTreeSet::new();
        let factors = output.xor_terms();
        for factor in &factors {
            for variable in factor.variables() {
                let Some(remaining) = budget.checked_sub(1) else {
                    return false;
                };
                budget = remaining;
                let Variable::Input(input) = variable else {
                    return false;
                };
                if !inputs.contains_key(&input) {
                    return false;
                }
                if factor.as_variable().is_some() {
                    linear.insert(input.clone());
                } else {
                    nonlinear.insert(input.clone());
                }
            }
        }
        rows.push((linear, nonlinear));
    }
    let mut known = BTreeSet::new();
    loop {
        if known.len() == inputs.len() {
            return true;
        }
        let before = known.len();
        for (linear, nonlinear) in &rows {
            let Some(remaining) = budget.checked_sub(linear.len() + nonlinear.len() + 1) else {
                return false;
            };
            budget = remaining;
            if !nonlinear.is_subset(&known) {
                continue;
            }
            let mut unresolved = linear.difference(&known);
            if let Some(input) = unresolved.next()
                && unresolved.next().is_none()
            {
                known.insert(input.clone());
            }
        }
        if known.len() == before {
            // Known nonlinear contributions can be removed from each output
            // value. XOR combinations of the remaining linear forms are
            // therefore also recoverable. RREF may expose a singleton that
            // is not present in any original output (e.g. a linear mixer).
            let eligible = rows
                .iter()
                .filter(|(_, nonlinear)| nonlinear.is_subset(&known))
                .map(|(linear, _)| linear)
                .collect::<Vec<_>>();
            let columns = inputs
                .keys()
                .filter(|input| !known.contains(input))
                .collect::<Vec<_>>();
            let Some(remaining) = eligible
                .len()
                .checked_mul(columns.len())
                .and_then(|cells| budget.checked_sub(cells))
            else {
                return false;
            };
            budget = remaining;
            if eligible.is_empty() {
                return false;
            }
            let mut matrix = BitMatrix::build(eligible.len(), columns.len(), |row, column| {
                eligible[row].contains(columns[column])
            });
            matrix.gauss(true);
            for row in 0..eligible.len() {
                let mut nonzero = (0..columns.len()).filter(|column| matrix.bit(row, *column));
                if let Some(column) = nonzero.next()
                    && nonzero.next().is_none()
                {
                    known.insert(columns[column].clone());
                }
            }
            if known.len() == before {
                return false;
            }
        }
    }
}

fn phases_equal_up_to_global(left: &PhasePolynomial, right: &PhasePolynomial) -> bool {
    let nonconstant = |phase: &PhasePolynomial| {
        phase
            .selectors()
            .filter(|(value, _)| !value.is_one())
            .map(|(value, coefficient)| (value, coefficient.clone()))
            .collect::<Vec<_>>()
    };
    nonconstant(left) == nonconstant(right)
}

fn boolean_miter(
    differences: &[BooleanPolynomial],
    positions: &BTreeMap<Qubit, usize>,
    namespace: &str,
) -> Option<String> {
    let declarations = declarations(positions.len(), &[namespace]);
    let (network, variables) = BooleanPolynomial::graph_network(differences);
    let network = crate::xag::davio::preprocess(network);
    let names = variables
        .iter()
        .map(|v| match v {
            Variable::Input(q) => positions.get(q).map(|i| format!("{namespace}{i}")),
            Variable::Path(_) => None,
        })
        .collect::<Option<Vec<_>>>()?;
    let (definitions, terms) = network.smt(&names, "out_xag_")?;
    Some(smt_script(
        format!("{declarations}{definitions}"),
        smt_or(&terms),
        &[],
    ))
}

/// Ask for values only after SAT. An unconditional get-value after UNSAT is
/// an SMT-LIB protocol error (Z3/cvc5 correctly reject it), not a failed proof.
/// A missing optional model never revokes a definite answer to the exact miter.
fn run_miter(query: &str, values: &[String]) -> Result<PortfolioResult, SolverDisagreement> {
    let proof = run_graph_query(query)?;
    if proof.consensus != PortfolioConsensus::Sat || values.is_empty() {
        return Ok(proof);
    }
    let model = run_graph_query(&format!("{query}(get-value ({}))\n", values.join(" ")))?;
    combine_same_query_results(proof, model)
}

fn combine_same_query_results(
    proof: PortfolioResult,
    mut model: PortfolioResult,
) -> Result<PortfolioResult, SolverDisagreement> {
    // get-value does not change the asserted formula. A contradictory status
    // in the model invocation is an error even if it is from the same backend.
    // Preserve the actual definitive observation as well as model diagnostics,
    // including when the same backend is invoked twice.
    model.results.extend(proof.results);
    model.consensus = smt::consensus(&model.results)?;
    Ok(model)
}

/// Exact Boolean/BV graph obligations use the same designated backend as the
/// exact density encoder. This is a complete graph encoding, not a candidate
/// heuristic. SAT models are still checked by the caller. When the designated
/// backend has no answer, fallback accepts any definite answer but reports
/// contradictory SAT/UNSAT answers as an error.
fn run_graph_query(query: &str) -> Result<PortfolioResult, SolverDisagreement> {
    let result = smt::run_solver(Solver::Bitwuzla, query);
    let consensus = match result.status {
        SolverStatus::Sat => PortfolioConsensus::Sat,
        SolverStatus::Unsat => PortfolioConsensus::Unsat,
        _ => {
            // Retain the existing portfolio as a fallback when the designated
            // backend gives no answer. Non-answers never veto a definite one.
            let mut fallback = smt::run_portfolio(query)?;
            if let Some(bitwuzla) = fallback
                .results
                .iter_mut()
                .find(|r| r.solver == Solver::Bitwuzla)
            {
                bitwuzla.duration += result.duration;
                bitwuzla.stderr = format!(
                    "initial graph attempt: {:?}: {}\n{}",
                    result.status, result.stderr, bitwuzla.stderr
                );
            }
            return Ok(fallback);
        }
    };
    Ok(PortfolioResult {
        consensus,
        results: vec![result],
    })
}

fn injectivity_query(
    outputs: &[BooleanPolynomial],
    positions: &BTreeMap<Qubit, usize>,
) -> Option<String> {
    let distinct_inputs = (0..positions.len())
        .map(|index| format!("(xor x{index} z{index})"))
        .collect::<Vec<_>>();
    let equal_outputs = outputs
        .iter()
        .map(|output| {
            Some(format!(
                "(= {} {})",
                smt_boolean(output, positions, "x")?,
                smt_boolean(output, positions, "z")?
            ))
        })
        .collect::<Option<Vec<_>>>()?;
    let assertion = format!(
        "(and {} {})",
        smt_or(&distinct_inputs),
        smt_and(&equal_outputs)
    );
    Some(smt_script(
        declarations(positions.len(), &["x", "z"]),
        assertion,
        &[],
    ))
}

fn smt_script(declarations: String, assertion: String, values: &[String]) -> String {
    let get_values = if values.is_empty() {
        String::new()
    } else {
        format!("(get-value ({}))\n", values.join(" "))
    };
    format!(
        "(set-logic QF_BV)\n(set-option :produce-models true)\n{declarations}(assert {assertion})\n(check-sat)\n{get_values}"
    )
}

fn declarations(width: usize, namespaces: &[&str]) -> String {
    namespaces
        .iter()
        .flat_map(|namespace| {
            (0..width).map(move |index| format!("(declare-fun {namespace}{index} () Bool)\n"))
        })
        .collect()
}

fn variable_names(width: usize, namespace: &str) -> Vec<String> {
    (0..width)
        .map(|index| format!("{namespace}{index}"))
        .collect()
}

fn smt_boolean(
    polynomial: &BooleanPolynomial,
    positions: &BTreeMap<Qubit, usize>,
    namespace: &str,
) -> Option<String> {
    polynomial.smt_expression(|variable| match variable {
        Variable::Input(qubit) => positions
            .get(qubit)
            .map(|position| format!("{namespace}{position}")),
        Variable::Path(_) => None,
    })
}

fn smt_or(terms: &[String]) -> String {
    smt_fold(terms, "or", "false")
}

fn smt_and(terms: &[String]) -> String {
    smt_fold(terms, "and", "true")
}

fn smt_fold(terms: &[String], operator: &str, identity: &str) -> String {
    terms
        .iter()
        .cloned()
        .fold(identity.to_owned(), |left, right| {
            format!("({operator} {left} {right})")
        })
}

/// Returns the first SAT model that also satisfies Irene's Boolean miter.
/// Non-SAT solver results have no model and are deliberately ignored.
fn validated_model(
    portfolio: &PortfolioResult,
    differences: &[BooleanPolynomial],
    positions: &BTreeMap<Qubit, usize>,
    namespace: &str,
) -> Option<Vec<bool>> {
    portfolio
        .results
        .iter()
        .filter(|result| result.status == SolverStatus::Sat)
        .find_map(|result| {
            let values = parse_boolean_values(&result.stdout, positions.len(), namespace)?;
            let bindings = input_bindings(&values, positions);
            differences
                .iter()
                .any(|difference| evaluate_boolean(difference, &bindings))
                .then_some(values)
        })
}

fn parse_boolean_values(stdout: &str, width: usize, namespace: &str) -> Option<Vec<bool>> {
    if width == 0 {
        return Some(Vec::new());
    }
    let tokens = stdout
        .replace(['(', ')'], " ")
        .split_whitespace()
        .map(str::to_owned)
        .collect::<Vec<_>>();
    (0..width)
        .map(|index| {
            let name = format!("{namespace}{index}");
            let position = tokens.iter().position(|token| token == &name)?;
            match tokens.get(position + 1).map(String::as_str) {
                Some("true") => Some(true),
                Some("false") => Some(false),
                _ => None,
            }
        })
        .collect()
}

fn input_bindings(values: &[bool], positions: &BTreeMap<Qubit, usize>) -> BTreeMap<Variable, bool> {
    positions
        .iter()
        .map(|(qubit, position)| (Variable::Input(qubit.clone()), values[*position]))
        .collect()
}

fn evaluate_boolean(polynomial: &BooleanPolynomial, bindings: &BTreeMap<Variable, bool>) -> bool {
    polynomial
        .evaluate::<std::convert::Infallible>(|v| Ok(bindings.get(v).copied().unwrap_or(false)))
        .unwrap()
}

type RationalPhase = BTreeMap<BooleanPolynomial, BigRational>;

fn rational_phase_difference(
    left: &PhasePolynomial,
    right: &PhasePolynomial,
) -> Option<RationalPhase> {
    let mut difference = BTreeMap::new();
    for (selector, coefficient) in left.selectors() {
        difference.insert(selector, coefficient.as_rational()?);
    }
    for (selector, coefficient) in right.selectors() {
        let value = difference.remove(&selector).unwrap_or_else(rational_zero)
            - coefficient.as_rational()?;
        let value = modulo_one(value);
        if value != rational_zero() {
            difference.insert(selector, value);
        }
    }
    difference.retain(|_, coefficient| {
        *coefficient = modulo_one(coefficient.clone());
        *coefficient != rational_zero()
    });
    Some(difference)
}

fn phase_variation_query(
    phase: &RationalPhase,
    positions: &BTreeMap<Qubit, usize>,
) -> Option<String> {
    let denominator = phase.values().fold(BigInt::from(1), |current, value| {
        lcm(current, value.denom().clone())
    });
    let coefficients = phase
        .iter()
        .filter(|(selector, _)| !selector.is_one())
        .map(|(monomial, coefficient)| {
            let integer = coefficient.numer() * (&denominator / coefficient.denom());
            (monomial.clone(), positive_mod(integer, &denominator))
        })
        .filter(|(_, coefficient)| coefficient != &BigInt::from(0))
        .collect::<Vec<_>>();
    if coefficients.is_empty() {
        return None;
    }
    let maximum = BigInt::from(coefficients.len()) * (&denominator - 1);
    let width = bit_width(if maximum > denominator {
        &maximum
    } else {
        &denominator
    });
    let value = |namespace: &str| -> Option<String> {
        let terms = coefficients
            .iter()
            .map(|(monomial, coefficient)| {
                Some(format!(
                    "(ite {} (_ bv{} {}) (_ bv0 {}))",
                    smt_boolean(monomial, positions, namespace)?,
                    coefficient,
                    width,
                    width
                ))
            })
            .collect::<Option<Vec<_>>>()?;
        let sum = terms
            .into_iter()
            .fold(format!("(_ bv0 {width})"), |left, right| {
                format!("(bvadd {left} {right})")
            });
        Some(format!("(bvurem {sum} (_ bv{} {}))", denominator, width))
    };
    let assertion = format!("(distinct {} {})", value("x")?, value("z")?);
    Some(smt_script(
        declarations(positions.len(), &["x", "z"]),
        assertion,
        &[],
    ))
}

/// Returns the first SAT model whose phase difference Irene confirms locally.
fn validated_phase_model(
    portfolio: &PortfolioResult,
    phase: &RationalPhase,
    positions: &BTreeMap<Qubit, usize>,
) -> Option<(Vec<bool>, Vec<bool>)> {
    portfolio
        .results
        .iter()
        .filter(|result| result.status == SolverStatus::Sat)
        .find_map(|result| {
            let ket = parse_boolean_values(&result.stdout, positions.len(), "x")?;
            let bra = parse_boolean_values(&result.stdout, positions.len(), "z")?;
            let ket_value = evaluate_phase(phase, &input_bindings(&ket, positions));
            let bra_value = evaluate_phase(phase, &input_bindings(&bra, positions));
            (ket_value != bra_value).then_some((ket, bra))
        })
}

fn evaluate_phase(phase: &RationalPhase, bindings: &BTreeMap<Variable, bool>) -> BigRational {
    modulo_one(
        phase
            .iter()
            .filter(|(selector, _)| evaluate_boolean(selector, bindings))
            .fold(rational_zero(), |sum, (_, coefficient)| sum + coefficient),
    )
}

fn modulo_one(value: BigRational) -> BigRational {
    BigRational::new(
        positive_mod(value.numer().clone(), value.denom()),
        value.denom().clone(),
    )
}

fn positive_mod(value: BigInt, modulus: &BigInt) -> BigInt {
    let remainder = value % modulus;
    if remainder < BigInt::from(0) {
        remainder + modulus
    } else {
        remainder
    }
}

fn lcm(left: BigInt, right: BigInt) -> BigInt {
    let gcd = gcd(left.clone(), right.clone());
    left / gcd * right
}

fn gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    while right != BigInt::from(0) {
        let remainder = left % &right;
        left = right;
        right = remainder;
    }
    left
}

fn bit_width(value: &BigInt) -> u64 {
    value.magnitude().bits().max(1)
}

fn rational_zero() -> BigRational {
    BigRational::from_integer(BigInt::from(0))
}

#[cfg(test)]
mod injectivity_tests {
    use super::*;

    #[test]
    fn optional_model_failure_never_revokes_sat_but_unsat_is_an_error() {
        let observation = |status| {
            let result = SolverResult {
                solver: Solver::Bitwuzla,
                status,
                stdout: String::new(),
                stderr: String::new(),
                duration: std::time::Duration::ZERO,
            };
            PortfolioResult {
                consensus: smt::consensus(std::slice::from_ref(&result)).unwrap(),
                results: vec![result],
            }
        };
        for status in [
            SolverStatus::Unknown,
            SolverStatus::Timeout,
            SolverStatus::Error,
            SolverStatus::Unavailable,
            SolverStatus::Sat,
        ] {
            let combined =
                combine_same_query_results(observation(SolverStatus::Sat), observation(status))
                    .unwrap();
            assert_eq!(combined.consensus, PortfolioConsensus::Sat);
            assert!(
                combined
                    .results
                    .iter()
                    .any(|r| r.status == SolverStatus::Sat)
            );
        }
        assert!(
            combine_same_query_results(
                observation(SolverStatus::Sat),
                observation(SolverStatus::Unsat)
            )
            .is_err()
        );
    }

    fn input(index: usize) -> Qubit {
        Qubit {
            register: SymbolId(0),
            index,
        }
    }

    fn variable(index: usize) -> BooleanPolynomial {
        BooleanPolynomial::variable(Variable::Input(input(index)))
    }

    #[test]
    fn triangular_recovery_accepts_nonlinear_dependencies_and_permutations() {
        let inputs = (0..3).map(|i| (input(i), i)).collect();
        let x = variable(0);
        let y = variable(1);
        let z = variable(2);
        assert!(triangular_injectivity(
            &[z.xor(&x.and(&y)).complement(), y.xor(&x), x],
            &inputs
        ));
        let inputs = (0..4).map(|i| (input(i), i)).collect();
        let [x, y, z, w] = [variable(0), variable(1), variable(2), variable(3)];
        // The first three rows are invertible but have no singleton row.
        assert!(triangular_injectivity(
            &[x.xor(&y), y.xor(&z), x.xor(&y).xor(&z), w.xor(&x.and(&z))],
            &inputs
        ));
    }

    #[test]
    fn triangular_recovery_rejects_self_dependence_and_undeclared_variables() {
        let inputs = (0..2).map(|i| (input(i), i)).collect();
        let x = variable(0);
        let y = variable(1);
        assert!(!triangular_injectivity(
            &[x.xor(&x.and(&y)), y.clone()],
            &inputs
        ));
        assert!(!triangular_injectivity(&[x.clone(), x.clone()], &inputs));
        assert!(!triangular_injectivity(&[x.clone(), variable(2)], &inputs));
        assert!(!triangular_injectivity(
            &[x, BooleanPolynomial::variable(Variable::Path(0))],
            &inputs
        ));
    }

    #[test]
    fn every_two_bit_recovery_certificate_is_injective() {
        let inputs = (0..2).map(|i| (input(i), i)).collect();
        let monomials = [
            BooleanPolynomial::one(),
            variable(0),
            variable(1),
            variable(0).and(&variable(1)),
        ];
        let polynomials = (0..16)
            .map(|mask| {
                monomials
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| mask & (1 << i) != 0)
                    .fold(BooleanPolynomial::zero(), |sum, (_, term)| sum.xor(term))
            })
            .collect::<Vec<_>>();
        for left in &polynomials {
            for right in &polynomials {
                let outputs = [left.clone(), right.clone()];
                if !triangular_injectivity(&outputs, &inputs) {
                    continue;
                }
                let images = (0..4)
                    .map(|bits| {
                        let bindings = (0..2)
                            .map(|i| (Variable::Input(input(i)), bits & (1 << i) != 0))
                            .collect();
                        outputs
                            .iter()
                            .map(|output| evaluate_boolean(output, &bindings))
                            .collect::<Vec<_>>()
                    })
                    .collect::<BTreeSet<_>>();
                assert_eq!(images.len(), 4);
            }
        }
    }
}
