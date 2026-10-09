//! Public verdicts and proof evidence, independent of backend organization.
use super::{KernelBuildError, PortfolioResult, UnsupportedInterface};
use num_rational::BigRational;
use std::fmt;

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
    pub(super) fn new(verdict: Verdict, evidence: Evidence, kernel_terms: (usize, usize)) -> Self {
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
