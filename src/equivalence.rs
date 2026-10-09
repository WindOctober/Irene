//! Equivalence checking in three proof stages: unitary trace, HPS, density kernel.
//! A failed shortcut is inconclusive; only a complete certificate decides EQ/NEQ.

use crate::ir::{Program, Qubit};

mod density;
mod hps;
mod interface;
mod result;
mod solver;
mod tuning;
mod unitary;

pub use density::kernel::{DensityKernel, KernelBuildError};
pub use interface::{
    Endpoint, EquivalenceConfig, InputPair, InterfaceError, NumericInputPair, OutputPair,
    PreparedComparison, PreparedOutput, PreparedOutputKind, PreparedSide, PreparedTerminal, Side,
    UnsupportedInterface, prepare_comparison,
};
pub use result::{
    Analysis, Counterexample, DensityCounterexample, DensityExactFactor, Evidence, Verdict,
};
pub use solver::{
    PortfolioConsensus, PortfolioResult, SOLVER_TIMEOUT, Solver, SolverDisagreement, SolverResult,
    SolverStatus,
};
// Preserve the public module paths used by the CLI, worker and Rust consumers.
pub use unitary::{
    dependency as dependency_miter, interval as interval_hps, miter as unitary_miter,
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

/// Compare two programs under an explicit paired interface.
/// Errors describe malformed/executable interfaces; incomplete proofs yield Unknown.
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
    unitary::rewrite::strategy().map_err(InterfaceError::InvalidConfiguration)?;
    // Exact operator rewrites also apply to a unitary side of a channel comparison.
    let rewritten_left = unitary::rewrite::preprocess(left);
    let rewritten_right = unitary::rewrite::preprocess(right);
    let left = rewritten_left.as_ref().unwrap_or(left);
    let right = rewritten_right.as_ref().unwrap_or(right);
    if let Some(analysis) = unitary::compare(left, right, config) {
        return Ok(analysis);
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
    if let Some(analysis) = hps::compare(&prepared)? {
        return Ok(analysis);
    }
    density::compare(&prepared)
}
