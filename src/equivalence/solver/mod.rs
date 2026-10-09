//! Shared solver execution and portfolio policy. Encoders stay with their proof stages.
pub(in crate::equivalence) mod query;
pub(in crate::equivalence) mod smt;

pub use smt::{
    PortfolioConsensus, PortfolioResult, SOLVER_TIMEOUT, Solver, SolverDisagreement, SolverResult,
    SolverStatus,
};
