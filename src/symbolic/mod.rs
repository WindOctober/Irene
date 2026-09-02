//! Symbolic execution with the hybrid path-sum representation.
//!
//! A component denotes `guard * scalar * exp(2πi phase)` times its output
//! memory, summed over its path support. Multiple components form the finite
//! sum introduced by classical control flow.

mod boolean;
mod executor;
pub mod optimize;
mod phase;
mod scalar;

pub use boolean::{BooleanPolynomial, Monomial, Variable};
pub use executor::{
    Component, ExecutionConfig, HistoryEntry, HybridMemory, HybridPathSum, InitialState,
    SymbolicError, execute,
};
pub use phase::{PhaseCoefficient, PhasePolynomial};
pub use scalar::{Scalar, ScalarBindings, ScalarEvaluationError};

#[cfg(test)]
mod tests;
