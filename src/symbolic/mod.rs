//! Symbolic execution with the hybrid path-sum representation.
//!
//! A component denotes `guard * scalar * exp(2πi phase)` times its output
//! memory, summed over its path support. Multiple components form the finite
//! sum introduced by classical control flow.

mod boolean;
mod executor;
mod optimize;
mod phase;
mod scalar;
mod validate;

pub(crate) use boolean::Expression as BooleanExpression;
pub use boolean::{BooleanPolynomial, Monomial, Variable};
pub use executor::{
    Component, ExecutionConfig, HistoryEntry, HybridMemory, HybridPathSum, InitialState,
    SymbolicError, execute,
};
pub use optimize::OutputSelection;
pub use phase::{PhaseCoefficient, PhasePolynomial};
pub use scalar::{Scalar, ScalarBindings, ScalarEvaluationError};
pub(crate) use validate::numeric_domains;

#[cfg(test)]
mod tests;
