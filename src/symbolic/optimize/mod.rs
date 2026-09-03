//! Semantics-preserving simplifications for symbolic HPS states.

mod merge;
mod simplify;
pub(crate) mod slice;

pub(crate) use merge::merge_components;
pub(crate) use simplify::simplify;
pub(crate) use simplify::simplify_component;
pub use slice::OutputSelection;

#[cfg(test)]
mod tests;
