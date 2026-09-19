//! Semantics-preserving simplifications for symbolic HPS states.

mod guard_rows;
mod merge;
mod path_sum;
mod simplify;
pub(crate) mod slice;

pub(crate) use merge::{merge_coherent_components, merge_components};
pub(crate) use path_sum::reduce_path_sums;
pub(crate) use simplify::simplify;
pub(crate) use simplify::simplify_component;
pub use slice::OutputSelection;

#[cfg(test)]
mod tests;
