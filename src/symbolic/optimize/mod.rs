//! Semantics-preserving simplifications for symbolic HPS states.

mod feedback;
mod guard_rows;
mod local_history;
mod merge;

#[cfg(test)]
pub(crate) use merge::tests::assert_density;
mod path_sum;
mod simplify;
pub(crate) mod slice;

pub(crate) use feedback::merge_feedback_groups;
pub(crate) use local_history::{collapse_local_history, local_history_has_work};
pub(crate) use merge::{merge_coherent_components, merge_components};
pub(crate) use path_sum::reduce_path_sums;
pub(crate) use simplify::simplify;
pub(crate) use simplify::simplify_component;
pub(crate) use simplify::substitute_component;
pub use slice::OutputSelection;

#[cfg(test)]
mod tests;
