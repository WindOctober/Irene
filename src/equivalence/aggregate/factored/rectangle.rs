//! Adapter to the exact four-atom certificate using the shared proof budget.
use super::{ExactAggregate, ReductionBudget};

pub(super) fn factor(
    source: &mut Option<ExactAggregate>,
    budget: &mut ReductionBudget,
) -> Option<Vec<ExactAggregate>> {
    super::super::factor_rectangle::factor(source, &mut budget.phase_cells)
}
