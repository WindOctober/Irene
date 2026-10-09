//! Adapter for complete small-bound sums using the shared proof budgets.
use super::*;

pub(super) fn admitted(source: &WorkingTerm) -> bool {
    super::super::small_sum::admitted(source)
}
pub(super) fn sum(source: &WorkingTerm, budget: &mut ReductionBudget) -> Option<ExactAggregate> {
    super::super::small_sum::sum(source, &mut budget.splits, &mut budget.phase_cells)
}
