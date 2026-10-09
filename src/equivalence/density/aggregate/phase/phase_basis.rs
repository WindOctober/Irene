//! Connect phase rewrite scheduling to complete local reduction and EQ proofs.
use crate::equivalence::density::aggregate::*;

mod checkpoint_components;
const WORK_CELLS: usize = super::phase_schedule::WORK_CELLS;

pub(in crate::equivalence::density::aggregate) fn matches_checkpoints(
    left: &Reduction,
    right: &Reduction,
    left_checkpoint: Option<&WorkingTerm>,
    right_checkpoint: Option<&WorkingTerm>,
) -> bool {
    fn source(reduction: &Reduction) -> super::checkpoint::Source<'_> {
        match reduction {
            Reduction::Sum(term) => super::checkpoint::Source::Sum(term),
            Reduction::Residual => super::checkpoint::Source::Refused,
            _ => super::checkpoint::Source::Finished,
        }
    }
    super::checkpoint::matches(
        source(left),
        source(right),
        left_checkpoint,
        right_checkpoint,
        |left, right| {
            matches(
                &Reduction::Sum(Box::new(left)),
                &Reduction::Sum(Box::new(right)),
            )
        },
        checkpoint_components::matches,
    )
}

pub(in crate::equivalence::density::aggregate) fn matches(
    left: &Reduction,
    right: &Reduction,
) -> bool {
    let (Reduction::Sum(left), Reduction::Sum(right)) = (left, right) else {
        return false;
    };

    super::phase_schedule::matches(left, right, prove_terms, factored::matches_components)
}

fn prove_terms(left: WorkingTerm, right: WorkingTerm, work: &mut usize) -> bool {
    debug_term("phase-basis-left", &left);
    debug_term("phase-basis-right", &right);
    let left = reduce_working_term(left);
    let right = reduce_working_term(right);
    if factored::matches(&left, &right) {
        return true;
    }
    if matches_reduced_components(&left, &right, work) {
        return true;
    }
    let mut budget = ReductionBudget {
        splits: MAX_RESIDUAL_SPLITS,
        products: MAX_FACTOR_PRODUCTS,
        phase_cells: MAX_FACTOR_PHASE_CELLS,
    };
    let mut aggregate = |reduction| {
        let mut sum = ExactAggregate::new();
        accumulate_reduction(reduction, &mut sum, &mut 0, &mut budget, 0)?;
        sum.retain(|_, coefficient| !coefficient.is_empty());
        Some(sum)
    };
    let Some(left) = aggregate(left) else {
        return false;
    };
    let Some(right) = aggregate(right) else {
        return false;
    };
    let mut free = MAX_FREE_SPLITS;
    aggregate_difference(left, right).is_some_and(|d| zero_by_free_splitting(d, &mut free, 0))
}

fn matches_reduced_components(left: &Reduction, right: &Reduction, work: &mut usize) -> bool {
    let (Reduction::Sum(left), Reduction::Sum(right)) = (left, right) else {
        return false;
    };

    super::phase_schedule::matches_reduced_components(
        left,
        right,
        work,
        factored::matches_components_refined,
    )
}
