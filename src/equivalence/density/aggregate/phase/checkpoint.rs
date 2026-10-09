//! Reuse complete reduction checkpoints without treating refusal as a value.

use crate::equivalence::density::aggregate::{WorkingTerm, vacuous};

/// The ordinary reduction outcome, without recovering a term from a refusal.
pub(in crate::equivalence::density::aggregate) enum Source<'a> {
    Sum(&'a WorkingTerm),
    Refused,
    Finished,
}

/// Capture only at a transactional boundary: `term` must represent the entire
/// original summand after complete, exact local rewrites. Admission checks
/// size and ownership, not equivalence; a partial aggregate is never eligible.
pub(in crate::equivalence::density::aggregate) fn capture(
    term: WorkingTerm,
) -> Option<WorkingTerm> {
    vacuous::admitted(&term).then_some(term)
}

fn source<'a>(outcome: Source<'a>, checkpoint: Option<&'a WorkingTerm>) -> Option<&'a WorkingTerm> {
    match outcome {
        Source::Sum(term) => Some(term),
        Source::Refused => checkpoint,
        Source::Finished => None,
    }
}

/// Proof callbacks must certify equality of BOTH COMPLETE terms. `false`
/// means inconclusive, never NEQ. No checkpoint or compaction alone proves EQ.
pub(in crate::equivalence::density::aggregate) fn matches(
    left: Source<'_>,
    right: Source<'_>,
    left_checkpoint: Option<&WorkingTerm>,
    right_checkpoint: Option<&WorkingTerm>,
    prove_compacted: impl FnOnce(WorkingTerm, WorkingTerm) -> bool,
    prove_components: impl FnOnce(&WorkingTerm, &WorkingTerm) -> bool,
) -> bool {
    if left_checkpoint.is_none() && right_checkpoint.is_none() {
        return false;
    }
    let (Some(left), Some(right)) = (
        source(left, left_checkpoint),
        source(right, right_checkpoint),
    ) else {
        return false;
    };
    if !vacuous::admitted(left) || !vacuous::admitted(right) {
        return false;
    }
    match (vacuous::remove(left), vacuous::remove(right)) {
        (Some(left), Some(right)) => prove_compacted(left, right),
        // Do not pass one compacted side or a partially accumulated sum.
        _ => prove_components(left, right),
    }
}
