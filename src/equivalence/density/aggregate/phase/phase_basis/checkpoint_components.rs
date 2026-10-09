//! Connect complete checkpoint factors to the existing local reducer and proof.
use super::*;
use crate::equivalence::density::aggregate::phase::checkpoint_factors::{Components, components};

pub(super) fn matches(left: &WorkingTerm, right: &WorkingTerm) -> bool {
    let mut work = WORK_CELLS;
    let result = (|| {
        let left = components(left, &mut work)?;
        let right = components(right, &mut work)?;
        let left = reduce_components(left, &mut work)?;
        let right = reduce_components(right, &mut work)?;
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "aggregate checkpoint components complete: left={} right={} work={work}",
                left.len(),
                right.len()
            );
        }
        Some(factored::matches_components_refined(left, right, true))
    })();
    if result != Some(true) && std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!("aggregate checkpoint components proof refused: work={work}");
    }
    result == Some(true)
}

fn reduce_components(factors: Components, work: &mut usize) -> Option<Vec<WorkingTerm>> {
    crate::equivalence::density::aggregate::phase::checkpoint_factors::reduce_components(
        factors,
        work,
        |factor| {
            match reduce_working_term(factor) {
                Reduction::Sum(term) => Some(*term),
                Reduction::Exact(term) => Some(WorkingTerm {
                    paths: BTreeSet::new(),
                    constraints: term.constraints,
                    coefficient: term.coefficient,
                    phase: term.phase,
                }),
                // TODO(completeness): `Zero` is a proven-zero certificate, not a
                // refusal. One zero component makes the whole product zero, which
                // is EQ evidence when the other side is also zero; folding it into
                // `Residual`'s `None` discards that evidence and degrades the
                // verdict to Unknown. `product_form::build` refuses the same way
                // (empty aggregate rejected by `factor_normalize::normalize`), so
                // both should short-circuit to the zero product `product_cases::
                // restrict` already uses. Guard: only two provably-zero sides may
                // yield EQ; a single zero side must never become NEQ here.
                Reduction::Zero | Reduction::Residual => None,
            }
        },
    )
}
