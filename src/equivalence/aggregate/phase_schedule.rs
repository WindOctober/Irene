//! Schedule exact phase-coordinate rewrites, then require a complete equality proof.
//! Work is shared by both sides within each attempt; the three alternative
//! attempts retain separate fixed allowances. Smaller syntax alone is not EQ.
use super::{
    KernelPhasePolynomial, WorkingTerm, factorization, pair_period, xor_basis, xor_blocks,
};

const INPUT_CELLS: usize = 750_000;
pub(super) const WORK_CELLS: usize = 1_000_000;
const MAX_LOCAL_TERMS: usize = 8192;

#[derive(Clone, Copy)]
pub(super) enum Strategy {
    Single,
    Blocks8,
    Blocks16,
}

/// Both callbacks certify equality of complete operands, not partial sums.
/// False is inconclusive. Neither callback may infer NEQ from unequal syntax.
pub(super) fn matches(
    left: &WorkingTerm,
    right: &WorkingTerm,
    mut prove_terms: impl FnMut(WorkingTerm, WorkingTerm, &mut usize) -> bool,
    mut prove_factors: impl FnMut(Vec<WorkingTerm>, Vec<WorkingTerm>) -> bool,
) -> bool {
    [Strategy::Single, Strategy::Blocks8, Strategy::Blocks16]
        .into_iter()
        .any(|strategy| try_strategy(left, right, strategy, &mut prove_terms, &mut prove_factors))
}

pub(super) fn try_strategy(
    left: &WorkingTerm,
    right: &WorkingTerm,
    strategy: Strategy,
    prove_terms: &mut impl FnMut(WorkingTerm, WorkingTerm, &mut usize) -> bool,
    prove_factors: &mut impl FnMut(Vec<WorkingTerm>, Vec<WorkingTerm>) -> bool,
) -> bool {
    let (shared_blocks, block_paths) = match strategy {
        Strategy::Single => (false, 8),
        Strategy::Blocks8 => (true, 8),
        Strategy::Blocks16 => (true, 16),
    };
    if !xor_basis::admitted(left) || !xor_basis::admitted(right) {
        return false;
    }
    let mut work = WORK_CELLS;
    if shared_blocks {
        let (source_left, source_right) = (left, right);
        let Some((left, l_changed, l_wide)) = compact_block_factors(left, &mut work, block_paths)
        else {
            return false;
        };
        let Some((right, r_changed, r_wide)) = compact_block_factors(right, &mut work, block_paths)
        else {
            return false;
        };
        if !(l_changed || r_changed) || (block_paths > 8 && !(l_wide || r_wide)) {
            return false;
        }
        // Keep the proven monolithic normal-form route first. If it refuses,
        // reuse the already-complete components without rerunning compaction.
        let reconstruct = |source: &WorkingTerm, factors: &[WorkingTerm]| {
            let mut result = source.clone();
            result.phase = KernelPhasePolynomial::default();
            for factor in factors {
                for (m, c) in factor.phase.terms() {
                    result.phase.add_term(m.clone(), c.clone());
                }
            }
            result
        };
        return prove_terms(
            reconstruct(source_left, &left),
            reconstruct(source_right, &right),
            &mut work,
        ) || prove_factors(left, right);
    }
    let Some((left, l_changed)) = xor_basis::compact(left, &mut work) else {
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!("aggregate phase-basis refused: left work={work}");
        }
        return false;
    };
    let Some((right, r_changed)) = xor_basis::compact(right, &mut work) else {
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!("aggregate phase-basis refused: right work={work}");
        }
        return false;
    };
    if !(l_changed || r_changed) {
        return false;
    }
    prove_terms(left, right, &mut work)
}

/// Reuse the WHOLE completed local reductions. The monolithic product's
/// entrance may refuse their combined syntax even when the newly separated
/// components meet its unchanged small-factor bounds. Never recover a
/// Residual, rerun compaction, or omit the new common coefficient/guards/phase.
pub(super) fn matches_reduced_components(
    left: &WorkingTerm,
    right: &WorkingTerm,
    work: &mut usize,
    prove: impl FnOnce(Vec<WorkingTerm>, Vec<WorkingTerm>, bool) -> bool,
) -> bool {
    if !xor_basis::admitted(left) || !xor_basis::admitted(right) {
        return false;
    }
    let (Some(mut left), Some(mut right)) = (
        factorization::factor(left, INPUT_CELLS),
        factorization::factor(right, INPUT_CELLS),
    ) else {
        return false;
    };
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!("aggregate reusing complete reduced components");
    }
    // Use remaining compaction work, never a fresh sum/proof allowance.
    // Only oversized small-bound components need this representation change;
    // every complete unchanged factor survives any read-only refusal.
    let mut period_changed = false;
    for factor in left.iter_mut().chain(&mut right) {
        if (2..=3).contains(&factor.paths.len())
            && factor
                .phase
                .terms()
                .map(|(m, _)| 1 + m.variables().count())
                .sum::<usize>()
                > 32768
        {
            period_changed |= pair_period::compact(factor, work).is_some_and(|changed| changed);
        }
    }
    prove(left, right, period_changed)
}

fn compact_block_factors(
    source: &WorkingTerm,
    work: &mut usize,
    block_paths: usize,
) -> Option<(Vec<WorkingTerm>, bool, bool)> {
    let mut factors = factorization::factor(source, INPUT_CELLS)?;
    // The common coefficient/guard remains first for the consuming proof.
    factors[1..].sort_by_key(|f| {
        // Only the wide alternative prioritizes components that cannot yet
        // enter the final eight-binder proof. Original successful scheduling
        // remains unchanged; every factor, including skipped ones, remains.
        let obstructing = block_paths > 8
            && (9..=block_paths).contains(&f.paths.len())
            && f.constraints.is_empty();
        (
            std::cmp::Reverse(obstructing),
            std::cmp::Reverse(f.phase.term_count()),
        )
    });
    let mut changed = false;
    let mut wide_changed = false;
    for factor in &mut factors {
        // In the wide fallback reserve existing work for complete post-local
        // period checks. Both earlier successful eight-bit schedules remain.
        if block_paths > 8 && factor.paths.len() <= 8 && *work < 250_000 {
            continue;
        }
        if factor.paths.len() < 2
            || factor.paths.len() > block_paths
            || factor.phase.term_count() > MAX_LOCAL_TERMS
            || factor.paths.iter().any(|v| factor.occurs_outside_phase(v))
        {
            continue;
        }
        match xor_blocks::compact(factor, work) {
            Some(true) => {
                changed = true;
                wide_changed |= factor.paths.len() > 8;
            }
            Some(false) => {}
            None => break,
        }
    }
    Some((factors, changed, wide_changed))
}
