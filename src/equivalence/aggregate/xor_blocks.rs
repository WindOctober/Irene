//! Exact sharing of bound-mask coefficient polynomials across free monomials.
//! All masks in a component undergo the SAME reversible basis changes. Equal
//! coefficient maps are shared by exact ordered comparison, never by hashes.

use super::xor_basis::admitted;
use super::{KernelMonomial, KernelPhasePolynomial, WorkingTerm};
use num_bigint::BigInt;
use std::collections::BTreeMap;

const MAX_LOCAL_TERMS: usize = 8192;
fn charge(work: &mut usize, cells: usize) -> Option<()> {
    *work = work.checked_sub(cells)?;
    Some(())
}
use crate::symbolic::PhaseCoefficient;

// Sparse support remains capped at 256 entries, independently of the mask's
// sixteen-bit coordinate namespace. No 2^16 assignment table is constructed.
type MaskPhase = BTreeMap<u16, PhaseCoefficient>;

struct Block {
    free: Vec<KernelMonomial>,
    free_cells: usize,
    phase: MaskPhase,
}

fn insert(phase: &mut MaskPhase, mask: u16, coefficient: PhaseCoefficient) {
    let entry = phase.entry(mask).or_default();
    entry.add_assign(coefficient);
    if entry.is_zero() {
        phase.remove(&mask);
    }
}

fn insert_bounded(phase: &mut MaskPhase, mask: u16, coefficient: PhaseCoefficient) -> Option<()> {
    // Do not transiently allocate a 257th key even for a zero delta.
    if coefficient.is_zero() {
        return Some(());
    }
    if !phase.contains_key(&mask) && phase.len() >= 256 {
        return None;
    }
    insert(phase, mask, coefficient);
    Some(())
}

fn cost(phase: &MaskPhase, block: &Block) -> (usize, usize) {
    (
        phase.len() * block.free.len(),
        phase.len() * block.free_cells
            + block.free.len() * phase.keys().map(|m| m.count_ones() as usize).sum::<usize>(),
    )
}

/// Sparse mask delta, with exactly the same block identity as the original
/// full-monomial transvection. Every changed key is checked against the entire
/// source, including keys without x. All block deltas must finish before commit.
fn delta(source: &MaskPhase, x: u16, y: u16, work: &mut usize) -> Option<MaskPhase> {
    if source.len() > 256 {
        return None;
    }
    let mut result = MaskPhase::new();
    for (&mask, coefficient) in source {
        charge(work, 1)?;
        if mask & x == 0 {
            continue;
        }
        if mask & y != 0 && source.contains_key(&(mask & !y)) {
            continue;
        }
        charge(work, 6 * (1 + mask.count_ones() as usize))?;
        let mut total = coefficient.clone();
        let other = if mask & y == 0 {
            source.get(&(mask | y)).cloned().unwrap_or_default()
        } else {
            PhaseCoefficient::default()
        };
        let value = other.as_rational()?;
        if value.numer().bits() > 256 || value.denom().bits() > 256 {
            return None;
        }
        if mask & y == 0 {
            total.add_assign(other);
        }
        for c in [coefficient, &total] {
            let v = c.as_rational()?;
            if v.numer().bits() > 256 || v.denom().bits() > 256 {
                return None;
            }
        }
        insert_bounded(&mut result, (mask & !x) | y, total.clone())?;
        insert_bounded(&mut result, mask | y, total.scaled(BigInt::from(-2)))?;
    }
    Some(result)
}

fn delta_cost(source: &MaskPhase, delta: &MaskPhase, block: &Block) -> Option<(usize, usize)> {
    let mut result = cost(source, block);
    let mut entries = source.len();
    for (&mask, coefficient) in delta {
        let before = source.get(&mask).cloned().unwrap_or_default();
        let value = before.as_rational()?;
        if value.numer().bits() > 256 || value.denom().bits() > 256 {
            return None;
        }
        let mut after = before.clone();
        after.add_assign(coefficient.clone());
        let cells = block.free_cells + block.free.len() * mask.count_ones() as usize;
        if !before.is_zero() {
            entries -= 1;
            result.0 -= block.free.len();
            result.1 -= cells;
        }
        if !after.is_zero() {
            entries += 1;
            result.0 += block.free.len();
            result.1 += cells;
        }
    }
    (entries <= 256).then_some(result)
}

pub(super) fn compact(factor: &mut WorkingTerm, work: &mut usize) -> Option<bool> {
    if !admitted(factor)
        || factor.paths.len() < 2
        || factor.paths.len() > 16
        || factor.phase.term_count() > MAX_LOCAL_TERMS
        || factor.paths.iter().any(|v| factor.occurs_outside_phase(v))
    {
        return Some(false);
    }
    let mut input_cells = 0usize;
    for (m, _) in factor.phase.terms() {
        input_cells = input_cells.checked_add(1 + m.variables().count())?;
        if input_cells > 32768 {
            return Some(false);
        }
    }
    // Reserve the complete final reconstruction before spending proposal work.
    // Every accepted move is non-growing, so this bound remains sufficient.
    // One monomial construction and one native insertion, without an occurrence
    // index or growing-prefix union copies. Reserve two original-cell passes.
    charge(work, input_cells.checked_mul(2)?)?;
    let paths = factor.paths.iter().cloned().collect::<Vec<_>>();
    let mut by_free = BTreeMap::<KernelMonomial, MaskPhase>::new();
    for (m, coefficient) in factor.phase.terms() {
        let value = coefficient.as_rational()?;
        if value.numer().bits() > 256 || value.denom().bits() > 256 {
            return Some(false);
        }
        charge(work, 2 * (1 + m.variables().count()))?;
        let mut mask = 0u16;
        let free = KernelMonomial::from_variables(m.variables().filter_map(|v| {
            if let Ok(i) = paths.binary_search(v) {
                mask |= 1 << i;
                None
            } else {
                Some(v.clone())
            }
        }));
        // The split is unique: no two original monomials have the same pair.
        let pattern = by_free.entry(free).or_default();
        if pattern.len() >= 256 {
            return Some(false);
        }
        pattern.insert(mask, coefficient.clone());
    }
    let mut shared = BTreeMap::<MaskPhase, Vec<KernelMonomial>>::new();
    for (free, phase) in by_free {
        charge(work, 1 + free.variables().count() + phase.len())?;
        shared.entry(phase).or_default().push(free);
    }
    let mut blocks = shared
        .into_iter()
        .map(|(phase, free)| Block {
            free_cells: free.iter().map(|m| 1 + m.variables().count()).sum(),
            free,
            phase,
        })
        .collect::<Vec<_>>();
    let original = blocks
        .iter()
        .map(|b| cost(&b.phase, b))
        .fold((0, 0), |a, b| (a.0 + b.0, a.1 + b.1));
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate shared-block geometry: patterns={} distinct_masks={} original_terms={} work={work}",
            blocks.len(),
            blocks.iter().map(|b| b.phase.len()).sum::<usize>(),
            original.0
        );
    }
    let mut current = original;
    let mut changed = false;
    'rounds: for _ in 0..8 {
        let mut pairs = BTreeMap::<(usize, usize), usize>::new();
        for block in &blocks {
            for &mask in block.phase.keys() {
                let active = (0..paths.len())
                    .filter(|i| mask & (1 << i) != 0)
                    .collect::<Vec<_>>();
                if charge(work, 1 + paths.len() + active.len() * active.len()).is_none() {
                    break 'rounds;
                }
                for &x in &active {
                    for &y in &active {
                        if x != y {
                            *pairs.entry((x, y)).or_default() += block.free.len();
                        }
                    }
                }
            }
        }
        let mut pairs = pairs.into_iter().collect::<Vec<_>>();
        pairs.sort_by_key(|(pair, count)| (std::cmp::Reverse(*count), *pair));
        let mut step = false;
        for ((x, y), _) in pairs.into_iter().take(8) {
            let mut proposed = Vec::new();
            let mut next = (0usize, 0usize);
            for block in &blocks {
                let Some(phase) = delta(&block.phase, 1 << x, 1 << y, work) else {
                    break 'rounds;
                };
                let Some(c) = delta_cost(&block.phase, &phase, block) else {
                    break 'rounds;
                };
                next.0 += c.0;
                next.1 += c.1;
                proposed.push(phase);
            }
            if next.0 <= current.0 && next.1 < current.1 {
                for (block, phase) in blocks.iter_mut().zip(proposed) {
                    if paths.len() <= 8 {
                        for (mask, coefficient) in phase {
                            insert(&mut block.phase, mask, coefficient);
                        }
                    } else {
                        // Cancel before adding keys so even a wide namespace
                        // cannot transiently grow the mask map beyond 256.
                        let mut updates = Vec::new();
                        for (mask, coefficient) in phase {
                            let mut after = block.phase.get(&mask).cloned().unwrap_or_default();
                            after.add_assign(coefficient);
                            if after.is_zero() {
                                block.phase.remove(&mask);
                            } else {
                                updates.push((mask, after));
                            }
                        }
                        for (mask, coefficient) in updates {
                            block.phase.insert(mask, coefficient);
                        }
                    }
                }
                current = next;
                changed = true;
                step = true;
                break;
            }
        }
        if !step {
            break;
        }
    }
    if !changed {
        return Some(false);
    }
    // Build every free block, including unchanged ones and the constant mask.
    // No collision can join different free monomials; masks are also unique.
    let mut result = KernelPhasePolynomial::default();
    for block in blocks {
        for free in block.free {
            for (&mask, coefficient) in &block.phase {
                let monomial = KernelMonomial::from_variables(
                    free.variables().cloned().chain(
                        paths
                            .iter()
                            .enumerate()
                            .filter(|(i, _)| mask & (1 << i) != 0)
                            .map(|(_, v)| v.clone()),
                    ),
                );
                result.add_term(monomial, coefficient.clone());
            }
        }
    }
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate shared-block move: terms={}->{} cells={}->{} work={work}",
            original.0, current.0, original.1, current.1
        );
    }
    factor.phase = result;
    Some(true)
}

#[cfg(test)]
#[path = "../../../tests/unit/equivalence/aggregate/xor_blocks/tests.rs"]
mod tests;
