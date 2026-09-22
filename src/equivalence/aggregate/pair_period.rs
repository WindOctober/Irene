//! Exact pair periods of COMPLETE small-bound phases, before product proof.
//! P=A+B*x+C*y+D*x*y with C=B and D=-2B is A+B*(x XOR y).
//! Summing two owned bits with independent guards/scalars thus equals twice
//! the sum with y=0. Other binders and every free coordinate remain intact.

use super::scalar::{integer, normalize_scalar, scalar_within_budget};
use super::small_sum::FreeKey;
use super::{KernelScalar, KernelVariable, MAX_BOOLEAN_TERMS, MAX_PHASE_TERMS, WorkingTerm};
use num_bigint::BigInt;
use std::collections::BTreeMap;

fn charge(work: &mut usize, cells: usize) -> Option<()> {
    *work = work.checked_sub(cells)?;
    Some(())
}
use crate::symbolic::PhaseCoefficient;

const SOURCE_CELLS: usize = 100_000;

// Total bounded real grammar; inspect BOTH branches, including inactive ones.
fn scalar_cells(scalar: &KernelScalar, cells: &mut usize) -> Option<()> {
    charge(cells, 1)?;
    match scalar {
        KernelScalar::Rational(r) => {
            if r.numer().bits() > 4096 || r.denom().bits() > 4096 {
                return None;
            }
        }
        KernelScalar::Neg(a) => scalar_cells(a, cells)?,
        KernelScalar::Add(a, b) | KernelScalar::Mul(a, b) => {
            scalar_cells(a, cells)?;
            scalar_cells(b, cells)?;
        }
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => {
            if !condition.is_algebraic() {
                return None;
            }
            for m in condition.terms() {
                charge(cells, 1 + m.variables().count())?;
                if m.variables().any(KernelVariable::is_bound_path) {
                    return None;
                }
            }
            scalar_cells(when_true, cells)?;
            scalar_cells(when_false, cells)?;
        }
        _ => return None,
    }
    Some(())
}

/// One bounded sweep: at most three pair candidates and ONE accepted period.
/// Refusal, including work exhaustion after grouping, never mutates source.
pub(super) fn compact(source: &mut WorkingTerm, work: &mut usize) -> Option<bool> {
    compact_bounded::<8>(source, work)
}

/// Separate four-binder entrance; the two-/three-binder entry stays bounded
/// to its eight-mask representation.
pub(super) fn compact_four(source: &mut WorkingTerm, work: &mut usize) -> Option<bool> {
    if source.paths.len() != 4 {
        return Some(false);
    }
    compact_bounded::<16>(source, work)
}

fn compact_bounded<const MASKS: usize>(source: &mut WorkingTerm, work: &mut usize) -> Option<bool> {
    if !(2..=MASKS.ilog2() as usize).contains(&source.paths.len())
        || source.constraints.len() > 64
        || !source.paths.iter().all(KernelVariable::is_bound_path)
        || !source.phase.is_algebraic()
        || source.phase.term_count() > MAX_PHASE_TERMS
        || !source
            .constraints
            .iter()
            .all(|row| row.is_algebraic() && row.term_count() <= MAX_BOOLEAN_TERMS)
        || !scalar_within_budget(&source.coefficient)
    {
        return Some(false);
    }
    let mut scalar_left = 256;
    scalar_cells(&source.coefficient, &mut scalar_left)?;
    let scalar_size = 256 - scalar_left;
    let mut source_cells = source.paths.len() + scalar_size;
    charge(work, source_cells)?;
    for row in &source.constraints {
        for m in row.terms() {
            let n = 1 + m.variables().count();
            source_cells = source_cells.checked_add(n)?;
            if source_cells > SOURCE_CELLS || m.variables().any(KernelVariable::is_bound_path) {
                return None;
            }
            charge(work, n)?;
        }
    }
    let paths = source.paths.iter().collect::<Vec<_>>();
    let mut groups = BTreeMap::<FreeKey<'_>, [Option<&PhaseCoefficient>; MASKS]>::new();
    let mut phase_cells = 0;
    for (m, c) in source.phase.terms() {
        let n = 1 + m.variables().count();
        source_cells = source_cells.checked_add(n)?;
        if source_cells > SOURCE_CELLS {
            return None;
        }
        phase_cells += n;
        // One complete source scan, one borrowed key and MASKS coefficient
        // reference slots only when a new projected group is inserted.
        charge(work, n)?;
        let r = c.as_rational()?;
        if r.numer().bits() > 256 || r.denom().bits() > 256 {
            return None;
        }
        let mut mask = 0;
        for v in m.variables().filter(|v| v.is_bound_path()) {
            mask |= 1 << paths.iter().position(|p| *p == v)?;
        }
        let entry = match groups.entry(FreeKey(m)) {
            std::collections::btree_map::Entry::Occupied(e) => e.into_mut(),
            std::collections::btree_map::Entry::Vacant(e) => {
                charge(work, MASKS + 1)?;
                e.insert([None; MASKS])
            }
        };
        if entry[mask].replace(c).is_some() {
            return None;
        }
    }
    let zero = PhaseCoefficient::default();
    let mut accepted = None;
    'pairs: for x in 0..paths.len() {
        for y in x + 1..paths.len() {
            let xb = 1 << x;
            let yb = 1 << y;
            let mut valid = true;
            for pattern in groups.values() {
                // Check ALL coefficients on other bound coordinates too.
                for rest in (0..1usize << paths.len()).filter(|m| m & (xb | yb) == 0) {
                    charge(work, 4)?;
                    let b = pattern[rest | xb].unwrap_or(&zero);
                    let c = pattern[rest | yb].unwrap_or(&zero);
                    let d = pattern[rest | xb | yb].unwrap_or(&zero);
                    if b != c || &b.scaled(BigInt::from(-2)) != d {
                        valid = false;
                        break;
                    }
                }
                if !valid {
                    break;
                }
            }
            if valid {
                accepted = Some(paths[y].clone());
                break 'pairs;
            }
        }
    }
    let Some(y) = accepted else {
        return Some(false);
    };
    // Reserve deletion scan and bounded complete scalar reconstruction BEFORE
    // mutation. Dropping the old index and erased keys constructs no syntax.
    charge(work, phase_cells + 3 * scalar_size + 3)?;
    drop(groups);
    let old = source.phase.term_count();
    source.phase.restrict_zero(&y);
    source.paths.remove(&y);
    source.coefficient =
        normalize_scalar(KernelScalar::Rational(integer(2)).multiply(source.coefficient.clone()));
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate pair-period restricted: terms={old}->{} paths={} work={work}",
            source.phase.term_count(),
            source.paths.len()
        );
    }
    Some(true)
}

#[cfg(test)]
mod tests;
