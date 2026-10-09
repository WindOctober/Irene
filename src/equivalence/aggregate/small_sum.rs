//! Complete small-bound sums with borrowed free keys and shared coefficient maps.
//!
//! P(u,v) = sum_f f(u) P_f(v). For each of ALL 2^k assignments a, its
//! coefficient at f is sum_{mask subset a} P_f[mask]. Equal complete maps
//! share this calculation; free monomials are never identified or summed.

use super::collection::{ExactAggregate, ExactTerm, accumulate_exact_term};
use super::scalar::{integer, normalize_scalar, ratio, scalar_within_budget};
use super::{
    KernelMonomial, KernelPhasePolynomial, KernelScalar, KernelVariable, MAX_BOOLEAN_TERMS,
    MAX_PHASE_TERMS, WorkingTerm,
};
use std::collections::{BTreeMap, BTreeSet};

// Borrowed projection onto the complete ordered free-variable sequence.
#[derive(Clone, Copy)]
pub(super) struct FreeKey<'a>(pub(super) &'a KernelMonomial);

impl<'a> FreeKey<'a> {
    pub(super) fn variables(&self) -> impl Iterator<Item = &'a KernelVariable> {
        self.0.variables().filter(|v| !v.is_bound_path())
    }
}

impl PartialEq for FreeKey<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for FreeKey<'_> {}
impl PartialOrd for FreeKey<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for FreeKey<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.variables().cmp(other.variables())
    }
}

use crate::symbolic::PhaseCoefficient;

const MAX_SOURCE_CELLS: usize = 100_000;
const MAX_PATHS: usize = 3;

fn charge(cells: &mut usize, amount: usize) -> Option<()> {
    *cells = cells.checked_sub(amount)?;
    Some(())
}

// A deliberately small, total real scalar grammar. No new inverse/root or
// numeric-expression domain assumptions are introduced by this entrance.
fn scalar_cells(scalar: &KernelScalar, left: &mut usize) -> Option<usize> {
    *left = left.checked_sub(1)?;
    let mut cells = 1;
    match scalar {
        KernelScalar::Rational(r) => {
            if r.numer().bits() > 4096 || r.denom().bits() > 4096 {
                return None;
            }
        }
        KernelScalar::Neg(a) => cells += scalar_cells(a, left)?,
        KernelScalar::Add(a, b) | KernelScalar::Mul(a, b) => {
            cells += scalar_cells(a, left)? + scalar_cells(b, left)?;
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
                let n = 1 + m.variables().count();
                *left = left.checked_sub(n)?;
                if m.variables().any(KernelVariable::is_bound_path) {
                    return None;
                }
                cells += n;
            }
            cells += scalar_cells(when_true, left)? + scalar_cells(when_false, left)?;
        }
        _ => return None,
    }
    Some(cells)
}

/// Read-only structural preflight. Larger source syntax is admitted ONLY to
/// this shared representation, never to the ordinary local reducer.
pub(super) fn admitted(source: &WorkingTerm) -> bool {
    geometry(source).is_some()
}

fn header_geometry(source: &WorkingTerm) -> Option<(usize, usize)> {
    if source.paths.is_empty()
        || source.paths.len() > MAX_PATHS
        || !source.paths.iter().all(KernelVariable::is_bound_path)
        || source.constraints.len() > 64
        || !source.phase.is_algebraic()
        || source.phase.term_count() > MAX_PHASE_TERMS
        || !source
            .constraints
            .iter()
            .all(|row| row.is_algebraic() && row.term_count() <= MAX_BOOLEAN_TERMS)
        || !scalar_within_budget(&source.coefficient)
    {
        return None;
    }
    let mut cells = source.paths.len();
    let mut retained = scalar_cells(&source.coefficient, &mut 256)?;
    for row in &source.constraints {
        for m in row.terms() {
            retained = retained.checked_add(1 + m.variables().count())?;
            if retained > MAX_SOURCE_CELLS || m.variables().any(KernelVariable::is_bound_path) {
                return None;
            }
        }
    }
    cells += retained;
    (cells <= MAX_SOURCE_CELLS).then_some((cells, retained))
}

fn phase_geometry(
    source: &WorkingTerm,
    m: &KernelMonomial,
    c: &PhaseCoefficient,
    cells: &mut usize,
) -> Option<usize> {
    let size = 1 + m.variables().count();
    *cells = cells.checked_add(size)?;
    if *cells > MAX_SOURCE_CELLS
        || m.variables()
            .any(|v| v.is_bound_path() && !source.paths.contains(v))
    {
        return None;
    }
    let rational = c.as_rational()?;
    if rational.numer().bits() > 256 || rational.denom().bits() > 256 {
        return None;
    }
    Some(size)
}

fn geometry(source: &WorkingTerm) -> Option<(usize, usize)> {
    let (mut cells, retained) = header_geometry(source)?;
    for (m, c) in source.phase.terms() {
        phase_geometry(source, m, c, &mut cells)?;
    }
    Some((cells, retained))
}

pub(super) fn sum(
    source: &WorkingTerm,
    splits: &mut usize,
    cells: &mut usize,
) -> Option<ExactAggregate> {
    let initial_work = *cells;
    let (mut source_cells, retained_cells) = header_geometry(source)?;
    charge(cells, source_cells)?;
    let paths = source.paths.iter().collect::<Vec<_>>();
    let leaves = 1usize << paths.len();
    // Same bound-node allowance as a complete binary Shannon tree, shared
    // with every other factor. No new per-leaf or coefficient-work budget.
    *splits = splits.checked_sub(leaves - 1)?;
    let mut groups: BTreeMap<FreeKey<'_>, BTreeMap<u8, &PhaseCoefficient>> = BTreeMap::new();
    for (m, c) in source.phase.terms() {
        // Fuse phase admission with grouping: inspect the complete source
        // once and allocate only a projected-key reference plus mask/value
        // records. No full pre-scan followed by free-vector copying remains.
        let size = phase_geometry(source, m, c, &mut source_cells)?;
        charge(cells, size + 3)?;
        let mut mask = 0u8;
        for v in m.variables() {
            if let Some(i) = paths.iter().position(|p| *p == v) {
                mask |= 1 << i;
            }
        }
        // The (free monomial, bound mask) split of a square-free monomial
        // is injective. All keys/coefficients borrow the immutable source.
        if groups
            .entry(FreeKey(m))
            .or_default()
            .insert(mask, c)
            .is_some()
        {
            return None;
        }
    }
    let mut shared: BTreeMap<&BTreeMap<u8, &PhaseCoefficient>, Vec<PhaseCoefficient>> =
        BTreeMap::new();
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate shared small sum grouped: source_cells={source_cells} groups={} remaining={}",
            groups.len(),
            *cells
        );
    }
    let mut active_patterns = BTreeSet::new();
    let mut constant_pattern = None;
    for (free, pattern) in &groups {
        charge(cells, 1 + pattern.len())?;
        match shared.entry(pattern) {
            std::collections::btree_map::Entry::Occupied(_) => {}
            std::collections::btree_map::Entry::Vacant(entry) => {
                charge(cells, leaves)?;
                let mut values = vec![PhaseCoefficient::default(); leaves];
                // k<=3 and at most eight source coefficients of <=256 bits.
                // Temporary rational widths are bounded by eight operand
                // widths. A complete subset-sum transform replaces repeated
                // tests of every source mask at every assignment.
                for (&mask, &c) in pattern {
                    charge(cells, 1)?;
                    values[mask as usize] = c.clone();
                }
                for bit in 0..paths.len() {
                    for a in 0..leaves {
                        if a & (1 << bit) != 0 {
                            charge(cells, 2)?;
                            let lower = values[a ^ (1 << bit)].clone();
                            values[a].add_assign(lower);
                        }
                    }
                }
                entry.insert(values);
            }
        }
        charge(cells, 1)?;
        if free.variables().next().is_some() {
            active_patterns.insert(pattern);
        } else {
            constant_pattern = Some(pattern);
        }
    }
    // A vector of ALL nonconstant block values determines the full formal
    // free phase. Combine equal complete leaf signatures (with exact constant
    // half-turn signs) BEFORE any free phase is expanded. No prefix equality.
    type Signature<'a> = (Vec<&'a PhaseCoefficient>, PhaseCoefficient);
    let mut signatures = BTreeMap::<Signature<'_>, (usize, i64)>::new();
    for assignment in 0..(1u8 << paths.len()) {
        let a = usize::from(assignment);
        charge(cells, 2 + active_patterns.len())?;
        let signature = active_patterns
            .iter()
            .map(|p| &shared[p][a])
            .collect::<Vec<_>>();
        let mut constant = constant_pattern
            .map(|p| shared[p][a].clone())
            .unwrap_or_default();
        let sign = if constant.rational_part() >= ratio(1, 2) {
            constant.add_assign(PhaseCoefficient::rational(ratio(1, 2)));
            -1
        } else {
            1
        };
        signatures.entry((signature, constant)).or_insert((a, 0)).1 += sign;
    }
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        // Read-only bounded geometry for a possible phase-basis route. It
        // never changes the sum, budget, binder set or certificate decision.
        let periods = (shared.len() <= 256).then(|| {
            (1..leaves)
                .filter(|d| {
                    shared
                        .values()
                        .all(|values| (0..leaves).all(|a| values[a] == values[a ^ d]))
                })
                .collect::<Vec<_>>()
        });
        eprintln!(
            "aggregate shared small sum signatures: patterns={} signatures={} surviving={} remaining={} periods={periods:?} multiplicities={:?}",
            shared.len(),
            signatures.len(),
            signatures.values().filter(|(_, n)| *n != 0).count(),
            *cells,
            signatures
                .values()
                .map(|(a, n)| (*a, *n))
                .collect::<Vec<_>>()
        );
    }
    let patterns = shared.len();
    let mut result = ExactAggregate::new();
    let mut atoms = 0;
    let mut leaf_cells = 0usize;
    for ((_, constant), (a, multiplicity)) in signatures {
        if multiplicity == 0 {
            continue;
        }
        let mut phase = KernelPhasePolynomial::default();
        for (free, pattern) in &groups {
            charge(cells, 1)?;
            let value = &shared[pattern][a];
            if value.is_zero() || free.variables().next().is_none() {
                continue;
            }
            // Only surviving coefficients allocate owned free monomials.
            // add_term moves this unique key, without generic Boolean lifts
            // or growing-prefix phase copies.
            let allocated = 1 + free.variables().count();
            charge(cells, allocated)?;
            leaf_cells += allocated;
            phase.add_term(
                KernelMonomial::from_variables(free.variables().cloned()),
                value.clone(),
            );
        }
        charge(cells, 3 + retained_cells)?;
        phase.add_term(KernelMonomial::one(), constant);
        accumulate_exact_term(
            ExactTerm {
                constraints: source.constraints.clone(),
                coefficient: normalize_scalar(
                    source
                        .coefficient
                        .clone()
                        .multiply(KernelScalar::Rational(integer(multiplicity))),
                ),
                phase,
            },
            &mut result,
            &mut atoms,
        )?;
    }
    result.retain(|_, values| !values.is_empty());
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate shared small sum: paths={} source_cells={source_cells} groups={} patterns={patterns} leaf_cells={leaf_cells} atoms={atoms} charged={} remaining={}",
            paths.len(),
            groups.len(),
            initial_work - *cells,
            *cells
        );
    }
    Some(result)
}
