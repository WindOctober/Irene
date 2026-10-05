//! Complete component checkpoints without reconstructing an oversized monolith.
use super::scalar::{integer, scalar_conditions_within_budget};
use super::{
    KernelMonomial, KernelPhasePolynomial, KernelScalar, KernelVariable, WorkingTerm, pair_period,
    vacuous,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::collections::{BTreeMap, BTreeSet};

const MAX_SMALL_PATHS: usize = 8;

fn charge(work: &mut usize, amount: usize) -> Option<()> {
    *work = work.checked_sub(amount)?;
    Some(())
}

#[derive(Default, Debug, PartialEq, Eq)]
struct Shape {
    paths: usize,
    rows: usize,
    phase_terms: usize,
    cells: usize,
}

struct Connectivity<'a> {
    positions: BTreeMap<&'a KernelVariable, usize>,
    owners: Vec<usize>,
    groups: BTreeMap<usize, Shape>,
    common: Shape,
    vacuous: usize,
}

fn root(parents: &mut [usize], mut index: usize) -> usize {
    while parents[index] != index {
        parents[index] = parents[parents[index]];
        index = parents[index];
    }
    index
}

fn connectivity(source: &WorkingTerm) -> Option<Connectivity<'_>> {
    if !vacuous::admitted(source)
        || !scalar_conditions_within_budget(&source.coefficient, |row| {
            row.terms()
                .flat_map(KernelMonomial::variables)
                .all(|v| !v.is_bound_path())
        })
    {
        return None;
    }
    let positions = source
        .paths
        .iter()
        .enumerate()
        .map(|(i, v)| (v, i))
        .collect::<BTreeMap<_, _>>();
    let mut parents = (0..positions.len()).collect::<Vec<_>>();
    let mut active = BTreeSet::new();
    let mut connect = |variables: Vec<&KernelVariable>| {
        let mut first = None;
        for v in variables {
            let Some(&position) = positions.get(v) else {
                continue;
            };
            active.insert(position);
            let current = root(&mut parents, position);
            if let Some(previous) = first {
                let previous = root(&mut parents, previous);
                parents[current] = previous;
            } else {
                first = Some(current);
            }
        }
    };
    // A whole XOR guard is ONE hyperedge, never separate monomial guards.
    for row in &source.constraints {
        connect(row.terms().flat_map(KernelMonomial::variables).collect());
    }
    for (m, _) in source.phase.terms() {
        connect(m.variables().collect());
    }
    let owners = (0..positions.len())
        .map(|i| root(&mut parents, i))
        .collect::<Vec<_>>();
    let mut groups = BTreeMap::<usize, Shape>::new();
    for &i in &active {
        let shape = groups.entry(owners[i]).or_default();
        shape.paths += 1;
        shape.cells += 1;
    }
    let mut common = Shape::default();
    for row in &source.constraints {
        let owner = row
            .terms()
            .flat_map(KernelMonomial::variables)
            .find_map(|v| positions.get(v))
            .map(|&i| owners[i]);
        let shape = match owner {
            Some(i) => groups.get_mut(&i)?,
            None => &mut common,
        };
        shape.rows += 1;
        shape.cells += row
            .terms()
            .map(|m| 1 + m.variables().count())
            .sum::<usize>();
    }
    for (m, _) in source.phase.terms() {
        let owner = m
            .variables()
            .find_map(|v| positions.get(v))
            .map(|&i| owners[i]);
        let shape = match owner {
            Some(i) => groups.get_mut(&i)?,
            None => &mut common,
        };
        shape.phase_terms += 1;
        shape.cells += 1 + m.variables().count();
    }
    Some(Connectivity {
        positions,
        owners,
        groups,
        common,
        vacuous: source.paths.len() - active.len(),
    })
}

pub(super) fn local_cells(term: &WorkingTerm) -> Option<usize> {
    let mut cells = term.paths.len();
    let mut inspect = |m: &KernelMonomial| {
        cells += 1 + m.variables().count();
        cells <= 32768
    };
    (term.constraints.iter().all(|r| r.terms().all(&mut inspect))
        && term.phase.terms().all(|(m, _)| inspect(m))
        && scalar_conditions_within_budget(&term.coefficient, |r| r.terms().all(&mut inspect)))
    .then_some(cells)
}

/// Every local reduction must finish: never salvage a Residual or discard a
/// later factor. Ordinary reduction retains its original rewrite preflights.
/// Each source has <=32binders/32768cells, so local elimination has at most
///32 binder-removing rounds plus the existing finite recovery probes.
/// The callback returns only a COMPLETE equivalent term. Refusal (including
/// an unsupported outcome) is None, never a prefix or a missing factor.
pub(super) fn reduce_components(
    factors: Components,
    work: &mut usize,
    mut reduce: impl FnMut(WorkingTerm) -> Option<WorkingTerm>,
) -> Option<Vec<WorkingTerm>> {
    let mut result = Vec::with_capacity(factors.len());
    for factor in factors.0 {
        if factor.paths.len() <= MAX_SMALL_PATHS {
            result.push(factor);
            continue;
        }
        // The private constructor already validated and charged the COMPLETE
        // input syntax. Consume that admission without rescanning its keys.
        // The local reducer still has all its own rewrite/preflight limits.
        charge(work, 1)?;
        let before = (
            factor.paths.len(),
            factor.constraints.len(),
            factor.phase.term_count(),
        );
        let mut factor = reduce(factor)?;
        if local_cells(&factor).is_none() && factor.paths.len() == 4 {
            // A COMPLETE local result, never Residual/prefix recovery. Reuse
            // the remaining compaction allowance for a full four-bit period
            // certificate; every original scalar/guard and later factor stays.
            let compacted = pair_period::compact_four(&mut factor, work);
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "aggregate checkpoint four-bit period: result={compacted:?} paths={} terms={} work={work}",
                    factor.paths.len(),
                    factor.phase.term_count()
                );
            }
            if compacted != Some(true) {
                return None;
            }
        }
        charge(work, local_cells(&factor)?)?;
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "aggregate checkpoint component reduction: before={before:?} after={:?} work={work}",
                (
                    factor.paths.len(),
                    factor.constraints.len(),
                    factor.phase.term_count()
                )
            );
        }
        if factor.paths.len() > MAX_SMALL_PATHS {
            return None;
        }
        result.push(factor);
    }
    Some(result)
}

/// Complete bounded construction from the borrowed plan. No absent-binder
/// dummy factors and no intermediate whole-phase reconstruction.
#[derive(Clone)]
pub(super) struct Components(Vec<WorkingTerm>);

#[cfg(test)]
impl Components {
    pub(super) fn from_complete_terms(terms: Vec<WorkingTerm>) -> Self {
        Self(terms)
    }
    pub(super) fn last_mut(&mut self) -> Option<&mut WorkingTerm> {
        self.0.last_mut()
    }
}

impl std::ops::Deref for Components {
    type Target = [WorkingTerm];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

pub(super) fn components(source: &WorkingTerm, work: &mut usize) -> Option<Components> {
    let plan = connectivity(source)?;
    let KernelScalar::Rational(weight) = &source.coefficient else {
        return None;
    };
    if weight.numer().bits() > 32768
        || weight.denom().bits() > 32768
        || plan.groups.len() > 128
        || plan.common.cells > 32768
        || plan
            .groups
            .values()
            .any(|s| s.paths > 32 || s.cells > 32768)
    {
        return None;
    }
    // Entire syntax to copy, path-reference plan, and exact multiplicity bits.
    // The separate read-only source admission is already bounded at750000.
    charge(
        work,
        plan.positions.len()
            + plan.common.cells
            + plan.groups.values().map(|s| s.cells).sum::<usize>()
            + plan.vacuous.div_ceil(64),
    )?;
    let unit = || WorkingTerm {
        paths: BTreeSet::new(),
        constraints: Vec::new(),
        coefficient: KernelScalar::Rational(integer(1)),
        phase: KernelPhasePolynomial::default(),
    };
    let mut groups = plan
        .groups
        .keys()
        .map(|&id| (id, unit()))
        .collect::<BTreeMap<_, _>>();
    for (v, &i) in &plan.positions {
        if let Some(group) = groups.get_mut(&plan.owners[i]) {
            group.paths.insert((*v).clone());
        }
    }
    let mut common = unit();
    common.coefficient =
        KernelScalar::Rational(weight * BigRational::from_integer(BigInt::from(1) << plan.vacuous));
    for row in &source.constraints {
        let owner = row
            .terms()
            .flat_map(KernelMonomial::variables)
            .find_map(|v| plan.positions.get(v))
            .map(|&i| plan.owners[i]);
        match owner {
            Some(id) => groups.get_mut(&id)?.constraints.push(row.clone()),
            None => common.constraints.push(row.clone()),
        }
    }
    for (m, c) in source.phase.terms() {
        let owner = m
            .variables()
            .find_map(|v| plan.positions.get(v))
            .map(|&i| plan.owners[i]);
        let target = match owner {
            Some(id) => &mut groups.get_mut(&id)?.phase,
            None => &mut common.phase,
        };
        target.add_term(m.clone(), c.clone());
    }
    Some(Components(
        std::iter::once(common)
            .chain(groups.into_values())
            .collect(),
    ))
}

#[cfg(test)]
mod tests;
