//! Exact four-atom product certificate without constructing its convolution.
//! Every corner is present. Scalar products and the COMPLETE modular phase
//! rectangle identity certify all four terms, including half-turn signs.

use super::collection::{ExactAggregate, ExactTerm, accumulate_exact_term};
use super::scalar::{integer, ratio};
use super::{KernelPhasePolynomial, KernelScalar, MAX_PHASE_TERMS};
use crate::symbolic::PhaseCoefficient;
use num_bigint::BigInt;
use num_rational::BigRational;
use std::collections::BTreeMap;

fn charge(budget: &mut usize, cells: usize) -> Option<()> {
    *budget = budget.checked_sub(cells)?;
    Some(())
}

// Return exp(2*pi*i*(p0+p3-p1-p2)) only if it is identically +1 or -1.
// Borrowed ordered merging visits every source coefficient, without building
// four differences/copies. An early nonconstant mismatch is only a refusal.
fn sign(phases: [&KernelPhasePolynomial; 4], budget: &mut usize) -> Option<i64> {
    if phases.iter().any(|phase| !phase.is_algebraic()) {
        return None;
    }
    let mut terms = phases.map(|p| p.terms().peekable());
    let mut constant = PhaseCoefficient::default();
    while let Some(monomial) = terms
        .iter_mut()
        .filter_map(|i| i.peek().map(|(m, _)| *m))
        .min()
    {
        let mut total = PhaseCoefficient::default();
        for (i, iter) in terms.iter_mut().enumerate() {
            if iter.peek().is_some_and(|(m, _)| *m == monomial) {
                let (m, c) = iter.next()?;
                charge(budget, 1 + m.variables().count())?;
                let r = c.as_rational()?;
                if r.numer().bits() > 256 || r.denom().bits() > 256 {
                    return None;
                }
                total.add_assign(if i == 0 || i == 3 {
                    c.clone()
                } else {
                    c.scaled(BigInt::from(-1))
                });
            }
        }
        if monomial.variables().next().is_none() {
            constant = total;
        } else if !total.is_zero() {
            return None;
        }
    }
    match constant.as_rational()? {
        r if r == integer(0) => Some(1),
        r if r == ratio(1, 2) => Some(-1),
        _ => None,
    }
}

fn certificate(source: &ExactAggregate, budget: &mut usize) -> Option<(usize, usize, BigRational)> {
    if source.len() != 1 {
        return None;
    }
    let (entry, values) = source.first_key_value()?;
    if values.len() != 4 || entry.constraints.iter().any(|row| !row.is_algebraic()) {
        return None;
    }
    let atoms = values
        .iter()
        .map(|(p, c)| {
            let KernelScalar::Rational(r) = c else {
                return None;
            };
            (r != &integer(0) && r.numer().bits() <= 4096 && r.denom().bits() <= 4096)
                .then_some((p, r))
        })
        .collect::<Option<Vec<_>>>()?;
    for (row, column, corner) in [(1, 2, 3), (1, 3, 2), (2, 3, 1)] {
        charge(budget, 4)?;
        let a = atoms[0].1 * atoms[corner].1;
        let b = atoms[row].1 * atoms[column].1;
        let expected = if a == b {
            1
        } else if a == -b {
            -1
        } else {
            continue;
        };
        if sign(
            [atoms[0].0, atoms[row].0, atoms[column].0, atoms[corner].0],
            budget,
        ) != Some(expected)
        {
            continue;
        }
        let relative = atoms[column].1 / atoms[0].1;
        if relative.numer().bits() > 4096 || relative.denom().bits() > 4096 {
            return None;
        }
        if atoms[0]
            .0
            .term_count()
            .checked_add(atoms[column].0.term_count())?
            > MAX_PHASE_TERMS
        {
            return None;
        }
        // Consume the original phase maps; only the pivot's subtraction
        // allocates copied keys/coefficient deltas. No copies of the unchanged
        // left phases or the column prefix are performed.
        charge(budget, 8)?;
        for (m, _) in atoms[0].0.terms() {
            charge(budget, 2 * (1 + m.variables().count()))?;
        }
        for row in &entry.constraints {
            for m in row.terms() {
                charge(budget, 4 * (1 + m.variables().count()))?;
            }
        }
        return Some((row, column, relative));
    }
    None
}

/// A failed preflight leaves the complete source available for old refinement.
/// After consumption, a later refusal leaves None: callers MUST abandon the
/// entire proof, never treat a consumed/prefix source as a unit or empty sum.
pub(super) fn factor(
    source: &mut Option<ExactAggregate>,
    budget: &mut usize,
) -> Option<Vec<ExactAggregate>> {
    let initial = *budget;
    let (row, column, relative) = certificate(source.as_ref()?, budget)?;
    let (entry, values) = source.take()?.into_iter().next()?;
    let mut atoms = values.into_iter().map(Some).collect::<Vec<_>>();
    let (pivot, pivot_scalar) = atoms[0].take()?;
    let (row_phase, row_scalar) = atoms[row].take()?;
    let (mut relative_phase, _) = atoms[column].take()?;
    for (m, c) in pivot.terms() {
        relative_phase.add_term(m.clone(), c.scaled(BigInt::from(-1)));
    }
    let mut left = ExactAggregate::new();
    let mut right = ExactAggregate::new();
    let mut count = 0;
    for (phase, coefficient) in [(pivot, pivot_scalar), (row_phase, row_scalar)] {
        accumulate_exact_term(
            ExactTerm {
                constraints: entry.constraints.clone(),
                coefficient,
                phase,
            },
            &mut left,
            &mut count,
        )?;
    }
    count = 0;
    for (coefficient, phase) in [
        (integer(1), KernelPhasePolynomial::default()),
        (relative, relative_phase),
    ] {
        accumulate_exact_term(
            ExactTerm {
                constraints: entry.constraints.clone(),
                coefficient: KernelScalar::Rational(coefficient),
                phase,
            },
            &mut right,
            &mut count,
        )?;
    }
    // These factors' four products correspond bijectively to the FOUR
    // distinct source atoms. For the last corner the identity above
    // checks BOTH the full phase (possibly a half turn) and its sign.
    // No rank guess, zero function division, or omitted cell is accepted.
    if left.values().map(BTreeMap::len).sum::<usize>() != 2
        || right.values().map(BTreeMap::len).sum::<usize>() != 2
    {
        return None;
    }
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate rectangle certificate: charged={} remaining={}",
            initial - *budget,
            *budget
        );
    }
    Some(vec![left, right])
}

#[cfg(test)]
mod tests;
