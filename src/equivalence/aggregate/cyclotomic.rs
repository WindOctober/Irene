//! Closed constant arithmetic in Q(zeta_(2^62)), without SMT or path sums.
//! Coefficients are exact rationals; only phase exponents wrap. Every value
//! is canonical in the power basis below ORDER/2, using zeta^(ORDER/2)=-1.
//! Resource refusal returns None, never a truncated polynomial. Budgets may
//! be consumed on refusal; immutable operands are always preserved.

use crate::symbolic::PhaseCoefficient;
use num_bigint::BigInt;
use num_rational::BigRational;
use std::collections::BTreeMap;

pub(crate) const ORDER: u64 = 1 << 62;
const HALF: u64 = ORDER / 2;

pub(crate) struct Budget {
    work: usize,
    max_terms: usize,
    max_bits: u64,
}

impl Budget {
    pub(crate) fn new(work: usize) -> Self {
        Self {
            work,
            max_terms: 8192,
            max_bits: 32768,
        }
    }

    pub(super) fn charge(&mut self, n: usize) -> Option<()> {
        self.work = self.work.checked_sub(n)?;
        Some(())
    }

    fn admits(&self, r: &BigRational) -> bool {
        r.numer().bits() <= self.max_bits && r.denom().bits() <= self.max_bits
    }
}

/// Sorted, distinct exponents below HALF; all stored coefficients are nonzero.
/// The private representation prevents noncanonical values reaching arithmetic.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Cyclotomic(Vec<(u64, BigRational)>);

impl Cyclotomic {
    pub(crate) fn terms(&self) -> &[(u64, BigRational)] {
        &self.0
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    pub(crate) fn is_one(&self) -> bool {
        matches!(self.0.as_slice(), [(0, r)] if *r == BigRational::from_integer(1.into()))
    }

    /// Fold half-turn signs and combine coefficients. The map includes zero
    /// entries until the end; even transient growth is bounded conservatively.
    pub(crate) fn from_terms(
        terms: impl IntoIterator<Item = (u64, BigRational)>,
        budget: &mut Budget,
    ) -> Option<Self> {
        let mut map = BTreeMap::<u64, BigRational>::new();
        for (exponent, mut coefficient) in terms {
            budget.charge(1)?;
            if !budget.admits(&coefficient) {
                return None;
            }
            let exponent = exponent % ORDER;
            if exponent >= HALF {
                coefficient = -coefficient;
            }
            let sum = map
                .entry(exponent % HALF)
                .or_insert_with(|| BigRational::from_integer(0.into()));
            *sum += coefficient;
            if !budget.admits(sum) || map.len() > budget.max_terms {
                return None;
            }
        }
        Some(Self(
            map.into_iter()
                .filter(|(_, r)| *r != BigRational::from_integer(0.into()))
                .collect(),
        ))
    }

    /// Exact phase admission: reject nonconstant or nondyadic angles rather
    /// than rounding them to the nearest representable root of unity.
    pub(crate) fn from_phase(phase: &PhaseCoefficient, budget: &mut Budget) -> Option<Self> {
        budget.charge(1)?;
        let turns = phase.as_rational()?;
        if !budget.admits(&turns) {
            return None;
        }
        let exponent = turns * BigInt::from(ORDER);
        if !exponent.is_integer() {
            return None;
        }
        let exponent = u64::try_from(exponent.to_integer()).ok()?;
        Self::from_terms([(exponent, BigRational::from_integer(1.into()))], budget)
    }

    fn admitted(&self, budget: &Budget) -> bool {
        self.0.len() <= budget.max_terms && self.0.iter().all(|(_, r)| budget.admits(r))
    }

    pub(crate) fn add(&self, other: &Self, budget: &mut Budget) -> Option<Self> {
        Self::from_terms(self.0.iter().chain(&other.0).cloned(), budget)
    }

    pub(crate) fn multiply(&self, other: &Self, budget: &mut Budget) -> Option<Self> {
        if !self.admitted(budget) || !other.admitted(budget) {
            return None;
        }
        let products = self.0.len().checked_mul(other.0.len())?;
        if products > budget.max_terms {
            return None;
        }
        budget.charge(products)?;
        // Each exponent is < HALF, so their sum cannot overflow u64.
        Self::from_terms(
            self.0
                .iter()
                .flat_map(|(a, r)| other.0.iter().map(move |(b, s)| ((a + b) % ORDER, r * s))),
            budget,
        )
    }

    pub(crate) fn conjugate(&self, budget: &mut Budget) -> Option<Self> {
        Self::from_terms(
            self.0.iter().map(|(p, r)| ((ORDER - p) % ORDER, r.clone())),
            budget,
        )
    }

    pub(crate) fn norm_squared(&self, budget: &mut Budget) -> Option<Self> {
        self.multiply(&self.conjugate(budget)?, budget)
    }
}

#[cfg(test)]
mod tests;
