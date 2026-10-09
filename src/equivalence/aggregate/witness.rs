//! Exact constant algebra shared by the EQ reducers. No counterexample search.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_rational::BigRational;

use super::collection::ExactAggregate;
use super::exact_trig;
use super::scalar::{integer, normalize_scalar, ratio, scalar_within_budget};
use super::{KernelBooleanPolynomial, KernelScalar};
use crate::ir::{NumericExpr, NumericExprKind};
use crate::symbolic::PhaseCoefficient;

const MAX_ATOMS: usize = 1024;
const MAX_CELLS: usize = 32768;
const MAX_CONSTANT_LEAVES: usize = 1024;
const MAX_WORK: usize = 1_000_000;
const MAX_ARITHMETIC: usize = 100_000;
const MAX_RATIONAL_BITS: u64 = 4096;
// For N = 2^62, Phi_N(X) = X^(N/2) + 1. Powers below N/2 form
// a rational basis, so reducing X^(N/2) to -1 is sufficient for exact
// zero testing. The representation is sparse, never a degree-sized vector.
const ROOT_ORDER: u64 = 1 << 62;
const DEGREE: u64 = ROOT_ORDER / 2;
const MAX_VALUE_TERMS: usize = 1024;

#[derive(Default, Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct Cyclotomic(BTreeMap<u64, BigRational>);

struct Budget {
    nodes: usize,
    work: usize,
    arithmetic: usize,
}

impl Default for Budget {
    fn default() -> Self {
        Self {
            nodes: MAX_CONSTANT_LEAVES,
            work: MAX_WORK,
            arithmetic: MAX_ARITHMETIC,
        }
    }
}

fn spend(remaining: &mut usize, amount: usize) -> Option<()> {
    if amount > *remaining {
        *remaining = 0;
        return None;
    }
    *remaining -= amount;
    Some(())
}

fn small_rational(value: &BigRational) -> bool {
    value.numer().bits() <= MAX_RATIONAL_BITS && value.denom().bits() <= MAX_RATIONAL_BITS
}

impl Cyclotomic {
    fn add_term(&mut self, power: u64, mut value: BigRational, budget: &mut Budget) -> Option<()> {
        spend(&mut budget.arithmetic, 1)?;
        if !small_rational(&value) {
            return None;
        }
        let power = power % ROOT_ORDER;
        let power = if power >= DEGREE {
            value = -value;
            power - DEGREE
        } else {
            power
        };
        let value = self.0.remove(&power).unwrap_or_else(|| integer(0)) + value;
        if !small_rational(&value) {
            return None;
        }
        if value != integer(0) {
            self.0.insert(power, value);
        }
        if self.0.len() > MAX_VALUE_TERMS {
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "density cyclotomic support refused: terms={} arithmetic_remaining={}",
                    self.0.len(),
                    budget.arithmetic
                );
            }
            return None;
        }
        Some(())
    }

    fn monomial(power: u64, value: BigRational, budget: &mut Budget) -> Option<Self> {
        let mut result = Self::default();
        result.add_term(power, value, budget)?;
        Some(result)
    }

    fn add(mut self, other: Self, budget: &mut Budget) -> Option<Self> {
        for (power, value) in other.0 {
            self.add_term(power, value, budget)?;
        }
        Some(self)
    }

    fn multiply(&self, other: &Self, budget: &mut Budget) -> Option<Self> {
        let mut result = Self::default();
        for (left_power, left) in &self.0 {
            for (right_power, right) in &other.0 {
                spend(&mut budget.arithmetic, 1)?;
                result.add_term(left_power + right_power, left * right, budget)?;
            }
        }
        Some(result)
    }
}

fn exponent(coefficient: &PhaseCoefficient) -> Option<u64> {
    let value = coefficient.as_rational()?;
    if !small_rational(&value) {
        return None;
    }
    let value = value * BigInt::from(ROOT_ORDER);
    if value.denom() != &BigInt::from(1) {
        return None;
    }
    value.numer().try_into().ok()
}

/// Only closed Boolean constants are admitted; no assignment is synthesized.
fn boolean(polynomial: &KernelBooleanPolynomial) -> Option<bool> {
    if polynomial.is_zero() {
        Some(false)
    } else if polynomial.is_one() {
        Some(true)
    } else {
        None
    }
}

fn rational_root(value: &BigRational) -> Option<BigRational> {
    if !small_rational(value) || value < &integer(0) {
        return None;
    }
    let numerator = value.numer().sqrt();
    let denominator = value.denom().sqrt();
    (&numerator * &numerator == *value.numer() && &denominator * &denominator == *value.denom())
        .then(|| BigRational::new(numerator, denominator))
}

fn scalar(value: &KernelScalar, budget: &mut Budget) -> Option<Cyclotomic> {
    spend(&mut budget.work, 1)?;
    match value {
        KernelScalar::Rational(value) => Cyclotomic::monomial(0, value.clone(), budget),
        KernelScalar::Neg(value) => {
            let value = scalar(value, budget)?;
            let minus_one = Cyclotomic::monomial(0, integer(-1), budget)?;
            value.multiply(&minus_one, budget)
        }
        KernelScalar::Add(left, right) => scalar(left, budget)?.add(scalar(right, budget)?, budget),
        KernelScalar::Mul(left, right) => {
            scalar(left, budget)?.multiply(&scalar(right, budget)?, budget)
        }
        KernelScalar::Sqrt(value) => {
            let KernelScalar::Rational(value) = value.as_ref() else {
                return None;
            };
            if let Some(root) = rational_root(value) {
                return Cyclotomic::monomial(0, root, budget);
            }
            if !small_rational(value) || value < &integer(0) {
                return None;
            }
            // sqrt(r) = sqrt(2r)/2 * (zeta^(N/8) - zeta^(3N/8)).
            let factor = rational_root(&(value * integer(2)))? / integer(2);
            let mut result = Cyclotomic::monomial(ROOT_ORDER / 8, factor.clone(), budget)?;
            result.add_term(3 * ROOT_ORDER / 8, -factor, budget)?;
            Some(result)
        }
        KernelScalar::Inverse(value) => {
            let KernelScalar::Rational(value) = value.as_ref() else {
                return None;
            };
            if value == &integer(0) {
                return None;
            }
            Cyclotomic::monomial(0, value.recip(), budget)
        }
        KernelScalar::Sin(angle) | KernelScalar::Cos(angle) => {
            let power = exponent(&PhaseCoefficient::angle(angle.clone(), integer(1)))?;
            let positive = Cyclotomic::monomial(power, ratio(1, 2), budget)?;
            let negative = Cyclotomic::monomial(
                (ROOT_ORDER - power) % ROOT_ORDER,
                if matches!(value, KernelScalar::Sin(_)) {
                    ratio(-1, 2)
                } else {
                    ratio(1, 2)
                },
                budget,
            )?;
            let result = positive.add(negative, budget)?;
            if matches!(value, KernelScalar::Sin(_)) {
                // 1/i = -i = zeta^(3N/4).
                result.multiply(
                    &Cyclotomic::monomial(3 * ROOT_ORDER / 4, integer(1), budget)?,
                    budget,
                )
            } else {
                Some(result)
            }
        }
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => scalar(
            if boolean(condition)? {
                when_true
            } else {
                when_false
            },
            budget,
        ),
    }
}

fn evaluate(source: &ExactAggregate, budget: &mut Budget) -> Option<Cyclotomic> {
    let mut result = Cyclotomic::default();
    for (entry, coefficients) in source {
        let mut active = true;
        for constraint in &entry.constraints {
            active &= !boolean(constraint)?;
        }
        if !active {
            continue;
        }
        for (phase, coefficient) in coefficients {
            let mut power = 0u64;
            for (monomial, coefficient) in phase.terms() {
                if monomial.variables().next().is_some() {
                    return None;
                }
                power = (power + exponent(coefficient)?) % ROOT_ORDER;
            }
            let phase = Cyclotomic::monomial(power, integer(1), budget)?;
            let coefficient = scalar(coefficient, budget).or_else(|| {
                let specialized = normalized_constant_scalar(coefficient, budget)?;
                scalar(&specialized, budget)
            })?;
            result = result.add(coefficient.multiply(&phase, budget)?, budget)?;
        }
    }
    Some(result)
}

/// A constant cofactor can be rational even when its individual radical
/// factors lie outside this field. Select the constant scalar branches,
/// then normalize the WHOLE scalar without erasing the original phase.
fn normalized_constant_scalar(value: &KernelScalar, budget: &mut Budget) -> Option<KernelScalar> {
    let mut geometry = Geometry { cells: 0 };
    geometry.scalar(value, 0)?;
    if geometry.cells > 256 {
        return None;
    }
    spend(&mut budget.work, 3 * geometry.cells.max(1))?;
    fn specialize(value: &KernelScalar) -> Option<KernelScalar> {
        Some(match value {
            KernelScalar::Rational(r) => {
                if r.numer().bits() > 256 || r.denom().bits() > 256 {
                    return None;
                }
                value.clone()
            }
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => specialize(if boolean(condition)? {
                when_true
            } else {
                when_false
            })?,
            KernelScalar::Add(a, b) => {
                KernelScalar::Add(Box::new(specialize(a)?), Box::new(specialize(b)?))
            }
            KernelScalar::Mul(a, b) => {
                KernelScalar::Mul(Box::new(specialize(a)?), Box::new(specialize(b)?))
            }
            KernelScalar::Neg(a) => KernelScalar::Neg(Box::new(specialize(a)?)),
            KernelScalar::Sqrt(a) => {
                let a = normalize_scalar(specialize(a)?);
                if !matches!(&a, KernelScalar::Rational(r) if r >= &integer(0)) {
                    return None;
                }
                KernelScalar::Sqrt(Box::new(a))
            }
            KernelScalar::Inverse(a) => {
                let a = normalize_scalar(specialize(a)?);
                if !matches!(&a, KernelScalar::Rational(r) if r != &integer(0)) {
                    return None;
                }
                KernelScalar::Inverse(Box::new(a))
            }
            KernelScalar::Sin(angle) | KernelScalar::Cos(angle) => {
                if !exact_trig::admitted(angle, &mut 64) {
                    return None;
                }
                value.clone()
            }
        })
    }
    let result = normalize_scalar(specialize(value)?);
    scalar_within_budget(&result).then_some(result)
}

struct Geometry {
    cells: usize,
}

impl Geometry {
    fn charge(&mut self, amount: usize) -> Option<()> {
        self.cells = self.cells.checked_add(amount)?;
        (self.cells <= MAX_CELLS).then_some(())
    }

    fn boolean(&mut self, value: &KernelBooleanPolynomial) -> Option<()> {
        self.charge(1)?;
        // Reject unresolved graphs without requesting an ANF expansion.
        boolean(value).map(|_| ())
    }

    fn numeric(&mut self, value: &NumericExpr, depth: usize) -> Option<()> {
        self.charge(1)?;
        if depth >= 64 {
            return None;
        }
        match &value.kind {
            NumericExprKind::Rational(value) => small_rational(value).then_some(()),
            NumericExprKind::Neg(value) => self.numeric(value, depth + 1),
            NumericExprKind::Add(left, right)
            | NumericExprKind::Sub(left, right)
            | NumericExprKind::Mul(left, right)
            | NumericExprKind::Div(left, right) => {
                self.numeric(left, depth + 1)?;
                self.numeric(right, depth + 1)
            }
            _ => Some(()),
        }
    }

    fn scalar(&mut self, value: &KernelScalar, depth: usize) -> Option<()> {
        self.charge(1)?;
        if depth >= 64 {
            return None;
        }
        match value {
            KernelScalar::Rational(_) => Some(()),
            KernelScalar::Sin(angle) | KernelScalar::Cos(angle) => self.numeric(angle, 0),
            KernelScalar::Sqrt(value) | KernelScalar::Neg(value) | KernelScalar::Inverse(value) => {
                self.scalar(value, depth + 1)
            }
            KernelScalar::Add(left, right) | KernelScalar::Mul(left, right) => {
                self.scalar(left, depth + 1)?;
                self.scalar(right, depth + 1)
            }
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => {
                self.boolean(condition)?;
                self.scalar(when_true, depth + 1)?;
                self.scalar(when_false, depth + 1)
            }
        }
    }
}

fn geometry(source: &ExactAggregate) -> Option<Geometry> {
    let mut geometry = Geometry { cells: 0 };
    let mut atoms = 0usize;
    for (entry, coefficients) in source {
        geometry.charge(1)?;
        for row in &entry.constraints {
            geometry.boolean(row)?;
        }
        atoms = atoms.checked_add(coefficients.len())?;
        if atoms > MAX_ATOMS {
            return None;
        }
        for (phase, scalar) in coefficients {
            geometry.scalar(scalar, 0)?;
            if !phase.is_algebraic() {
                return None;
            }
            for (monomial, _) in phase.terms() {
                geometry.charge(1)?;
                if monomial.variables().next().is_some() {
                    return None;
                }
            }
        }
    }
    Some(geometry)
}

/// Shared across all constant leaves of one universal equality obligation.
#[derive(Default)]
pub(super) struct ConstantBudget(Budget);

/// Exact constant value restricted to one nonzero rational/root monomial.
/// This is not a test-point certificate: callers must cover every cofactor.
pub(super) fn constant_monomial(
    source: &ExactAggregate,
    budget: &mut ConstantBudget,
) -> Option<(BigRational, BigRational)> {
    let geometry = geometry(source)?;
    spend(&mut budget.0.nodes, 1)?;
    spend(&mut budget.0.work, geometry.cells.max(1))?;
    let value = evaluate(source, &mut budget.0)?;
    if value.0.len() != 1 {
        return None;
    }
    let (mut power, mut scalar) = value.0.into_iter().next()?;
    if scalar < integer(0) {
        scalar = -scalar;
        power += DEGREE;
    }
    Some((scalar, BigRational::new(power.into(), ROOT_ORDER.into())))
}

/// A sufficient exact-zero certificate, not a numerical test. False includes
/// unsupported expressions and exhausted budgets; it cannot establish NEQ.
pub(super) fn constant_is_zero(source: &ExactAggregate, budget: &mut ConstantBudget) -> bool {
    let Some(geometry) = geometry(source) else {
        return false;
    };
    if spend(&mut budget.0.nodes, 1).is_none()
        || spend(&mut budget.0.work, geometry.cells.max(1)).is_none()
    {
        return false;
    }
    evaluate(source, &mut budget.0).is_some_and(|value| value.0.is_empty())
}
