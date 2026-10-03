//! Exact admission of constant scalar trees into the closed cyclotomic field.
//! No Boolean selection, numeric input, SMT encoding, or sqrt(3) extension.
//! Refusal is incompleteness, never a numeric approximation or zero value.
use super::KernelScalar;
use super::cyclotomic::{Budget, Cyclotomic, ORDER};
use super::exact_trig;
use crate::symbolic::PhaseCoefficient;
use num_bigint::BigInt;
use num_rational::BigRational;

const MAX_DEPTH: usize = 64;
const MAX_LITERAL_BITS: u64 = 4096;

fn integer(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}

fn admitted(r: &BigRational) -> bool {
    r.numer().bits() <= MAX_LITERAL_BITS && r.denom().bits() <= MAX_LITERAL_BITS
}

fn literal(r: BigRational, budget: &mut Budget) -> Option<Cyclotomic> {
    if !admitted(&r) {
        return None;
    }
    Cyclotomic::from_terms([(0, r)], budget)
}

fn rational_root(r: &BigRational) -> Option<BigRational> {
    if !admitted(r) || r < &integer(0) {
        return None;
    }
    let n = r.numer().sqrt();
    let d = r.denom().sqrt();
    (&n * &n == *r.numer() && &d * &d == *r.denom()).then(|| BigRational::new(n, d))
}

pub(super) fn lower(scalar: &KernelScalar, budget: &mut Budget) -> Option<Cyclotomic> {
    lower_at(scalar, budget, 0)
}

fn lower_at(scalar: &KernelScalar, budget: &mut Budget, depth: usize) -> Option<Cyclotomic> {
    budget.charge(1)?;
    if depth >= MAX_DEPTH {
        return None;
    }
    match scalar {
        KernelScalar::Rational(r) => literal(r.clone(), budget),
        KernelScalar::Neg(a) => {
            let value = lower_at(a, budget, depth + 1)?;
            value.multiply(&literal(integer(-1), budget)?, budget)
        }
        KernelScalar::Add(a, b) | KernelScalar::Mul(a, b) => {
            // Validate both operands even when a zero could annihilate the result.
            let left = lower_at(a, budget, depth + 1)?;
            let right = lower_at(b, budget, depth + 1)?;
            if matches!(scalar, KernelScalar::Add(..)) {
                left.add(&right, budget)
            } else {
                left.multiply(&right, budget)
            }
        }
        KernelScalar::Inverse(a) => {
            let KernelScalar::Rational(r) = a.as_ref() else {
                return None;
            };
            if !admitted(r) || *r == integer(0) {
                return None;
            }
            literal(r.recip(), budget)
        }
        KernelScalar::Sqrt(a) => {
            let KernelScalar::Rational(r) = a.as_ref() else {
                return None;
            };
            if !admitted(r) || r < &integer(0) {
                return None;
            }
            if let Some(root) = rational_root(r) {
                return literal(root, budget);
            }
            // sqrt(r) = sqrt(2r)/2 * sqrt(2), with an exactly checked rational
            // sqrt(2r). The two unit roots below equal positive sqrt(2).
            let coefficient = rational_root(&(r * BigInt::from(2)))? / integer(2);
            Cyclotomic::from_terms(
                [
                    (ORDER / 8, coefficient.clone()),
                    (3 * ORDER / 8, -coefficient),
                ],
                budget,
            )
        }
        KernelScalar::Sin(angle) | KernelScalar::Cos(angle) => {
            let mut nodes = 64;
            if !exact_trig::admitted(angle, &mut nodes) {
                return None;
            }
            budget.charge(64 - nodes)?;
            let sine = matches!(scalar, KernelScalar::Sin(_));
            // Existing exact pi/6 constants may reduce to a rational. A sqrt(3)
            // result still refuses through the restricted Sqrt branch above.
            if let Some(normal) = exact_trig::normalize(angle, sine) {
                return lower_at(&normal, budget, depth + 1);
            }
            let root = Cyclotomic::from_phase(
                &PhaseCoefficient::angle(angle.clone(), integer(1)),
                budget,
            )?;
            let mut conjugate = root.conjugate(budget)?;
            if sine {
                conjugate = conjugate.multiply(&literal(integer(-1), budget)?, budget)?;
            }
            let sum = root.add(&conjugate, budget)?;
            // cos=(z+conj(z))/2; sin=(z-conj(z))/(2i).
            let scale = Cyclotomic::from_terms(
                [(
                    if sine { 3 * ORDER / 4 } else { 0 },
                    BigRational::new(1.into(), 2.into()),
                )],
                budget,
            )?;
            sum.multiply(&scale, budget)
        }
        KernelScalar::Select { .. } => None,
    }
}

#[cfg(test)]
mod tests;
