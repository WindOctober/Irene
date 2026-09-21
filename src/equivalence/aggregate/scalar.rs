//! Exact simplification of well-defined real density-kernel coefficients.
//! This pass preserves unsupported expressions; it is not a domain validator.
//! Products are flattened but never distributed over sums.
use std::collections::BTreeMap;

use num_rational::BigRational;

use super::exact_trig;
use super::{KernelBooleanPolynomial, KernelScalar, MAX_BOOLEAN_TERMS};

const MAX_SCALAR_NODES: usize = 100_000;

pub(super) fn scalar_within_budget(scalar: &KernelScalar) -> bool {
    scalar_conditions_within_budget(scalar, |condition| {
        condition.term_count() <= MAX_BOOLEAN_TERMS
    })
}

pub(super) fn scalar_conditions_within_budget(
    scalar: &KernelScalar,
    mut condition_fits: impl FnMut(&KernelBooleanPolynomial) -> bool,
) -> bool {
    let mut pending = vec![scalar];
    let mut nodes = 0usize;
    while let Some(current) = pending.pop() {
        let Some(next_nodes) = nodes.checked_add(1) else {
            return false;
        };
        nodes = next_nodes;
        if nodes > MAX_SCALAR_NODES {
            return false;
        }
        match current {
            KernelScalar::Rational(_) | KernelScalar::Sin(_) | KernelScalar::Cos(_) => {}
            KernelScalar::Sqrt(value) | KernelScalar::Neg(value) | KernelScalar::Inverse(value) => {
                pending.push(value)
            }
            KernelScalar::Add(left, right) | KernelScalar::Mul(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => {
                if !condition_fits(condition) {
                    return false;
                }
                pending.push(when_true);
                pending.push(when_false);
            }
        }
    }
    true
}

/// Canonicalizes the exact scalar products produced by density doubling.
pub(super) fn normalize_scalar(value: KernelScalar) -> KernelScalar {
    match value {
        KernelScalar::Sin(angle) => {
            exact_trig::normalize(&angle, true).unwrap_or(KernelScalar::Sin(angle))
        }
        KernelScalar::Cos(angle) => {
            exact_trig::normalize(&angle, false).unwrap_or(KernelScalar::Cos(angle))
        }
        KernelScalar::Mul(left, right) => {
            normalize_product(vec![normalize_scalar(*left), normalize_scalar(*right)])
        }
        KernelScalar::Add(left, right) => {
            normalize_sum(vec![normalize_scalar(*left), normalize_scalar(*right)])
        }
        KernelScalar::Sqrt(value) => normalize_sqrt(normalize_scalar(*value)),
        KernelScalar::Neg(value) => normalize_product(vec![
            KernelScalar::Rational(integer(-1)),
            normalize_scalar(*value),
        ]),
        KernelScalar::Inverse(value) => match normalize_scalar(*value) {
            KernelScalar::Rational(value) if value != BigRational::from_integer(0.into()) => {
                KernelScalar::Rational(value.recip())
            }
            KernelScalar::Sqrt(value) => match value.as_ref() {
                KernelScalar::Rational(value) if value > &integer(0) => {
                    normalize_sqrt(KernelScalar::Rational(value.recip()))
                }
                _ => KernelScalar::Inverse(Box::new(KernelScalar::Sqrt(value))),
            },
            value => KernelScalar::Inverse(Box::new(value)),
        },
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => {
            let when_true = normalize_scalar(*when_true);
            let when_false = normalize_scalar(*when_false);
            if condition.is_zero() {
                when_false
            } else if condition.is_one() || when_true == when_false {
                when_true
            } else {
                KernelScalar::Select {
                    condition,
                    when_true: Box::new(when_true),
                    when_false: Box::new(when_false),
                }
            }
        }
        value => value,
    }
}

/// Flattens a real product, combines its exact rational magnitude, and uses
/// only radical identities whose non-negativity side condition is proved.
pub(super) fn normalize_product(values: Vec<KernelScalar>) -> KernelScalar {
    let mut pending = values;
    let mut rational = integer(1);
    let mut rational_radicand = integer(1);
    let mut has_rational_radical = false;
    let mut factors = Vec::new();

    while let Some(value) = pending.pop() {
        match value {
            KernelScalar::Mul(left, right) => {
                pending.push(*left);
                pending.push(*right);
            }
            KernelScalar::Rational(value) => rational *= value,
            KernelScalar::Sqrt(value) => match value.as_ref() {
                KernelScalar::Rational(value) if value >= &integer(0) => {
                    has_rational_radical = true;
                    rational_radicand *= value;
                }
                _ => factors.push(KernelScalar::Sqrt(value)),
            },
            value => factors.push(value),
        }
    }
    if rational == integer(0) {
        return KernelScalar::Rational(integer(0));
    }

    // sqrt(r)^2 = r is used only when r is known non-negative. This also
    // handles roots of density weights such as sums of syntactic squares.
    factors.sort();
    let mut paired = Vec::with_capacity(factors.len());
    let mut position = 0;
    while position < factors.len() {
        let end = factors[position..]
            .iter()
            .position(|value| value != &factors[position])
            .map_or(factors.len(), |offset| position + offset);
        let count = end - position;
        if let KernelScalar::Sqrt(root) = &factors[position]
            && scalar_is_provably_nonnegative(root)
        {
            for _ in 0..count / 2 {
                paired.push((**root).clone());
            }
            if count % 2 == 1 {
                paired.push(factors[position].clone());
            }
        } else {
            paired.extend(factors[position..end].iter().cloned());
        }
        position = end;
    }
    factors = paired;

    if has_rational_radical {
        // For real rational a and non-negative r,
        // a*sqrt(r) = sign(a)*sqrt(a^2*r). Absorbing the magnitude makes
        // 2*sqrt(1/8) and sqrt(1/2) share one exact representation.
        let negative = rational < integer(0);
        let radicand = rational.clone() * rational * rational_radicand;
        let root = normalize_sqrt(KernelScalar::Rational(radicand));
        rational = if negative { integer(-1) } else { integer(1) };
        match root {
            KernelScalar::Rational(value) => rational *= value,
            value => factors.push(value),
        }
    }

    // Roots collapsed above can expose products. Flatten once more; unlike a
    // distributive rewrite, this cannot increase the number of scalar atoms.
    let mut flattened = Vec::new();
    while let Some(value) = factors.pop() {
        match value {
            KernelScalar::Mul(left, right) => {
                factors.push(*left);
                factors.push(*right);
            }
            KernelScalar::Rational(value) => rational *= value,
            value => flattened.push(value),
        }
    }
    if rational == integer(0) {
        return KernelScalar::Rational(integer(0));
    }
    flattened.sort();
    if rational != integer(1) || flattened.is_empty() {
        flattened.insert(0, KernelScalar::Rational(rational));
    }
    make_product(flattened)
}

/// Collects coefficients of identical exact scalar atoms without distributing
/// products. This proves cancellations such as `a + (-a) = 0` but leaves
/// algebraically different symbolic/trigonometric expressions distinct.
fn normalize_sum(values: Vec<KernelScalar>) -> KernelScalar {
    let mut pending = values;
    let mut coefficients: BTreeMap<Option<KernelScalar>, BigRational> = BTreeMap::new();
    while let Some(value) = pending.pop() {
        match value {
            KernelScalar::Add(left, right) => {
                pending.push(*left);
                pending.push(*right);
            }
            value => {
                let (coefficient, base) = split_scalar_coefficient(value);
                *coefficients.entry(base).or_insert_with(|| integer(0)) += coefficient;
            }
        }
    }

    let mut terms = Vec::new();
    for (base, coefficient) in coefficients {
        if coefficient == integer(0) {
            continue;
        }
        terms.push(match base {
            None => KernelScalar::Rational(coefficient),
            Some(base) => normalize_product(vec![KernelScalar::Rational(coefficient), base]),
        });
    }
    match terms.len() {
        0 => KernelScalar::Rational(integer(0)),
        1 => terms.pop().expect("one scalar term exists"),
        _ => {
            terms.sort();
            make_sum(terms)
        }
    }
}

fn split_scalar_coefficient(value: KernelScalar) -> (BigRational, Option<KernelScalar>) {
    match value {
        KernelScalar::Rational(value) => (value, None),
        value => {
            let mut factors = Vec::new();
            collect_product(value, &mut factors);
            factors.sort();
            let coefficient = if let Some(KernelScalar::Rational(_)) = factors.first() {
                match factors.remove(0) {
                    KernelScalar::Rational(value) => value,
                    _ => unreachable!("the first factor was matched as rational"),
                }
            } else {
                integer(1)
            };
            (coefficient, Some(make_product(factors)))
        }
    }
}

fn collect_product(value: KernelScalar, factors: &mut Vec<KernelScalar>) {
    match value {
        KernelScalar::Mul(left, right) => {
            collect_product(*left, factors);
            collect_product(*right, factors);
        }
        value => factors.push(value),
    }
}

fn make_product(mut factors: Vec<KernelScalar>) -> KernelScalar {
    debug_assert!(!factors.is_empty());
    let first = factors.remove(0);
    factors.into_iter().fold(first, |left, right| {
        KernelScalar::Mul(Box::new(left), Box::new(right))
    })
}

fn make_sum(mut terms: Vec<KernelScalar>) -> KernelScalar {
    debug_assert!(!terms.is_empty());
    let first = terms.remove(0);
    terms.into_iter().fold(first, |left, right| {
        KernelScalar::Add(Box::new(left), Box::new(right))
    })
}

fn normalize_sqrt(value: KernelScalar) -> KernelScalar {
    match value {
        KernelScalar::Rational(value) if value == integer(0) => KernelScalar::Rational(integer(0)),
        KernelScalar::Rational(value) if value == integer(1) => KernelScalar::Rational(integer(1)),
        KernelScalar::Rational(value) if value > integer(0) => {
            let numerator = value.numer().sqrt();
            let denominator = value.denom().sqrt();
            if &numerator * &numerator == *value.numer()
                && &denominator * &denominator == *value.denom()
            {
                KernelScalar::Rational(BigRational::new(numerator, denominator))
            } else {
                KernelScalar::Sqrt(Box::new(KernelScalar::Rational(value)))
            }
        }
        value => KernelScalar::Sqrt(Box::new(value)),
    }
}

fn scalar_is_provably_nonnegative(value: &KernelScalar) -> bool {
    match value {
        KernelScalar::Rational(value) => value >= &integer(0),
        KernelScalar::Sqrt(_) => true,
        KernelScalar::Add(left, right) => {
            scalar_is_provably_nonnegative(left) && scalar_is_provably_nonnegative(right)
        }
        KernelScalar::Mul(left, right) if left == right => true,
        KernelScalar::Mul(left, right) => {
            scalar_is_provably_nonnegative(left) && scalar_is_provably_nonnegative(right)
        }
        KernelScalar::Select {
            when_true,
            when_false,
            ..
        } => {
            scalar_is_provably_nonnegative(when_true) && scalar_is_provably_nonnegative(when_false)
        }
        KernelScalar::Sin(_)
        | KernelScalar::Cos(_)
        | KernelScalar::Neg(_)
        | KernelScalar::Inverse(_) => false,
    }
}

pub(super) fn integer(value: i64) -> BigRational {
    BigRational::from_integer(value.into())
}

pub(super) fn ratio(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(numerator.into(), denominator.into())
}

#[cfg(test)]
mod tests;
