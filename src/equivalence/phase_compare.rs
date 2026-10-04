//! Rational phase queries and evaluation restored from FSE-Ver.
use std::collections::BTreeMap;
use num_bigint::BigInt;
use num_rational::BigRational;
use crate::ir::Qubit;
use crate::symbolic::{BooleanPolynomial, PhasePolynomial, Variable};
use super::model_witness::evaluate_boolean;
pub(super) type RationalPhase = BTreeMap<BooleanPolynomial, BigRational>;
pub(super) fn rational_phase_difference(
    left: &PhasePolynomial,
    right: &PhasePolynomial,
) -> Option<RationalPhase> {
    let mut difference = BTreeMap::new();
    for (selector, coefficient) in left.selectors() {
        difference.insert(selector, coefficient.as_rational()?);
    }
    for (selector, coefficient) in right.selectors() {
        let value = difference.remove(&selector).unwrap_or_else(rational_zero)
            - coefficient.as_rational()?;
        let value = modulo_one(value);
        if value != rational_zero() {
            difference.insert(selector, value);
        }
    }
    difference.retain(|_, coefficient| {
        *coefficient = modulo_one(coefficient.clone());
        *coefficient != rational_zero()
    });
    Some(difference)
}
pub(super) fn phase_variation_query(
    phase: &RationalPhase,
    positions: &BTreeMap<Qubit, usize>,
) -> Option<String> {
    let denominator = phase.values().fold(BigInt::from(1), |current, value| {
        lcm(current, value.denom().clone())
    });
    let coefficients = phase
        .iter()
        .filter(|(selector, _)| !selector.is_one())
        .map(|(monomial, coefficient)| {
            let integer = coefficient.numer() * (&denominator / coefficient.denom());
            (monomial.clone(), positive_mod(integer, &denominator))
        })
        .filter(|(_, coefficient)| coefficient != &BigInt::from(0))
        .collect::<Vec<_>>();
    if coefficients.is_empty() {
        return None;
    }
    let maximum = BigInt::from(coefficients.len()) * (&denominator - 1);
    let width = bit_width(if maximum > denominator {
        &maximum
    } else {
        &denominator
    });
    let value = |namespace: &str| -> Option<String> {
        let terms = coefficients
            .iter()
            .map(|(monomial, coefficient)| {
                Some(format!(
                    "(ite {} (_ bv{} {}) (_ bv0 {}))",
                    smt_boolean(monomial, positions, namespace)?,
                    coefficient,
                    width,
                    width
                ))
            })
            .collect::<Option<Vec<_>>>()?;
        let sum = terms
            .into_iter()
            .fold(format!("(_ bv0 {width})"), |left, right| {
                format!("(bvadd {left} {right})")
            });
        Some(format!("(bvurem {sum} (_ bv{} {}))", denominator, width))
    };
    let assertion = format!("(distinct {} {})", value("x")?, value("z")?);
    Some(smt_script(
        declarations(positions.len(), &["x", "z"]),
        assertion,
        &[],
    ))
}
pub(super) fn evaluate_phase(phase: &RationalPhase, bindings: &BTreeMap<Variable, bool>) -> BigRational {
    modulo_one(
        phase
            .iter()
            .filter(|(selector, _)| evaluate_boolean(selector, bindings))
            .fold(rational_zero(), |sum, (_, coefficient)| sum + coefficient),
    )
}
pub(super) fn modulo_one(value: BigRational) -> BigRational {
    BigRational::new(
        positive_mod(value.numer().clone(), value.denom()),
        value.denom().clone(),
    )
}
fn positive_mod(value: BigInt, modulus: &BigInt) -> BigInt {
    let remainder = value % modulus;
    if remainder < BigInt::from(0) {
        remainder + modulus
    } else {
        remainder
    }
}
pub(super) fn lcm(left: BigInt, right: BigInt) -> BigInt {
    let gcd = gcd(left.clone(), right.clone());
    left / gcd * right
}
fn gcd(mut left: BigInt, mut right: BigInt) -> BigInt {
    while right != BigInt::from(0) {
        let remainder = left % &right;
        left = right;
        right = remainder;
    }
    left
}
pub(super) fn bit_width(value: &BigInt) -> u64 {
    value.magnitude().bits().max(1)
}
pub(super) fn rational_zero() -> BigRational {
    BigRational::from_integer(BigInt::from(0))
}
fn declarations(width: usize, namespaces: &[&str]) -> String {
    namespaces
        .iter()
        .flat_map(|namespace| {
            (0..width).map(move |index| format!("(declare-fun {namespace}{index} () Bool)\n"))
        })
        .collect()
}
fn smt_boolean(
    polynomial: &BooleanPolynomial,
    positions: &BTreeMap<Qubit, usize>,
    namespace: &str,
) -> Option<String> {
    polynomial.smt_expression(|variable| match variable {
        Variable::Input(qubit) => positions
            .get(qubit)
            .map(|position| format!("{namespace}{position}")),
        Variable::Path(_) => None,
    })
}
fn smt_or(terms: &[String]) -> String {
    smt_fold(terms, "or", "false")
}
fn smt_and(terms: &[String]) -> String {
    smt_fold(terms, "and", "true")
}
fn smt_fold(terms: &[String], operator: &str, identity: &str) -> String {
    terms
        .iter()
        .cloned()
        .fold(identity.to_owned(), |left, right| {
            format!("({operator} {left} {right})")
        })
}
fn smt_script(declarations: String, assertion: String, values: &[String]) -> String {
    let get_values = if values.is_empty() {
        String::new()
    } else {
        format!("(get-value ({}))\n", values.join(" "))
    };
    format!(
        "(set-logic QF_BV)\n(set-option :produce-models true)\n{declarations}(assert {assertion})\n(check-sat)\n{get_values}"
    )
}

#[cfg(test)]
mod tests;
