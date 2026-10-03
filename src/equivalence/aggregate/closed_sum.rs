//! Complete small closed sums, without SMT, factorization, or scheduling.
//! Prepare every expression before evaluating any guard. Both Shannon branches
//! share one budget; refusal discards the complete result, never just a tail.
use super::constant_scalar;
use super::cyclotomic::{Budget, Cyclotomic};
use super::{KernelBooleanPolynomial, KernelPhasePolynomial, KernelScalar, KernelVariable};
use crate::symbolic::{BooleanExpression, BooleanPolynomial};
use num_rational::BigRational;
use std::collections::{BTreeMap, BTreeSet};

const MAX_PATHS: usize = 16;
const MAX_DEPTH: usize = 64;

enum Boolean {
    Constant(bool),
    Bit(usize),
    Xor(Vec<Self>),
    And(Vec<Self>),
}

impl Boolean {
    fn prepare(
        p: &BooleanPolynomial,
        paths: &BTreeMap<KernelVariable, usize>,
        budget: &mut Budget,
        depth: usize,
    ) -> Option<Self> {
        budget.charge(1)?;
        if depth >= MAX_DEPTH {
            return None;
        }
        Some(match p.expression() {
            BooleanExpression::Constant(b) => Self::Constant(*b),
            BooleanExpression::Variable(v) => {
                Self::Bit(*paths.get(&KernelVariable::from_graph_variable(v))?)
            }
            BooleanExpression::Xor(xs) | BooleanExpression::And(xs) => {
                // Deliberately bounded tree expansion; no implicit unbudgeted
                // ANF conversion or recursive walk of arbitrarily deep graphs.
                let values = xs
                    .iter()
                    .map(|p| Self::prepare(p, paths, budget, depth + 1))
                    .collect::<Option<Vec<_>>>()?;
                if matches!(p.expression(), BooleanExpression::Xor(_)) {
                    Self::Xor(values)
                } else {
                    Self::And(values)
                }
            }
        })
    }

    fn evaluate(&self, bits: &[bool], budget: &mut Budget) -> Option<bool> {
        budget.charge(1)?;
        Some(match self {
            Self::Constant(b) => *b,
            Self::Bit(i) => bits[*i],
            Self::Xor(xs) => {
                let mut value = false;
                for x in xs {
                    value ^= x.evaluate(bits, budget)?;
                }
                value
            }
            Self::And(xs) => {
                let mut value = true;
                for x in xs {
                    value &= x.evaluate(bits, budget)?;
                }
                value
            }
        })
    }
}

enum Weight {
    Constant(Cyclotomic),
    Neg(Box<Self>),
    Add(Box<Self>, Box<Self>),
    Mul(Box<Self>, Box<Self>),
    Select(Boolean, Box<Self>, Box<Self>),
}

impl Weight {
    fn prepare(
        s: &KernelScalar,
        paths: &BTreeMap<KernelVariable, usize>,
        budget: &mut Budget,
        depth: usize,
    ) -> Option<Self> {
        budget.charge(1)?;
        if depth >= MAX_DEPTH {
            return None;
        }
        Some(match s {
            KernelScalar::Neg(a) => {
                Self::Neg(Box::new(Self::prepare(a, paths, budget, depth + 1)?))
            }
            KernelScalar::Add(a, b) | KernelScalar::Mul(a, b) => {
                let a = Box::new(Self::prepare(a, paths, budget, depth + 1)?);
                let b = Box::new(Self::prepare(b, paths, budget, depth + 1)?);
                if matches!(s, KernelScalar::Add(..)) {
                    Self::Add(a, b)
                } else {
                    Self::Mul(a, b)
                }
            }
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => Self::Select(
                Boolean::prepare(&condition.as_graph(), paths, budget, 0)?,
                Box::new(Self::prepare(when_true, paths, budget, depth + 1)?),
                Box::new(Self::prepare(when_false, paths, budget, depth + 1)?),
            ),
            _ => Self::Constant(constant_scalar::lower(s, budget)?),
        })
    }

    fn evaluate(&self, bits: &[bool], budget: &mut Budget) -> Option<Cyclotomic> {
        budget.charge(1)?;
        match self {
            Self::Constant(c) => {
                budget.charge(c.terms().len())?;
                Some(c.clone())
            }
            Self::Neg(a) => a.evaluate(bits, budget)?.multiply(
                &Cyclotomic::from_terms([(0, BigRational::from_integer((-1).into()))], budget)?,
                budget,
            ),
            Self::Add(a, b) => a
                .evaluate(bits, budget)?
                .add(&b.evaluate(bits, budget)?, budget),
            Self::Mul(a, b) => a
                .evaluate(bits, budget)?
                .multiply(&b.evaluate(bits, budget)?, budget),
            Self::Select(condition, a, b) => if condition.evaluate(bits, budget)? {
                a
            } else {
                b
            }
            .evaluate(bits, budget),
        }
    }
}

/// Sum amplitudes, not probabilities. Inputs must be closed over at most 16
/// declared bound paths. Unused paths remain present and supply factors of 2.
pub(super) fn evaluate(
    paths: &BTreeSet<KernelVariable>,
    constraints: &[KernelBooleanPolynomial],
    coefficient: &KernelScalar,
    phase: &KernelPhasePolynomial,
    budget: &mut Budget,
) -> Option<Cyclotomic> {
    budget.charge(1)?;
    if paths.len() > MAX_PATHS || paths.iter().any(|p| !p.is_bound_path()) {
        return None;
    }
    let positions = paths
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, p)| (p, i))
        .collect();
    let guards = constraints
        .iter()
        .map(|p| Boolean::prepare(&p.as_graph(), &positions, budget, 0))
        .collect::<Option<Vec<_>>>()?;
    let weight = Weight::prepare(coefficient, &positions, budget, 0)?;
    let mut phases = Vec::new();
    for (selector, coefficient) in phase.selectors() {
        budget.charge(1)?;
        phases.push((
            Boolean::prepare(&selector.as_graph(), &positions, budget, 0)?,
            Cyclotomic::from_phase(&coefficient, budget)?,
        ));
    }
    let mut bits = vec![false; paths.len()];
    sum(0, &mut bits, &guards, &weight, &phases, budget)
}

fn sum(
    index: usize,
    bits: &mut [bool],
    guards: &[Boolean],
    weight: &Weight,
    phases: &[(Boolean, Cyclotomic)],
    budget: &mut Budget,
) -> Option<Cyclotomic> {
    budget.charge(1)?;
    if index < bits.len() {
        bits[index] = false;
        let zero = sum(index + 1, bits, guards, weight, phases, budget)?;
        bits[index] = true;
        let one = sum(index + 1, bits, guards, weight, phases, budget)?;
        return zero.add(&one, budget);
    }
    for guard in guards {
        if guard.evaluate(bits, budget)? {
            return Cyclotomic::from_terms([], budget);
        }
    }
    let mut value = weight.evaluate(bits, budget)?;
    for (selector, root) in phases {
        if selector.evaluate(bits, budget)? {
            value = value.multiply(root, budget)?;
        }
    }
    Some(value)
}

#[cfg(test)]
mod tests;
