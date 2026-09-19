//! Exact local elimination rules for bound HPS path variables.
//!
//! Each rule sums one Boolean path variable in closed form. This is variable
//! elimination, not global path enumeration: after a successful rule the
//! variable disappears before another path is considered.

use std::collections::BTreeSet;

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::symbolic::{
    BooleanPolynomial, Component, HistoryEntry, PhaseCoefficient, Scalar, Variable,
};

use super::simplify_component;

#[cfg(test)]
mod tests;

/// A closed-form rule available to the path-sum reducer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PathRule {
    /// `sum_y A = 2A` when `y` occurs nowhere in the summand.
    Vacuous,
    /// `sum_y (-1)^(y f) A = 2 [f=0] A`.
    Fourier,
    /// `sum_y i^(±y) (-1)^(y f) A` becomes one phase and a `sqrt(2)` factor.
    Omega,
}

/// Eliminates every path variable accepted by one of the exact local rules.
///
/// For example, the intermediate path in `H; H` has phase
/// `y0 * (x xor y1) / 2`. The Fourier rule replaces its sum by the guard
/// `x xor y1 = 0`; ordinary guard simplification then substitutes `y1 = x`.
pub(crate) fn reduce_path_sums(component: &mut Component) -> bool {
    if !simplify_component(component) {
        return false;
    }
    loop {
        // Visit every current path once before starting another fixed-point
        // round.  A successful elimination can make a path visited earlier in
        // this round reducible, so another round is still required.  Continuing
        // through the remaining paths avoids the former restart-after-every-
        // success behavior, which retried a large irreducible suffix O(n²)
        // times on measurement-heavy programs.
        let paths: Vec<_> = component.path_support.iter().rev().copied().collect();
        // Most paths that survive output slicing occur in a visible output or
        // a guard and therefore cannot be summed locally. Collect that set
        // once per round instead of rescanning every output expression for
        // every candidate path.
        let mut blocked = paths_in_guard_scalar_or_outputs(component);
        // These coherent rules require the path to be absent from history.
        // Eligible candidates are rechecked after earlier rewrites in a round.
        for entry in &component.output.history {
            let value = match entry {
                HistoryEntry::Write { value, .. } | HistoryEntry::Discard { value } => value,
            };
            blocked.extend(value.variables());
        }
        let mut reduced = false;
        for path in paths {
            let variable = Variable::Path(path);
            if blocked.contains(&variable) || !component.path_support.contains(&path) {
                continue;
            }
            if reduce_path(component, &variable) {
                reduced = true;
                if !simplify_component(component) {
                    return false;
                }
            }
        }
        if !reduced {
            return true;
        }
    }
}

impl PathRule {
    fn apply(self, component: &mut Component, variable: &Variable, profile: PhaseProfile) {
        match (self, profile) {
            (Self::Vacuous, PhaseProfile::Absent) => {
                remove_path(component, variable, Scalar::rational(integer(2)));
            }
            (Self::Fourier, PhaseProfile::Fourier(relation)) => {
                // Summing `1 + (-1)^relation` is two when the relation is
                // false and zero otherwise, hence the equation `relation=0`.
                component
                    .phase
                    .substitute(variable, &BooleanPolynomial::zero());
                component.guard.push(relation);
                remove_path(component, variable, Scalar::rational(integer(2)));
            }
            (Self::Omega, PhaseProfile::Omega { parity, sign }) => {
                component
                    .phase
                    .substitute(variable, &BooleanPolynomial::zero());
                let (constant, coefficient) = match sign {
                    OmegaSign::Positive => (ratio(1, 8), ratio(-1, 4)),
                    OmegaSign::Negative => (ratio(-1, 8), ratio(1, 4)),
                };
                component.phase.add_boolean(
                    &BooleanPolynomial::one(),
                    PhaseCoefficient::rational(constant),
                );
                component
                    .phase
                    .add_boolean(&parity, PhaseCoefficient::rational(coefficient));
                remove_path(
                    component,
                    variable,
                    Scalar::sqrt(Scalar::rational(integer(2))),
                );
            }
            _ => unreachable!("a path rule is selected from its matching profile"),
        }
    }
}

/// Classifies one path once, then dispatches to the matching closed-form rule.
/// This avoids rescanning the component's phase separately for every rule.
fn reduce_path(component: &mut Component, variable: &Variable) -> bool {
    // A previous elimination in the same round can introduce `variable` into
    // an output or scalar. Recheck dynamically even though the round-level
    // blocked set filtered its original state.
    if occurs_in_guard_scalar_or_outputs(component, variable) {
        return false;
    }
    let profile = phase_profile(component, variable);
    if matches!(profile, PhaseProfile::Unsupported) {
        return false;
    }
    let history_is_absent = component.output.history.iter().all(|entry| {
        let value = match entry {
            HistoryEntry::Write { value, .. } | HistoryEntry::Discard { value } => value,
        };
        !value.variables().contains(variable)
    });
    let rule = match (&profile, history_is_absent) {
        (PhaseProfile::Absent, true) => PathRule::Vacuous,
        (PhaseProfile::Fourier(_), true) => PathRule::Fourier,
        (PhaseProfile::Omega { .. }, true) => PathRule::Omega,
        _ => return false,
    };
    rule.apply(component, variable, profile);
    true
}

/// The complete supported dependence of a phase on one path variable.
enum PhaseProfile {
    Absent,
    Fourier(BooleanPolynomial),
    Omega {
        parity: BooleanPolynomial,
        sign: OmegaSign,
    },
    Unsupported,
}

#[derive(Clone, Copy)]
enum OmegaSign {
    Positive,
    Negative,
}

/// Classifies `phase = phase_without_y + y * coefficient` without expanding
/// any other variable. Non-constant terms must have coefficient one half so
/// that they denote the Boolean parity in `(-1)^(y f)`.
fn phase_profile(component: &Component, variable: &Variable) -> PhaseProfile {
    let mut present = false;
    let mut constant = integer(0);
    let mut parity = BooleanPolynomial::zero();

    for (value, coefficient) in component.phase.selectors() {
        if !value.variables().contains(variable) {
            continue;
        }
        present = true;
        let Some(coefficient) = coefficient.as_rational() else {
            return PhaseProfile::Unsupported;
        };
        let low = value.substitute(variable, &BooleanPolynomial::zero());
        let high = value.substitute(variable, &BooleanPolynomial::one());
        if coefficient == ratio(1, 2) {
            // c*(B1-B0) == (B1 XOR B0)/2 modulo one. This
            // cofactor identity works on the DAG without distributing ANF.
            parity = parity.xor(&low.xor(&high));
        } else if low.is_zero() && high.is_one() {
            constant += coefficient;
        } else {
            return PhaseProfile::Unsupported;
        }
    }
    constant = PhaseCoefficient::rational(constant).as_rational().unwrap();

    if !present {
        return PhaseProfile::Absent;
    }
    if constant == integer(0) {
        PhaseProfile::Fourier(parity)
    } else if constant == ratio(1, 2) {
        PhaseProfile::Fourier(parity.complement())
    } else if constant == ratio(1, 4) {
        PhaseProfile::Omega {
            parity,
            sign: OmegaSign::Positive,
        }
    } else if constant == ratio(3, 4) {
        PhaseProfile::Omega {
            parity,
            sign: OmegaSign::Negative,
        }
    } else {
        PhaseProfile::Unsupported
    }
}

/// Rejects dependencies that cannot be eliminated by any local rule.
fn occurs_in_guard_scalar_or_outputs(component: &Component, variable: &Variable) -> bool {
    component
        .guard
        .iter()
        .any(|guard| guard.variables().contains(variable))
        || scalar_depends_on(&component.scalar, variable)
        || component
            .output
            .quantum
            .values()
            .chain(component.output.classical.values())
            .any(|value| value.variables().contains(variable))
}

fn paths_in_guard_scalar_or_outputs(component: &Component) -> BTreeSet<Variable> {
    let mut variables = BTreeSet::new();
    for guard in &component.guard {
        variables.extend(guard.variables());
    }
    collect_scalar_variables(&component.scalar, &mut variables);
    for value in component
        .output
        .quantum
        .values()
        .chain(component.output.classical.values())
    {
        variables.extend(value.variables());
    }
    variables
}

fn collect_scalar_variables(scalar: &Scalar, variables: &mut BTreeSet<Variable>) {
    match scalar {
        Scalar::Rational(_) | Scalar::Sin(_) | Scalar::Cos(_) => {}
        Scalar::Sqrt(value) | Scalar::Neg(value) | Scalar::Inverse(value) => {
            collect_scalar_variables(value, variables);
        }
        Scalar::Add(left, right) | Scalar::Mul(left, right) => {
            collect_scalar_variables(left, variables);
            collect_scalar_variables(right, variables);
        }
        Scalar::Select {
            condition,
            when_true,
            when_false,
        } => {
            variables.extend(condition.variables());
            collect_scalar_variables(when_true, variables);
            collect_scalar_variables(when_false, variables);
        }
    }
}

/// Tests exact dependence through the scalar's existing substitution rules.
/// Equal cofactors mean the Boolean path is absent semantically, including a
/// reduced selection such as `select(y, a, a)`.
fn scalar_depends_on(scalar: &Scalar, variable: &Variable) -> bool {
    scalar.substitute(variable, &BooleanPolynomial::zero())
        != scalar.substitute(variable, &BooleanPolynomial::one())
}

fn remove_path(component: &mut Component, variable: &Variable, factor: Scalar) {
    let Variable::Path(path) = variable else {
        unreachable!("path rules receive only bound path variables")
    };
    component.path_support.remove(path);
    // Admission proved equality of the scalar's two cofactors, not syntactic
    // absence. Keep one cofactor so no eliminated binder survives in a shared
    // Boolean selector inside the stored scalar expression.
    component.scalar = component
        .scalar
        .substitute(variable, &BooleanPolynomial::zero());
    component.scalar = factor.multiply(component.scalar.clone());
}

fn integer(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn ratio(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}
