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

mod joint_phase;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod history_tests;

#[cfg(test)]
mod history_phase_tests;

/// Cancels common Clifford phases that depend only on hidden history values.
///
/// Multiplying an extended state by `(-1)^f(h)` applies a diagonal unitary to
/// the hidden environment `h`; tracing that environment is invariant under
/// the unitary. We greedily toggle the frequent linear and quadratic forms
/// `h_i/2` and `h_i*h_j/2` only when doing so strictly shortens the exact phase
/// polynomial. Every accepted step is semantic, while the size test merely
/// chooses a useful representative.
fn cancel_half_turn_history_phases(component: &mut Component) {
    const HISTORY_LIMIT: usize = 64;

    let history = component
        .output
        .history
        .iter()
        .map(HistoryEntry::value)
        .filter(|value| value.is_affine())
        .cloned()
        .collect::<Vec<_>>();
    // A large history must not suppress the linear single-history scan.
    // Only the genuinely quadratic pair search retains a scheduling limit.
    let pairs = (0..history.len())
        .flat_map(|left| {
            let history = &history;
            (left + 1..history.len()).map(move |right| history[left].and(&history[right]))
        })
        .take(if history.len() <= HISTORY_LIMIT {
            usize::MAX
        } else {
            0
        });
    component
        .phase
        .shorten_half_turns(history.iter().cloned().chain(pairs));
}

// TODO: Unify the duplicated vacuous/Fourier/Omega rule logic with
// equivalence::aggregate (including its graph reducer). Share the algebraic
// rules while retaining layer-specific applicability checks and adapters for
// Component and WorkingTerm; history elimination remains HPS-specific.
/// A closed-form rule available to the path-sum reducer.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PathRule {
    /// `sum_y A = 2A` when `y` occurs nowhere in the summand.
    Vacuous,
    /// `sum_y (-1)^(y f) A = 2 [f=0] A`.
    Fourier,
    /// `sum_y i^(±y) (-1)^(y f) A` becomes one phase and a `sqrt(2)` factor.
    Omega,
    /// A hidden affine history bit `y xor f` separates the two values of `y`.
    History,
}

/// Eliminates every path variable accepted by one of the exact local rules.
///
/// With `allow_history`, preserves the reduced density map rather than the
/// full history-indexed amplitude. The caller must provide a single component
/// or separately certify isolation from all siblings before and after rewriting.
///
/// For example, the intermediate path in `H; H` has phase
/// `y0 * (x xor y1) / 2`. The Fourier rule replaces its sum by the guard
/// `x xor y1 = 0`; ordinary guard simplification then substitutes `y1 = x`.
pub(crate) fn reduce_path_sums(component: &mut Component, allow_history: bool) -> bool {
    if !simplify_component(component) {
        return false;
    }
    if allow_history {
        cancel_half_turn_history_phases(component);
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
        // Fourier/Omega require no history occurrence; History requires no
        // phase occurrence. Cache this necessary condition once per round.
        // A rewrite may unblock an earlier path, which is reconsidered in
        // the next round. Eligible candidates still get the dynamic checks
        // in reduce_path, so stale information can only defer a rewrite.
        let phase_variables = component.phase.variables();
        for variable in component
            .output
            .history
            .iter()
            .map(HistoryEntry::value)
            .flat_map(BooleanPolynomial::variables)
        {
            if !allow_history || phase_variables.contains(&variable) {
                blocked.insert(variable.clone());
            }
        }
        let mut reduced = false;
        for path in paths {
            let variable = Variable::Path(path);
            if blocked.contains(&variable) || !component.path_support.contains(&path) {
                continue;
            }
            if reduce_path(component, &variable, allow_history) {
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
            (Self::History, PhaseProfile::Absent) => {
                eliminate_history_path(component, variable);
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
fn reduce_path(component: &mut Component, variable: &Variable, allow_history: bool) -> bool {
    // A previous elimination in the same round can introduce `variable` into
    // an output or scalar. Recheck dynamically even though the round-level
    // blocked set filtered its original state.
    if occurs_in_guard_scalar_or_outputs(component, variable) {
        return false;
    }
    let mut profile = phase_profile(component, variable);
    if matches!(profile, PhaseProfile::Unsupported) {
        // Individual selectors may cancel in the whole phase derivative.
        // Only a failed syntactic classification needs joint cofactoring.
        profile = joint_phase::profile(component, variable);
    }
    // Unsupported phases have no local rule, independent of the history.
    // A history pivot is only needed for the phase-absent History rule.
    if matches!(profile, PhaseProfile::Unsupported) {
        return false;
    }
    let history_is_absent = component
        .output
        .history
        .iter()
        .all(|entry| !HistoryEntry::value(entry).variables().contains(variable));
    let rule = match (&profile, history_is_absent) {
        (PhaseProfile::Absent, true) => PathRule::Vacuous,
        (PhaseProfile::Absent, false)
            if allow_history && history_pivot(component, variable).is_some() =>
        {
            PathRule::History
        }
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

/// Finds a hidden history pivot of the form `y xor f`.
///
/// Every history row containing the path must have derivative one in `y`,
/// hence the form `y xor f` with `f` independent of `y`. A pivot row can then
/// be XORed into the other rows to remove their `y` dependence. These
/// are invertible GF(2) row operations, so equality of the complete history
/// vector is unchanged.
fn history_pivot(component: &Component, variable: &Variable) -> Option<usize> {
    let mut position = None;
    for (index, entry) in component.output.history.iter().enumerate() {
        let value = HistoryEntry::value(entry);
        if !value.variables().contains(variable) {
            continue;
        }
        let derivative = value
            .substitute(variable, &BooleanPolynomial::zero())
            .xor(&value.substitute(variable, &BooleanPolynomial::one()));
        if !derivative.is_one() {
            return None;
        }
        position.get_or_insert(index);
    }
    position
}

/// Eliminates one full-rank affine history column by Gaussian row operations.
///
/// For example, `[y xor x, y xor z]` becomes `[x xor z]` after the first row
/// is used as the pivot and summed out. The two values of the removed pivot
/// are orthogonal worlds with the same visible state, hence the `sqrt(2)`
/// scalar supplied by [`PathRule::History`].
fn eliminate_history_path(component: &mut Component, variable: &Variable) {
    let position = history_pivot(component, variable)
        .expect("the history rule is selected only for an affine pivot");
    let pivot_value = HistoryEntry::value(&component.output.history[position]).clone();
    for (index, entry) in component.output.history.iter_mut().enumerate() {
        if index == position || !HistoryEntry::value(entry).variables().contains(variable) {
            continue;
        }
        let value = HistoryEntry::value(entry).xor(&pivot_value);
        *HistoryEntry::value_mut(entry) = value;
    }
    component.output.history.remove(position);
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
