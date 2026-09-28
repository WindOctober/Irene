use std::collections::{BTreeMap, BTreeSet};

use num_rational::BigRational;

use crate::symbolic::{BooleanPolynomial, Component, HybridPathSum, Scalar, Variable};

use super::{guard_rows::eliminate_guard_path, reduce_path_sums};

/// Maximum support of a nonlinear guard handled by exact enumeration.
/// Larger supports are left unchanged; this is an optimization limit, not an
/// approximation of the guard.
const MAX_NONLINEAR_GUARD_VARIABLES: usize = 16;

/// Simplifies every reachable HPS component.
///
/// Guard XOR factors share the kernel's GF(2) row reducer. Unique owned-path
/// relations propagate through every field, with or without hidden history.
/// A bounded truth table remains a fallback for nonlinear Boolean implications
/// outside the formal row span.
pub fn simplify(mut hps: HybridPathSum) -> HybridPathSum {
    // Collapsing an affine hidden-history path produces a density
    // representative. It is safe directly only when no sibling component can
    // acquire a spurious coherent cross term with that representative.
    let allow_history_elimination = hps.components.len() == 1;
    let mut components = Vec::with_capacity(hps.components.len());
    for mut component in hps.components {
        if reduce_path_sums(&mut component, allow_history_elimination) {
            components.push(component);
        }
    }
    hps.components = components;
    hps
}

/// Simplifies one control-flow path and returns whether it is reachable.
///
/// This is called as soon as a classical branch adds a new constraint. Hence
/// a relation such as `y0 = x0` is removed before the branch body introduces
/// more paths or phases.
pub(crate) fn simplify_component(component: &mut Component) -> bool {
    loop {
        // Normalize graph cancellations in semantic fields. Keep original
        // guard rows for row-space inference; add reduced rows as consequences
        // only when useful, so factorization does not hide affine columns.
        for value in component
            .output
            .quantum
            .values_mut()
            .chain(component.output.classical.values_mut())
        {
            *value = value.factored();
        }
        for entry in &mut component.output.history {
            let value = entry.value_mut();
            *value = value.factored();
        }
        let normalized: Vec<_> = component
            .guard
            .iter()
            .map(|g| {
                let factored = g.factored();
                // A compact nonlinear XAG may denote an affine constraint.
                // Recover it semantically before the row-space solver; do
                // not build a decision diagram for an entire large guard.
                if !factored.is_affine()
                    && factored.storage_size() <= 1024
                    && factored.variables().len() <= 16
                    && let Some(roots) = BooleanPolynomial::normalize_local(&[factored.clone()])
                {
                    let reduced = &roots[0];
                    if reduced.is_affine() {
                        return reduced.clone();
                    }
                }
                factored
            })
            .collect();
        if normalized.iter().any(BooleanPolynomial::is_one) {
            return false;
        }
        component.guard = component
            .guard
            .iter()
            .zip(&normalized)
            .filter(|(_, reduced)| !reduced.is_zero())
            .map(|(original, _)| original.clone())
            .collect();
        for reduced in normalized {
            if !reduced.is_zero() && reduced.is_affine() && !component.guard.contains(&reduced) {
                component.guard.push(reduced);
            }
        }
        match eliminate_guard_path(component) {
            Err(()) => return false,
            Ok(true) => continue,
            Ok(false) => {}
        }

        if !component.guard.iter().any(|equation| !equation.is_affine()) {
            break;
        }
        match solve_nonlinear_guard(&component.guard, &component.path_support) {
            Inference::Unsatisfiable => return false,
            Inference::Substitute(variable, replacement) => {
                substitute_component(component, &variable, &replacement);
            }
            Inference::None => break,
        }
    }

    component.scalar = simplify_scalar(&component.scalar);
    true
}

enum Inference {
    Unsatisfiable,
    Substitute(Variable, BooleanPolynomial),
    None,
}

/// Uses a bounded exact truth table when a guard equation is nonlinear.
///
/// Enumeration decides reachability exactly and detects compact implied
/// relations `y = 0`, `y = 1`, `y = v`, and `y = 1 ⊕ v`. A support beyond the
/// fixed bound remains in the guard. This prevents a best-effort optimizer
/// from allocating and enumerating an unbounded truth table.
fn solve_nonlinear_guard(guard: &[BooleanPolynomial], path_support: &BTreeSet<usize>) -> Inference {
    let Some(table) = TruthTableGuard::build(guard) else {
        return Inference::None;
    };
    if table.satisfying.is_empty() {
        return Inference::Unsatisfiable;
    }

    let mut paths: Vec<_> = guard_variables(guard)
        .into_iter()
        .filter(|variable| match variable {
            Variable::Path(path) => path_support.contains(path),
            Variable::Input(_) => false,
        })
        .collect();
    paths.sort_by(|left, right| right.cmp(left));

    for variable in paths {
        if table.implies_constant(&variable, false) {
            return Inference::Substitute(variable, BooleanPolynomial::zero());
        }
        if table.implies_constant(&variable, true) {
            return Inference::Substitute(variable, BooleanPolynomial::one());
        }

        for candidate in table.positions.keys() {
            let eligible = match candidate {
                Variable::Input(_) => true,
                Variable::Path(candidate_path) => match &variable {
                    Variable::Path(path) => candidate_path < path,
                    Variable::Input(_) => false,
                },
            };
            if !eligible {
                continue;
            }
            if table.implies_relation(&variable, candidate, false) {
                return Inference::Substitute(
                    variable,
                    BooleanPolynomial::variable(candidate.clone()),
                );
            }
            if table.implies_relation(&variable, candidate, true) {
                return Inference::Substitute(
                    variable,
                    BooleanPolynomial::variable(candidate.clone()).complement(),
                );
            }
        }
    }

    Inference::None
}

struct TruthTableGuard {
    positions: BTreeMap<Variable, usize>,
    satisfying: Vec<usize>,
}

impl TruthTableGuard {
    fn build(guard: &[BooleanPolynomial]) -> Option<Self> {
        let ordered_variables: Vec<_> = guard_variables(guard).into_iter().collect();
        if ordered_variables.len() > MAX_NONLINEAR_GUARD_VARIABLES {
            return None;
        }
        let positions = ordered_variables
            .into_iter()
            .enumerate()
            .map(|(position, variable)| (variable, position))
            .collect::<BTreeMap<_, _>>();
        let assignments = 1usize.checked_shl(positions.len() as u32)?;
        let satisfying = (0..assignments)
            .filter(|assignment| {
                guard
                    .iter()
                    .all(|equation| !evaluate_boolean_polynomial(equation, &positions, *assignment))
            })
            .collect();
        Some(Self {
            positions,
            satisfying,
        })
    }

    fn value(&self, assignment: usize, variable: &Variable) -> bool {
        let position = self.positions[variable];
        assignment & (1usize << position) != 0
    }

    fn implies_constant(&self, variable: &Variable, value: bool) -> bool {
        self.satisfying
            .iter()
            .all(|assignment| self.value(*assignment, variable) == value)
    }

    fn implies_relation(&self, left: &Variable, right: &Variable, complement: bool) -> bool {
        self.satisfying.iter().all(|assignment| {
            self.value(*assignment, left) == (self.value(*assignment, right) ^ complement)
        })
    }
}

fn evaluate_boolean_polynomial(
    polynomial: &BooleanPolynomial,
    positions: &BTreeMap<Variable, usize>,
    assignment: usize,
) -> bool {
    polynomial
        .evaluate::<std::convert::Infallible>(|v| Ok(assignment & (1usize << positions[v]) != 0))
        .unwrap()
}

fn guard_variables(guard: &[BooleanPolynomial]) -> BTreeSet<Variable> {
    guard
        .iter()
        .flat_map(BooleanPolynomial::variables)
        .collect()
}

/// Applies one proven equality to every semantic field of a component.
pub(crate) fn substitute_component(
    component: &mut Component,
    variable: &Variable,
    replacement: &BooleanPolynomial,
) {
    component.guard = component
        .guard
        .iter()
        .map(|equation| equation.substitute(variable, replacement))
        .filter(|equation| !equation.is_zero())
        .collect();
    component.scalar = component.scalar.substitute(variable, replacement);
    component.phase.substitute(variable, replacement);

    for value in component.output.quantum.values_mut() {
        *value = value.substitute(variable, replacement);
    }
    for value in component.output.classical.values_mut() {
        *value = value.substitute(variable, replacement);
    }
    for entry in &mut component.output.history {
        let value = entry.value_mut();
        *value = value.substitute(variable, replacement);
    }

    if let Variable::Path(index) = variable {
        component.path_support.remove(index);
    }
}

/// Performs small exact scalar reductions exposed by path substitution.
///
/// In particular, `sqrt(r) * sqrt(r) = r` for a non-negative rational `r`.
fn simplify_scalar(scalar: &Scalar) -> Scalar {
    match scalar {
        Scalar::Rational(_) | Scalar::Sin(_) | Scalar::Cos(_) => scalar.clone(),
        Scalar::Sqrt(value) => Scalar::sqrt(simplify_scalar(value)),
        Scalar::Add(left, right) => simplify_scalar(left).sum(simplify_scalar(right)),
        Scalar::Mul(_, _) => simplify_product(scalar),
        Scalar::Neg(value) => simplify_scalar(value).negate(),
        Scalar::Inverse(value) => simplify_scalar(value).inverse(),
        Scalar::Select {
            condition,
            when_true,
            when_false,
        } => Scalar::select(
            condition.clone(),
            simplify_scalar(when_true),
            simplify_scalar(when_false),
        ),
    }
}

/// Canonicalizes an associative, commutative product of real scalar factors.
///
/// Rational factors and square roots of non-negative rationals are collected
/// exactly. For example, `2 * 2 * (1/2) * sqrt(1/2)^2` becomes `1`; remaining
/// symbolic factors are sorted before rebuilding the product tree.
fn simplify_product(scalar: &Scalar) -> Scalar {
    let mut rational = BigRational::from_integer(1.into());
    let mut radicand = BigRational::from_integer(1.into());
    let mut factors = Vec::new();
    collect_product(scalar, &mut rational, &mut radicand, &mut factors);
    if rational == BigRational::from_integer(0.into()) {
        return Scalar::zero();
    }

    let root = Scalar::sqrt(Scalar::rational(radicand));
    match root {
        Scalar::Rational(value) => rational *= value,
        root => factors.push(root),
    }
    if rational != BigRational::from_integer(1.into()) || factors.is_empty() {
        factors.push(Scalar::rational(rational));
    }
    factors.sort();
    factors
        .into_iter()
        .reduce(|left, right| Scalar::Mul(Box::new(left), Box::new(right)))
        .unwrap_or_else(Scalar::one)
}

fn collect_product(
    scalar: &Scalar,
    rational: &mut BigRational,
    radicand: &mut BigRational,
    factors: &mut Vec<Scalar>,
) {
    match scalar {
        Scalar::Mul(left, right) => {
            collect_product(left, rational, radicand, factors);
            collect_product(right, rational, radicand, factors);
        }
        Scalar::Rational(value) => *rational *= value,
        Scalar::Sqrt(value) => {
            let value = simplify_scalar(value);
            match value {
                Scalar::Rational(value) if value >= BigRational::from_integer(0.into()) => {
                    *radicand *= value;
                }
                value => factors.push(Scalar::sqrt(value)),
            }
        }
        Scalar::Neg(value) => {
            *rational = -rational.clone();
            collect_product(value, rational, radicand, factors);
        }
        scalar => factors.push(simplify_scalar(scalar)),
    }
}
