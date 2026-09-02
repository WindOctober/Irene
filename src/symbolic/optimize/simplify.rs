use std::collections::{BTreeMap, BTreeSet};

use bitgauss::BitMatrix;
use oxidd::bdd::BDDFunction;
use oxidd::{BooleanFunction, Manager, ManagerRef};

use crate::symbolic::{
    BooleanPolynomial, Component, HistoryEntry, HybridPathSum, Monomial, Scalar, Variable,
};

/// Simplifies every reachable HPS component without enumerating assignments.
///
/// Affine guard equations are reduced over GF(2). Guards containing products,
/// such as `x*y ⊕ y0 = 0`, are represented by a BDD for exact satisfiability
/// and implication checks. Substitutions are propagated through all semantic
/// fields of the component.
pub fn simplify(mut hps: HybridPathSum) -> HybridPathSum {
    let mut components = Vec::with_capacity(hps.components.len());
    for mut component in hps.components {
        if simplify_component(&mut component) {
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
        match solve_affine_guard(&component.guard, &component.path_support) {
            Inference::Unsatisfiable => return false,
            Inference::Substitute(variable, replacement) => {
                substitute_component(component, &variable, &replacement);
                continue;
            }
            Inference::None => {}
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

/// Row-reduces the affine part of a guard over GF(2).
///
/// For example, the equations `y0 ⊕ y1 = 0` and `y1 ⊕ x0 ⊕ 1 = 0`
/// yield `y0 = 1 ⊕ x0` and `y1 = 1 ⊕ x0`. Path columns precede input
/// columns, so elimination solves paths in terms of free program inputs.
fn solve_affine_guard(guard: &[BooleanPolynomial], path_support: &BTreeSet<usize>) -> Inference {
    let equations: Vec<_> = guard
        .iter()
        .filter(|equation| equation.is_affine())
        .collect();
    if equations.is_empty() {
        return Inference::None;
    }

    let variables = affine_variable_order(&equations);
    let constant_column = variables.len();
    let mut matrix = BitMatrix::build(equations.len(), constant_column + 1, |row, column| {
        if column == constant_column {
            equations[row].has_term(&Monomial::one())
        } else {
            equations[row].has_term(&Monomial::variable(variables[column].clone()))
        }
    });
    matrix.gauss(true);

    for row in 0..equations.len() {
        let pivot = (0..variables.len()).find(|column| matrix.bit(row, *column));
        let Some(pivot) = pivot else {
            if matrix.bit(row, constant_column) {
                return Inference::Unsatisfiable;
            }
            continue;
        };

        let Variable::Path(path) = &variables[pivot] else {
            continue;
        };
        if !path_support.contains(path) {
            continue;
        }

        let mut replacement = BooleanPolynomial::from(matrix.bit(row, constant_column));
        for (column, variable) in variables.iter().enumerate() {
            if column != pivot && matrix.bit(row, column) {
                replacement = replacement.xor(&BooleanPolynomial::variable(variable.clone()));
            }
        }
        return Inference::Substitute(variables[pivot].clone(), replacement);
    }

    Inference::None
}

fn affine_variable_order(equations: &[&BooleanPolynomial]) -> Vec<Variable> {
    let all: BTreeSet<_> = equations
        .iter()
        .flat_map(|equation| equation.variables())
        .collect();
    let mut paths: Vec<_> = all
        .iter()
        .filter(|variable| matches!(variable, Variable::Path(_)))
        .cloned()
        .collect();
    paths.sort_by(|left, right| right.cmp(left));
    paths.extend(
        all.into_iter()
            .filter(|variable| matches!(variable, Variable::Input(_))),
    );
    paths
}

/// Uses a BDD when at least one guard equation is nonlinear.
///
/// The BDD decides reachability exactly and detects compact implied relations
/// `y = 0`, `y = 1`, `y = v`, and `y = 1 ⊕ v`. An arbitrary nonlinear
/// function of many variables remains in the guard instead of being expanded
/// into a potentially exponential ANF expression.
fn solve_nonlinear_guard(guard: &[BooleanPolynomial], path_support: &BTreeSet<usize>) -> Inference {
    let Some(bdd) = BddGuard::build(guard) else {
        // Optimization is best-effort: allocation failure leaves the exact
        // symbolic guard unchanged.
        return Inference::None;
    };
    if !bdd.function.satisfiable() {
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
        for (replacement, function) in [
            (BooleanPolynomial::zero(), &bdd.false_function),
            (BooleanPolynomial::one(), &bdd.true_function),
        ] {
            if bdd.implies_equal(&variable, function) == Some(true) {
                return Inference::Substitute(variable, replacement);
            }
        }

        for candidate in bdd.variables.keys() {
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
            let candidate_function = &bdd.variables[candidate];
            if bdd.implies_equal(&variable, candidate_function) == Some(true) {
                return Inference::Substitute(
                    variable,
                    BooleanPolynomial::variable(candidate.clone()),
                );
            }
            let Some(complement) = candidate_function.not().ok() else {
                continue;
            };
            if bdd.implies_equal(&variable, &complement) == Some(true) {
                return Inference::Substitute(
                    variable,
                    BooleanPolynomial::variable(candidate.clone()).complement(),
                );
            }
        }
    }

    Inference::None
}

struct BddGuard {
    function: BDDFunction,
    variables: BTreeMap<Variable, BDDFunction>,
    false_function: BDDFunction,
    true_function: BDDFunction,
}

impl BddGuard {
    fn build(guard: &[BooleanPolynomial]) -> Option<Self> {
        let ordered_variables: Vec<_> = guard_variables(guard).into_iter().collect();
        let capacity = ordered_variables.len().saturating_mul(1024).max(1024);
        let manager_ref = oxidd::bdd::new_manager(capacity, capacity, 1);
        let (functions, false_function, true_function) =
            manager_ref.with_manager_exclusive(|manager| {
                manager.add_vars(ordered_variables.len() as u32);
                let functions = (0..ordered_variables.len())
                    .map(|level| BDDFunction::var(manager, level as u32).ok())
                    .collect::<Option<Vec<_>>>()?;
                Some((functions, BDDFunction::f(manager), BDDFunction::t(manager)))
            })?;
        let variables: BTreeMap<_, _> = ordered_variables.into_iter().zip(functions).collect();

        let mut function = true_function.clone();
        for equation in guard {
            let equation = bdd_polynomial(equation, &variables, &false_function, &true_function)?;
            function = function.and(&equation.not().ok()?).ok()?;
        }
        Some(Self {
            function,
            variables,
            false_function,
            true_function,
        })
    }

    fn implies_equal(&self, variable: &Variable, value: &BDDFunction) -> Option<bool> {
        let difference = self.variables.get(variable)?.xor(value).ok()?;
        Some(!self.function.and(&difference).ok()?.satisfiable())
    }
}

/// Converts an ANF polynomial to a BDD by preserving XOR and multiplication.
///
/// For example, `x ⊕ x*y` becomes the BDD expression `x XOR (x AND y)`.
fn bdd_polynomial(
    polynomial: &BooleanPolynomial,
    variables: &BTreeMap<Variable, BDDFunction>,
    false_function: &BDDFunction,
    true_function: &BDDFunction,
) -> Option<BDDFunction> {
    let mut result = false_function.clone();
    for monomial in polynomial.terms() {
        let mut term = true_function.clone();
        for variable in monomial.variables() {
            term = term.and(variables.get(variable)?).ok()?;
        }
        result = result.xor(&term).ok()?;
    }
    Some(result)
}

fn guard_variables(guard: &[BooleanPolynomial]) -> BTreeSet<Variable> {
    guard
        .iter()
        .flat_map(BooleanPolynomial::variables)
        .collect()
}

/// Applies one proven equality to every semantic field of a component.
fn substitute_component(
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
        let value = match entry {
            HistoryEntry::Write { value, .. } | HistoryEntry::Discard { value } => value,
        };
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
        Scalar::Mul(left, right) => {
            let left = simplify_scalar(left);
            let right = simplify_scalar(right);
            if let (Scalar::Sqrt(left_root), Scalar::Sqrt(right_root)) = (&left, &right)
                && left_root == right_root
                && let Scalar::Rational(value) = left_root.as_ref()
                && value >= &Default::default()
            {
                return Scalar::rational(value.clone());
            }
            left.multiply(right)
        }
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
