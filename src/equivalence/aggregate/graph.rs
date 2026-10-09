//! Graph-native guard/Fourier reduction. Every substitution has a unique
//! bound-path solution. Graph leaves are never new independent coordinates.
use super::*;
use crate::utils::constraint_rows::Error;

use super::constraints::graph_rows as guard_rows;

fn scalar_algebraic(s: &KernelScalar) -> bool {
    match s {
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => {
            condition.is_algebraic() && scalar_algebraic(when_true) && scalar_algebraic(when_false)
        }
        KernelScalar::Sqrt(x) | KernelScalar::Neg(x) | KernelScalar::Inverse(x) => {
            scalar_algebraic(x)
        }
        KernelScalar::Mul(a, b) | KernelScalar::Add(a, b) => {
            scalar_algebraic(a) && scalar_algebraic(b)
        }
        _ => true,
    }
}
pub(super) fn is_algebraic(t: &WorkingTerm) -> bool {
    t.phase.is_algebraic()
        && t.constraints
            .iter()
            .all(KernelBooleanPolynomial::is_algebraic)
        && scalar_algebraic(&t.coefficient)
}

pub(super) fn reduce(mut t: WorkingTerm) -> Reduction {
    let mut selector_recovery = true;
    let mut graph_recovery = true;
    loop {
        if t.coefficient.is_zero() || t.constraints.iter().any(KernelBooleanPolynomial::is_one) {
            return Reduction::Zero;
        }
        t.constraints.retain(|p| !p.is_zero());
        if is_algebraic(&t) {
            return reduce_working_term(t);
        }
        // Match the existing literal-alias orientation: retain the least bound
        // coordinate, or the free coordinate. This also keeps independently
        // lowered kernels in compatible path coordinates without ANF expansion.
        let alias = t.constraints.iter().find_map(|row| {
            let parts = row.as_graph().xor_terms();
            if parts.len() != 2 {
                return None;
            }
            let vars: Vec<_> = parts
                .iter()
                .map(|p| p.as_variable().map(KernelVariable::from_graph_variable))
                .collect::<Option<_>>()?;
            let removed = vars.iter().filter(|v| t.paths.contains(*v)).max()?.clone();
            let kept = vars.into_iter().find(|v| *v != removed)?;
            Some((removed, KernelBooleanPolynomial::variable(kept)))
        });
        if let Some((v, rhs)) = alias {
            t.substitute(&v, &rhs);
            t.paths.remove(&v);
            selector_recovery = true;
            graph_recovery = true;
            continue;
        }
        let mut pivot = None;
        let rows = match guard_rows(&t) {
            Ok(rows) => rows,
            Err(Error::Contradiction) => return Reduction::Zero,
            Err(Error::BudgetExceeded) => t.constraints.clone(),
        };
        // Retain the equivalent row-space normal form, including in path-free
        // cofactors, so semantically identical selectors can share SMT nodes.
        t.constraints = rows.clone();
        for row in &rows {
            let graph = row.as_graph();
            for atom in graph.xor_terms() {
                let Some(v) = atom.as_variable() else {
                    continue;
                };
                let v = KernelVariable::from_graph_variable(v);
                if !t.paths.contains(&v) {
                    continue;
                }
                let rhs = row.xor(&KernelBooleanPolynomial::variable(v.clone()));
                if !rhs.variables().contains(&v) {
                    pivot = Some((v, rhs));
                    break;
                }
            }
            if pivot.is_some() {
                break;
            }
        }
        if let Some((v, rhs)) = pivot {
            t.substitute(&v, &rhs);
            t.paths.remove(&v);
            selector_recovery = true;
            graph_recovery = true;
            continue;
        }
        let mut changed = false;
        for v in t.paths.clone() {
            let Some(factor) = t.graph_fourier(&v) else {
                continue;
            };
            t.remove_summed_path(&v, factor);
            changed = true;
            break;
        }
        if changed {
            selector_recovery = true;
            graph_recovery = true;
            continue;
        }
        if graph_recovery {
            graph_recovery = false;
            let roots: Vec<_> = t
                .constraints
                .iter()
                .map(|p| p.as_graph().factored())
                .collect();
            let normalized: Vec<_> = roots
                .into_iter()
                .map(KernelBooleanPolynomial::from_graph)
                .collect();
            if normalized != t.constraints {
                t.constraints = normalized;
                continue;
            }
        }
        if selector_recovery {
            selector_recovery = false;
            let before = (
                t.constraints.clone(),
                t.phase.clone(),
                t.coefficient.clone(),
            );
            // Free coordinates are NOT summed. Keep each defining equality
            // while substituting it through the other fields. Least-variable
            // orientation makes definitions triangular, including nonlinear RHSs.
            for row in &rows {
                let Some(v) = row.variables().into_iter().next() else {
                    continue;
                };
                if t.paths.contains(&v) {
                    continue;
                }
                let rhs = row.xor(&KernelBooleanPolynomial::variable(v.clone()));
                if rhs.variables().contains(&v) {
                    continue;
                }
                t.substitute(&v, &rhs);
                t.constraints.push(row.clone());
            }
            t.constraints.retain(|p| !p.is_zero());
            t.constraints.sort();
            t.constraints.dedup();
            if before
                != (
                    t.constraints.clone(),
                    t.phase.clone(),
                    t.coefficient.clone(),
                )
            {
                continue;
            }
        }
        if t.paths.is_empty() {
            return Reduction::Exact(ExactTerm {
                constraints: t.constraints,
                coefficient: t.coefficient,
                phase: t.phase,
            });
        }
        return Reduction::Sum(Box::new(t));
    }
}

#[cfg(test)]
#[path = "../../../tests/unit/equivalence/aggregate/graph/tests.rs"]
mod tests;
