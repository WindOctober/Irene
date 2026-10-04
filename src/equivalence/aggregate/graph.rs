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
mod tests {
    use super::*;
    use crate::symbolic::{BooleanPolynomial, PhaseCoefficient};
    fn graph(p: BooleanPolynomial) -> KernelBooleanPolynomial {
        KernelBooleanPolynomial::from_graph(p)
    }
    fn value(p: &KernelBooleanPolynomial, assignments: &BTreeMap<KernelVariable, bool>) -> bool {
        p.as_graph()
            .evaluate::<std::convert::Infallible>(|v| {
                Ok(assignments[&KernelVariable::from_graph_variable(v)])
            })
            .unwrap()
    }
    fn scalar(s: &KernelScalar, assignments: &BTreeMap<KernelVariable, bool>) -> BigRational {
        match s {
            KernelScalar::Rational(r) => r.clone(),
            KernelScalar::Mul(a, b) => scalar(a, assignments) * scalar(b, assignments),
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => scalar(
                if value(condition, assignments) {
                    when_true
                } else {
                    when_false
                },
                assignments,
            ),
            _ => panic!("unexpected test scalar"),
        }
    }
    fn sum(t: &WorkingTerm, free: &BTreeMap<KernelVariable, bool>) -> BigRational {
        let paths: Vec<_> = t.paths.iter().cloned().collect();
        (0..1 << paths.len())
            .map(|bits| {
                let mut a = free.clone();
                for (i, v) in paths.iter().enumerate() {
                    a.insert(v.clone(), bits & (1 << i) != 0);
                }
                if t.constraints.iter().any(|p| value(p, &a)) {
                    return integer(0);
                }
                let phase = t
                    .phase
                    .selectors()
                    .filter(|(p, _)| value(p, &a))
                    .map(|(_, c)| c.as_rational().unwrap())
                    .fold(integer(0), |a, b| a + b);
                let sign = if phase.is_integer() {
                    1
                } else {
                    assert!((phase * integer(2)).is_integer());
                    -1
                };
                scalar(&t.coefficient, &a) * integer(sign)
            })
            .fold(integer(0), |a, b| a + b)
    }
    fn fixture() -> (WorkingTerm, KernelVariable, KernelBooleanPolynomial) {
        let v = KernelVariable::PathKet { term: 0, path: 0 };
        let bit = |i| KernelBooleanPolynomial::variable(KernelVariable::InputKet(i));
        let f = graph(
            bit(0)
                .as_graph()
                .xor(&bit(1).as_graph())
                .and(&bit(2).as_graph()),
        );
        assert!(!f.is_algebraic());
        (
            WorkingTerm {
                constraints: vec![],
                paths: BTreeSet::from([v.clone()]),
                coefficient: KernelScalar::Rational(ratio(2, 3)),
                phase: KernelPhasePolynomial::default(),
            },
            v,
            f,
        )
    }

    fn reduced(t: WorkingTerm) -> WorkingTerm {
        match reduce_working_term(t) {
            Reduction::Exact(e) => WorkingTerm {
                constraints: e.constraints,
                coefficient: e.coefficient,
                phase: e.phase,
                paths: BTreeSet::new(),
            },
            Reduction::Sum(t) => *t,
            Reduction::Zero => WorkingTerm {
                constraints: vec![],
                coefficient: KernelScalar::Rational(integer(0)),
                phase: KernelPhasePolynomial::default(),
                paths: BTreeSet::new(),
            },
            Reduction::Residual => panic!("small graph should not refuse"),
        }
    }

    fn check_entries(before: &WorkingTerm, after: &WorkingTerm) {
        for bits in 0..16 {
            let free = (0..4)
                .map(|i| (KernelVariable::InputKet(i), bits & (1 << i) != 0))
                .collect();
            assert_eq!(sum(before, &free), sum(after, &free), "assignment {bits}");
        }
    }

    #[test]
    fn alias_and_dispatch_preserve_graph_weighted_entries() {
        let (mut t, v, f) = fixture();
        let w = KernelVariable::PathBra { term: 0, path: 0 };
        t.paths.insert(w.clone());
        t.constraints = vec![
            KernelBooleanPolynomial::variable(v).xor(&KernelBooleanPolynomial::variable(w.clone())),
            KernelBooleanPolynomial::variable(w).xor(&f),
        ];
        let result = reduced(t.clone());
        assert!(result.paths.is_empty());
        check_entries(&t, &result);
    }

    #[test]
    fn free_selector_is_retained_while_phase_is_simplified() {
        let (mut t, v, _) = fixture();
        let bit = |i| KernelBooleanPolynomial::variable(KernelVariable::InputKet(i));
        let f = graph(
            bit(1)
                .as_graph()
                .xor(&bit(2).as_graph())
                .and(&bit(3).as_graph()),
        );
        let x = bit(0);
        t.paths.clear();
        t.constraints = vec![x.xor(&f)];
        t.phase
            .add_boolean(&x, PhaseCoefficient::rational(ratio(1, 2)));
        let result = reduced(t.clone());
        assert!(result.paths.is_empty());
        assert!(!result.constraints.is_empty());
        assert!(!result.phase.variables().contains(&v));
        assert!(
            !result
                .phase
                .variables()
                .contains(&KernelVariable::InputKet(0))
        );
        check_entries(&t, &result);
    }

    #[test]
    fn self_dependent_definition_keeps_the_bound_sum() {
        let (mut t, v, f) = fixture();
        let path = KernelBooleanPolynomial::variable(v.clone());
        t.constraints = vec![path.xor(&graph(path.as_graph().and(&f.as_graph())))];
        let result = reduced(t.clone());
        assert!(result.paths.contains(&v));
        check_entries(&t, &result);
    }

    #[test]
    fn contradictory_graph_rows_annihilate_the_term() {
        let (mut t, _, f) = fixture();
        t.constraints = vec![f.clone(), f.complement()];
        assert!(matches!(reduce_working_term(t), Reduction::Zero));
    }

    #[test]
    fn graph_guards_and_fourier_preserve_complete_weighted_sums() {
        let v = KernelVariable::PathKet { term: 0, path: 0 };
        let path = KernelBooleanPolynomial::variable(v.clone());
        let a = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
        let b = KernelBooleanPolynomial::variable(KernelVariable::InputKet(1));
        let c = KernelBooleanPolynomial::variable(KernelVariable::InputKet(2));
        let f = graph(a.as_graph().xor(&b.as_graph()).and(&c.as_graph()));
        for with_guard in [false, true] {
            let mut phase = KernelPhasePolynomial::default();
            phase.add_boolean(
                &graph(path.as_graph().and(&f.as_graph()).xor(&a.as_graph())),
                PhaseCoefficient::rational(ratio(1, 2)),
            );
            let t = WorkingTerm {
                paths: BTreeSet::from([v.clone()]),
                constraints: if with_guard {
                    vec![path.xor(&f)]
                } else {
                    vec![]
                },
                phase,
                coefficient: KernelScalar::Rational(ratio(1, 3)),
            };
            let reduced = match reduce(t.clone()) {
                Reduction::Exact(e) => WorkingTerm {
                    constraints: e.constraints,
                    phase: e.phase,
                    coefficient: e.coefficient,
                    paths: BTreeSet::new(),
                },
                Reduction::Sum(t) => *t,
                Reduction::Zero => WorkingTerm {
                    constraints: vec![],
                    phase: KernelPhasePolynomial::default(),
                    coefficient: KernelScalar::Rational(integer(0)),
                    paths: BTreeSet::new(),
                },
                Reduction::Residual => panic!("small graph reduction refused"),
            };
            assert!(reduced.paths.is_empty());
            for bits in 0..8 {
                let free = (0..3)
                    .map(|i| (KernelVariable::InputKet(i), bits & (1 << i) != 0))
                    .collect();
                assert_eq!(sum(&t, &free), sum(&reduced, &free));
            }
        }
    }
}
