use super::*;
use crate::equivalence::kernel::{KernelPhasePolynomial, KernelScalar};
use crate::symbolic::PhaseCoefficient;
use num_rational::BigRational;
use std::collections::BTreeMap;

fn integer(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}
fn ratio(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}
fn path() -> KernelVariable {
    KernelVariable::PathKet { term: 0, path: 0 }
}
fn var(v: KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v)
}
fn term() -> WorkingTerm {
    WorkingTerm {
        paths: [path()].into(),
        constraints: vec![],
        coefficient: KernelScalar::Rational(integer(1)),
        phase: KernelPhasePolynomial::default(),
    }
}
type Complex = (BigRational, BigRational);
fn add(a: Complex, b: Complex) -> Complex {
    (a.0 + b.0, a.1 + b.1)
}

// Independent exact Q(i) evaluation, enumerating only the small test binders.
fn evaluate(t: &WorkingTerm, free: bool) -> Complex {
    let paths: Vec<_> = t.paths.iter().cloned().collect();
    let mut result = (integer(0), integer(0));
    for mask in 0..1usize << paths.len() {
        let mut values = BTreeMap::from([(KernelVariable::QuantumOutputKet(0), free)]);
        for (i, p) in paths.iter().enumerate() {
            values.insert(p.clone(), mask & (1 << i) != 0);
        }
        let boolean = |p: &KernelBooleanPolynomial| {
            p.as_graph()
                .evaluate::<std::convert::Infallible>(|v| {
                    Ok(values[&KernelVariable::from_graph_variable(v)])
                })
                .unwrap()
        };
        fn scalar(
            s: &KernelScalar,
            boolean: &impl Fn(&KernelBooleanPolynomial) -> bool,
        ) -> BigRational {
            match s {
                KernelScalar::Rational(r) => r.clone(),
                KernelScalar::Add(a, b) => scalar(a, boolean) + scalar(b, boolean),
                KernelScalar::Mul(a, b) => scalar(a, boolean) * scalar(b, boolean),
                KernelScalar::Neg(a) => -scalar(a, boolean),
                KernelScalar::Select {
                    condition,
                    when_true,
                    when_false,
                } => scalar(
                    if boolean(condition) {
                        when_true
                    } else {
                        when_false
                    },
                    boolean,
                ),
                _ => panic!("unsupported test scalar"),
            }
        }
        if t.constraints.iter().any(&boolean) {
            continue;
        }
        let mut phase = integer(0);
        for (p, c) in t.phase.selectors() {
            if boolean(&p) {
                phase += c.as_rational().unwrap();
            }
        }
        let quarters = phase * integer(4);
        assert!(quarters.is_integer());
        let quarter = i64::try_from(quarters.to_integer()).unwrap().rem_euclid(4);
        let weight = scalar(&t.coefficient, &boolean);
        let contribution = match quarter {
            0 => (weight, integer(0)),
            1 => (integer(0), weight),
            2 => (-weight, integer(0)),
            3 => (integer(0), -weight),
            _ => unreachable!(),
        };
        result = add(result, contribution);
    }
    result
}
fn children(t: &WorkingTerm, v: &KernelVariable) -> Vec<WorkingTerm> {
    let mut result = Vec::new();
    visit_bound_cofactors(
        t,
        v,
        |_| true,
        |child| {
            result.push(child);
            Some(())
        },
    )
    .unwrap();
    assert_eq!(result.len(), 2);
    result
}

#[test]
fn all_bound_namespaces_preserve_the_complete_guarded_complex_sum() {
    let paths = [
        path(),
        KernelVariable::PathBra { term: 0, path: 0 },
        KernelVariable::PathKet { term: 1, path: 0 },
    ];
    let p: Vec<_> = paths.iter().cloned().map(var).collect();
    let mut t = term();
    t.paths = paths.iter().cloned().collect();
    t.constraints.push(
        p[1].and(&p[2])
            .xor(&var(KernelVariable::QuantumOutputKet(0))),
    );
    t.coefficient = KernelScalar::Select {
        condition: p[0].xor(&p[1]),
        when_true: Box::new(KernelScalar::Rational(integer(3))),
        when_false: Box::new(KernelScalar::Rational(integer(-2))),
    };
    t.phase
        .add_boolean(&p[0].and(&p[1]), PhaseCoefficient::rational(ratio(1, 4)));
    t.phase
        .add_boolean(&p[2], PhaseCoefficient::rational(ratio(1, 2)));
    for v in paths {
        let parts = children(&t, &v);
        for child in &parts {
            assert!(!child.paths.contains(&v));
            assert_eq!(child.paths.len(), 2);
        }
        for free in [false, true] {
            assert_eq!(
                evaluate(&t, free),
                add(evaluate(&parts[0], free), evaluate(&parts[1], free))
            );
        }
    }
}

#[test]
fn contributions_are_added_without_averaging_or_probability_squaring() {
    let mut t = term();
    t.coefficient = KernelScalar::Select {
        condition: var(path()),
        when_true: Box::new(KernelScalar::Rational(integer(3))),
        when_false: Box::new(KernelScalar::Rational(integer(2))),
    };
    for (half, expected) in [(false, 5), (true, -1)] {
        if half {
            t.phase
                .add_boolean(&var(path()), PhaseCoefficient::rational(ratio(1, 2)));
        }
        let parts = children(&t, &path());
        assert_eq!(
            add(evaluate(&parts[0], false), evaluate(&parts[1], false)),
            (integer(expected), integer(0))
        );
    }
    let parts = children(&term(), &path());
    assert_eq!(
        add(evaluate(&parts[0], false), evaluate(&parts[1], false)),
        (integer(2), integer(0))
    );
}

#[test]
fn free_coordinates_and_unowned_paths_cannot_be_summed() {
    let mut t = term();
    let free = KernelVariable::QuantumOutputKet(0);
    t.paths.insert(free.clone()); // Even a malformed ownership set cannot bind a free coordinate.
    for v in [free, KernelVariable::PathKet { term: 2, path: 0 }] {
        let mut called = false;
        assert!(
            visit_bound_cofactors(
                &t,
                &v,
                |_| true,
                |_| {
                    called = true;
                    Some(())
                }
            )
            .is_none()
        );
        assert!(!called);
    }
}

#[test]
fn refusal_of_second_cofactor_is_not_success_after_first_cofactor() {
    let t = term();
    let mut admitted = 0;
    let mut visited = 0;
    let result = visit_bound_cofactors(
        &t,
        &path(),
        |_| {
            admitted += 1;
            admitted == 1
        },
        |_| {
            visited += 1;
            Some(())
        },
    );
    assert!(result.is_none());
    assert_eq!(visited, 1);
    assert!(t.paths.contains(&path()));
    assert_eq!(evaluate(&t, false), (integer(2), integer(0)));
}

#[test]
fn downstream_refusal_in_either_branch_propagates() {
    for refused in [1, 2] {
        let mut visits = 0;
        let result = visit_bound_cofactors(
            &term(),
            &path(),
            |_| true,
            |_| {
                visits += 1;
                (visits != refused).then_some(())
            },
        );
        assert!(result.is_none());
        assert_eq!(visits, refused);
    }
}

fn enumerate(t: WorkingTerm, budget: &mut usize, depth: usize, limit: usize) -> Option<Complex> {
    let Some(v) = t.paths.first() else {
        return Some(evaluate(&t, false));
    };
    claim_split(budget, depth, limit)?;
    let mut total = (integer(0), integer(0));
    visit_bound_cofactors(
        &t,
        v,
        |_| true,
        |child| {
            total = add(total.clone(), enumerate(child, budget, depth + 1, limit)?);
            Some(())
        },
    )?;
    Some(total)
}

#[test]
fn recursive_branches_share_the_split_budget_and_require_complete_results() {
    let mut t = term();
    t.paths.insert(KernelVariable::PathBra { term: 0, path: 0 });
    assert!(enumerate(t.clone(), &mut 2, 0, 2).is_none());
    assert!(enumerate(t.clone(), &mut 3, 0, 1).is_none());
    assert_eq!(enumerate(t, &mut 3, 0, 2), Some((integer(4), integer(0))));
}

#[test]
fn exhausted_or_depth_limited_split_does_not_consume_budget() {
    for (initial, depth, limit) in [(0, 0, 8), (3, 8, 8), (3, 9, 8)] {
        let mut remaining = initial;
        assert!(claim_split(&mut remaining, depth, limit).is_none());
        assert_eq!(remaining, initial);
    }
}
