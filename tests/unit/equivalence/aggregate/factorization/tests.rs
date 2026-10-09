use super::super::collection::ExactEntry;
use super::super::{ConstraintNormalization, normalize_constraint_span};
use super::*;
use num_rational::BigRational;

fn path(i: usize) -> KernelVariable {
    KernelVariable::PathKet { term: 0, path: i }
}

#[test]
fn mixed_guards_phases_and_path_dependent_weights_are_not_separated() {
    let a = variable(path(0));
    let b = variable(path(1));
    let original = WorkingTerm {
        paths: [path(0), path(1)].into(),
        constraints: vec![],
        coefficient: rational(3),
        phase: KernelPhasePolynomial::default(),
    };
    assert!(factor(&original, 32768).is_some());
    let mut guarded = original.clone();
    guarded.constraints.push(a.xor(&b));
    assert!(factor(&guarded, 32768).is_none());
    let mut coupled_phase = original.clone();
    coupled_phase.phase.add_boolean(
        &a.and(&b),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 4)),
    );
    assert!(factor(&coupled_phase, 32768).is_none());
    let mut weighted = original;
    weighted.coefficient = KernelScalar::Select {
        condition: a,
        when_true: Box::new(rational(3)),
        when_false: Box::new(rational(5)),
    };
    assert!(factor(&weighted, 32768).is_none());
}

fn aggregate(weight: i64, quarter: i64, guards: Vec<KernelBooleanPolynomial>) -> ExactAggregate {
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(
        &KernelBooleanPolynomial::one(),
        crate::symbolic::PhaseCoefficient::rational(ratio(quarter, 4)),
    );
    BTreeMap::from([(
        ExactEntry {
            constraints: guards,
        },
        BTreeMap::from([(phase, rational(weight))]),
    )])
}

fn reduce(mut t: WorkingTerm) -> Option<Option<ExactTerm>> {
    assert!(t.paths.is_empty());
    match normalize_constraint_span(&mut t.constraints) {
        ConstraintNormalization::Contradiction => Some(None),
        ConstraintNormalization::BudgetExceeded => None,
        ConstraintNormalization::Normalized => Some(Some(ExactTerm {
            constraints: t.constraints,
            coefficient: t.coefficient,
            phase: t.phase,
        })),
    }
}

// Independent exact Q(i) evaluation of the complete guarded aggregate.
fn value(sum: &ExactAggregate, input: bool) -> (BigRational, BigRational) {
    let boolean = |p: &KernelBooleanPolynomial| {
        p.as_graph()
            .evaluate::<std::convert::Infallible>(|v| {
                assert_eq!(
                    KernelVariable::from_graph_variable(v),
                    KernelVariable::InputKet(0)
                );
                Ok(input)
            })
            .unwrap()
    };
    let mut total = (integer(0), integer(0));
    for (entry, coefficients) in sum {
        if entry.constraints.iter().any(&boolean) {
            continue;
        }
        for (phase, coefficient) in coefficients {
            let KernelScalar::Rational(weight) = coefficient else {
                panic!("non-rational test coefficient")
            };
            let mut turns = integer(0);
            for (p, c) in phase.selectors() {
                if boolean(&p) {
                    turns += c.as_rational().unwrap();
                }
            }
            let quarters = turns * integer(4);
            assert!(quarters.is_integer());
            match i64::try_from(quarters.to_integer()).unwrap().rem_euclid(4) {
                0 => total.0 += weight,
                1 => total.1 += weight,
                2 => total.0 -= weight,
                3 => total.1 -= weight,
                _ => unreachable!(),
            }
        }
    }
    total
}

#[test]
fn aggregate_multiplication_preserves_guard_conjunction_and_complex_products() {
    let x = variable(KernelVariable::InputKet(0));
    for p in 0..4 {
        for q in 0..4 {
            let mut left = aggregate(2, p, vec![]);
            left.extend(aggregate(3, (p + 1) % 4, vec![x.clone()]));
            let mut right = aggregate(-2, q, vec![]);
            right.extend(aggregate(5, q, vec![x.complement()]));
            let result = multiply(left.clone(), right.clone(), &mut 4, &mut 100, reduce).unwrap();
            for bit in [false, true] {
                let a = value(&left, bit);
                let b = value(&right, bit);
                assert_eq!(
                    value(&result, bit),
                    (&a.0 * &b.0 - &a.1 * &b.1, &a.0 * &b.1 + &a.1 * &b.0)
                );
            }
        }
    }
}

#[test]
fn contradictory_selectors_annihilate_the_product() {
    let x = variable(KernelVariable::InputKet(0));
    let result = multiply(
        aggregate(2, 0, vec![x.clone()]),
        aggregate(3, 0, vec![x.complement()]),
        &mut 1,
        &mut 0,
        reduce,
    )
    .unwrap();
    assert!(result.is_empty());
}

#[test]
fn shared_product_and_phase_budgets_refuse_without_returning_partial_products() {
    let a = aggregate(1, 1, vec![]);
    let mut products = 2;
    let mut cells = 4;
    assert!(multiply(a.clone(), a.clone(), &mut products, &mut cells, reduce).is_some());
    assert_eq!((products, cells), (1, 2));
    assert!(multiply(a.clone(), a.clone(), &mut products, &mut cells, reduce).is_some());
    assert_eq!((products, cells), (0, 0));
    assert!(multiply(a.clone(), a.clone(), &mut products, &mut cells, reduce).is_none());
    assert!(multiply(a.clone(), a, &mut 2, &mut 1, reduce).is_none());
}

#[test]
fn reducer_refusal_after_a_successful_pair_discards_the_product() {
    let mut left = aggregate(2, 0, vec![]);
    left.extend(aggregate(3, 0, vec![variable(KernelVariable::InputKet(0))]));
    let mut visited = 0;
    let result = multiply(left, aggregate(1, 0, vec![]), &mut 2, &mut 0, |term| {
        visited += 1;
        if visited == 2 { None } else { reduce(term) }
    });
    assert_eq!(visited, 2);
    assert!(result.is_none());
}

#[test]
fn graph_phase_is_not_silently_dropped_by_algebraic_convolution() {
    let mut phase = KernelPhasePolynomial::default();
    let a = variable(KernelVariable::InputKet(0)).as_graph();
    let b = variable(KernelVariable::InputKet(1)).as_graph();
    let c = variable(KernelVariable::InputKet(2)).as_graph();
    let graph = KernelBooleanPolynomial::from_graph(a.and(&b.xor(&c)));
    phase.add_boolean(
        &graph,
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 4)),
    );
    assert!(!phase.is_algebraic());
    let graph_sum = BTreeMap::from([(
        ExactEntry {
            constraints: vec![],
        },
        BTreeMap::from([(phase, rational(1))]),
    )]);
    assert!(
        multiply(
            aggregate(1, 0, vec![]),
            graph_sum,
            &mut 1,
            &mut 10,
            |_| panic!("graph phase should be refused")
        )
        .is_none()
    );
}
use super::super::scalar::ratio;
use super::super::{KernelMonomial, KernelVariable};

fn variable(v: KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v)
}
fn rational(n: i64) -> KernelScalar {
    KernelScalar::Rational(integer(n))
}

#[test]
fn guarded_factorization_preserves_all_pointwise_weights_and_equations() {
    let names = [
        KernelVariable::PathKet { term: 0, path: 0 },
        KernelVariable::PathBra { term: 1, path: 0 },
        KernelVariable::PathKet { term: 0, path: 1 },
        KernelVariable::InputKet(0),
    ];
    let vars = names.clone().map(variable);
    let anf = |mask: usize, a: &KernelBooleanPolynomial, b: &KernelBooleanPolynomial| {
        [
            KernelBooleanPolynomial::one(),
            a.clone(),
            b.clone(),
            a.and(b),
        ]
        .into_iter()
        .enumerate()
        .fold(KernelBooleanPolynomial::zero(), |p, (bit, term)| {
            if mask & (1 << bit) == 0 {
                p
            } else {
                p.xor(&term)
            }
        })
    };
    for f in 0..16 {
        for g in 0..16 {
            let mut source = WorkingTerm {
                paths: names[..3].iter().cloned().collect(),
                constraints: vec![anf(f, &vars[0], &vars[1]), anf(g, &vars[2], &vars[3])],
                coefficient: rational(3),
                phase: KernelPhasePolynomial::default(),
            };
            for (index, term) in [
                vars[0].and(&vars[1]).and(&vars[3]),
                vars[2].and(&vars[3]),
                vars[3].clone(),
            ]
            .into_iter()
            .enumerate()
            {
                source.phase.add_boolean(
                    &term,
                    crate::symbolic::PhaseCoefficient::rational(ratio(index as i64 + 1, 8)),
                );
            }
            let factors = factor(&source, 32768).unwrap();
            assert_eq!(factors.len(), 3);
            assert_eq!(
                factors
                    .iter()
                    .map(|factor| factor.paths.len())
                    .sum::<usize>(),
                3
            );
            for assignment in 0..16 {
                let mono = |m: &KernelMonomial| {
                    m.variables().all(|v| {
                        assignment & (1 << names.iter().position(|n| n == v).unwrap()) != 0
                    })
                };
                let guard = |term: &WorkingTerm| {
                    term.constraints
                        .iter()
                        .all(|row| !row.terms().fold(false, |value, m| value ^ mono(m)))
                };
                assert_eq!(guard(&source), factors.iter().all(guard));
                let phase = |term: &WorkingTerm| {
                    term.phase
                        .terms()
                        .filter(|(m, _)| mono(m))
                        .fold(integer(0), |p, (_, c)| p + c.as_rational().unwrap())
                };
                assert_eq!(
                    phase(&source),
                    factors.iter().map(phase).sum::<BigRational>()
                );
                assert_eq!(factors[0].coefficient, rational(3));
                assert!(
                    factors[1..]
                        .iter()
                        .all(|factor| factor.coefficient == rational(1))
                );
            }
            let mut refused = source;
            refused
                .constraints
                .resize(65, KernelBooleanPolynomial::zero());
            if refused
                .constraints
                .iter()
                .any(|row| row.variables().iter().any(KernelVariable::is_bound_path))
            {
                assert!(factor(&refused, 32768).is_none());
            }
        }
    }
}

#[test]
fn guarded_factorization_charges_combined_phase_and_guard_syntax() {
    let a = KernelVariable::PathKet { term: 0, path: 0 };
    let b = KernelVariable::PathBra { term: 0, path: 0 };
    let mut source = WorkingTerm {
        paths: BTreeSet::from([a.clone(), b]),
        constraints: vec![variable(a)],
        coefficient: rational(3),
        phase: KernelPhasePolynomial::default(),
    };
    for i in 0..5000 {
        source.phase.add_boolean(
            &variable(KernelVariable::InputKet(i)),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    let factors = factor(&source, 32768).unwrap();
    assert_eq!(factors.len(), 3);
    assert_eq!(factors[0].phase, source.phase);
    assert_eq!(factors[0].coefficient, source.coefficient);
    assert_eq!(
        factors
            .iter()
            .flat_map(|factor| factor.constraints.iter())
            .collect::<Vec<_>>(),
        source.constraints.iter().collect::<Vec<_>>()
    );
    assert_eq!(
        factors
            .iter()
            .flat_map(|factor| factor.paths.iter().cloned())
            .collect::<BTreeSet<_>>(),
        source.paths
    );
    let mut high_degree = source;
    high_degree.phase = KernelPhasePolynomial::default();
    let common = (0..7).fold(KernelBooleanPolynomial::one(), |p, i| {
        p.and(&variable(KernelVariable::InputBra(i)))
    });
    for i in 0..4096 {
        high_degree.phase.add_boolean(
            &common.and(&variable(KernelVariable::InputKet(i))),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    // Fewer terms than the admitted source, but >32768 actual cells.
    assert!(factor(&high_degree, 32768).is_none());
}
