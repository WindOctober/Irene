use super::*;

type Complex = (BigRational, BigRational);
fn cmul(a: Complex, b: Complex) -> Complex {
    (&a.0 * &b.0 - &a.1 * &b.1, a.0 * b.1 + a.1 * b.0)
}
fn boolean(p: &KernelBooleanPolynomial, inputs: &[bool; 3]) -> bool {
    p.as_graph()
        .evaluate::<()>(|v| {
            let index = match KernelVariable::from_graph_variable(v) {
                KernelVariable::InputKet(0) => 0,
                KernelVariable::InputBra(0) => 1,
                KernelVariable::ClassicalOutput(0) => 2,
                _ => panic!("unexpected coordinate"),
            };
            Ok(inputs[index])
        })
        .unwrap()
}
// Independent exact interpretation in Q(i), without the production multiplier.
fn value(s: &ExactAggregate, inputs: &[bool; 3]) -> Complex {
    let mut result = (integer(0), integer(0));
    for (entry, values) in s {
        if entry.constraints.iter().any(|p| boolean(p, inputs)) {
            continue;
        }
        for (p, c) in values {
            let KernelScalar::Rational(c) = c else {
                panic!("non-rational coefficient")
            };
            let mut turns = integer(0);
            for (condition, coefficient) in p.selectors() {
                if boolean(&condition, inputs) {
                    turns += coefficient.as_rational().unwrap();
                }
            }
            let quarters = turns * integer(4);
            assert!(quarters.is_integer());
            match i64::try_from(quarters.to_integer()).unwrap().rem_euclid(4) {
                0 => result.0 += c,
                1 => result.1 += c,
                2 => result.0 -= c,
                3 => result.1 -= c,
                _ => unreachable!(),
            }
        }
    }
    result
}
fn p(x: i64, y: i64, offset: i64) -> KernelPhasePolynomial {
    let mut phase = KernelPhasePolynomial::default();
    for (condition, n) in [
        (
            KernelBooleanPolynomial::variable(KernelVariable::InputKet(0)),
            x,
        ),
        (
            KernelBooleanPolynomial::variable(KernelVariable::InputBra(0)),
            y,
        ),
        (KernelBooleanPolynomial::one(), offset),
    ] {
        phase.add_boolean(&condition, PhaseCoefficient::rational(ratio(n, 4)));
    }
    phase
}
fn raw_sum(
    atoms: Vec<(KernelPhasePolynomial, i64)>,
    guard: Vec<KernelBooleanPolynomial>,
) -> ExactAggregate {
    BTreeMap::from([(
        super::super::collection::ExactEntry { constraints: guard },
        atoms
            .into_iter()
            .map(|(p, c)| (p, KernelScalar::Rational(integer(c))))
            .collect(),
    )])
}
fn source() -> ExactAggregate {
    // (2 + 3 exp(2 pi i (x+1)/4)) (1 + 2 exp(2 pi i (y+1)/4)).
    // The fourth term has already had its half turn folded into its sign.
    raw_sum(
        vec![
            (p(0, 0, 0), 2),
            (p(1, 0, 1), 3),
            (p(0, 1, 1), 4),
            (p(1, 1, 0), -6),
        ],
        vec![KernelBooleanPolynomial::variable(
            KernelVariable::ClassicalOutput(0),
        )],
    )
}
fn check_all(s: &ExactAggregate, factors: &[ExactAggregate]) {
    for mask in 0u8..8 {
        let inputs = std::array::from_fn(|i| mask & (1u8 << i) != 0);
        assert_eq!(
            value(s, &inputs),
            factors
                .iter()
                .fold((integer(1), integer(0)), |product, f| cmul(
                    product,
                    value(f, &inputs)
                )),
            "assignment={mask}"
        );
    }
}
#[test]
fn folded_half_turn_signs_and_guards_match_independent_semantics() {
    let s = source();
    let factors = factor(&s, &mut budget()).unwrap();
    check_all(&s, &factors);
    for f in &factors {
        assert_eq!(value(f, &[false, false, true]), (integer(0), integer(0)));
    }
    // Without the compensating sign, the same phase rectangle is invalid.
    let mut wrong = s;
    *wrong
        .values_mut()
        .next()
        .unwrap()
        .get_mut(&p(1, 1, 0))
        .unwrap() = KernelScalar::Rational(integer(6));
    assert!(factor(&wrong, &mut budget()).is_none());
}
#[test]
fn complete_modular_phase_relation_not_only_support_is_checked() {
    let p0 = p(0, 0, 0);
    let p1 = p(1, 0, 1);
    let p2 = p(0, 1, 1);
    let p3 = p(1, 1, 0);
    assert_eq!(sign([&p0, &p1, &p2, &p3], &mut budget()), Some(-1));
    assert_eq!(
        sign([&p0, &p(1, 0, 0), &p(0, 1, 0), &p3], &mut budget()),
        Some(1)
    );
    assert_eq!(sign([&p0, &p1, &p2, &p(1, 1, 1)], &mut budget()), None);
    assert_eq!(sign([&p0, &p1, &p2, &p(2, 1, 0)], &mut budget()), None);
}
#[test]
fn every_small_budget_returns_complete_factors_or_preserves_source() {
    let s = source();
    let mut successes = 0;
    for cells in 0..150 {
        let mut owned = Some(s.clone());
        if let Some(factors) = super::factor(&mut owned, &mut { cells }) {
            check_all(&s, &factors);
            assert!(owned.is_none());
            successes += 1;
        } else {
            assert_eq!(owned, Some(s.clone()));
        }
    }
    assert!(successes > 0);
}
#[test]
fn refusal_after_consumption_does_not_expose_a_partial_product() {
    // Noncanonical input with distinct formal atoms denoting opposite phases.
    // Construction merges each binomial to one atom, so refinement refuses.
    let s = raw_sum(
        vec![
            (p(0, 0, 0), 2),
            (p(0, 0, 2), 3),
            (p(1, 0, 0), 4),
            (p(1, 0, 2), 6),
        ],
        vec![],
    );
    let mut owned = Some(s);
    assert!(super::factor(&mut owned, &mut budget()).is_none());
    assert!(owned.is_none());
}
#[test]
fn non_rational_zero_pivots_and_multiple_selectors_are_refused() {
    for coefficient in [
        KernelScalar::Rational(integer(0)),
        KernelScalar::Neg(Box::new(KernelScalar::Rational(integer(2)))),
    ] {
        let mut s = source();
        *s.values_mut()
            .next()
            .unwrap()
            .first_entry()
            .unwrap()
            .get_mut() = coefficient;
        let mut owned = Some(s.clone());
        assert!(super::factor(&mut owned, &mut budget()).is_none());
        assert_eq!(owned, Some(s));
    }
    let mut s = source();
    s.insert(
        super::super::collection::ExactEntry {
            constraints: vec![],
        },
        s.values().next().unwrap().clone(),
    );
    let mut owned = Some(s.clone());
    assert!(super::factor(&mut owned, &mut budget()).is_none());
    assert_eq!(owned, Some(s));
}
#[test]
fn graph_only_phase_or_guard_is_refused_without_flattening() {
    let a = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0)).as_graph();
    let b = KernelBooleanPolynomial::variable(KernelVariable::InputBra(0)).as_graph();
    let c = KernelBooleanPolynomial::variable(KernelVariable::ClassicalOutput(0)).as_graph();
    let graph = KernelBooleanPolynomial::from_graph(a.and(&b.xor(&c)));
    assert!(!graph.is_algebraic());
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(&graph, PhaseCoefficient::rational(ratio(1, 4)));
    assert!(!phase.is_algebraic());
    assert!(
        sign(
            [&phase, &p(0, 0, 0), &p(0, 0, 0), &p(0, 0, 0)],
            &mut budget()
        )
        .is_none()
    );
    let s = source();
    let mut owned = Some(BTreeMap::from([(
        super::super::collection::ExactEntry {
            constraints: vec![graph],
        },
        s.into_values().next().unwrap(),
    )]));
    let before = owned.clone();
    assert!(super::factor(&mut owned, &mut budget()).is_none());
    assert_eq!(owned, before);
}
use super::super::scalar::normalize_scalar;
use super::super::{
    ConstraintNormalization, KernelBooleanPolynomial, KernelVariable, normalize_constraint_span,
};
fn multiply_aggregates(
    left: ExactAggregate,
    right: ExactAggregate,
    cells: &mut usize,
) -> Option<ExactAggregate> {
    super::super::factorization::multiply(left, right, &mut 100_000, cells, |mut t| {
        assert!(t.paths.is_empty());
        match normalize_constraint_span(&mut t.constraints) {
            ConstraintNormalization::Contradiction => Some(None),
            ConstraintNormalization::BudgetExceeded => None,
            ConstraintNormalization::Normalized => Some(Some(ExactTerm {
                constraints: t.constraints,
                coefficient: normalize_scalar(t.coefficient),
                phase: t.phase,
            })),
        }
    })
}

fn factor(source: &ExactAggregate, budget: &mut usize) -> Option<Vec<ExactAggregate>> {
    super::factor(&mut Some(source.clone()), budget)
}

fn budget() -> usize {
    250_000
}

#[test]
fn rectangle_certificate_reconstructs_every_phase_sign_scale_and_guard() {
    let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
    let y = KernelBooleanPolynomial::variable(KernelVariable::InputBra(0));
    for k in 0..8 {
        for b in [-3, -1, 1, 2] {
            for d in [-2, -1, 1, 3] {
                let make = |axis: &KernelBooleanPolynomial, weight, shift| {
                    let mut result = ExactAggregate::new();
                    for (c, phase) in [
                        (integer(1), KernelPhasePolynomial::default()),
                        (integer(weight), {
                            let mut p = KernelPhasePolynomial::default();
                            p.add_boolean(axis, PhaseCoefficient::rational(ratio(1, 4)));
                            p.add_boolean(
                                &KernelBooleanPolynomial::one(),
                                PhaseCoefficient::rational(ratio(shift, 8)),
                            );
                            p
                        }),
                    ] {
                        accumulate_exact_term(
                            ExactTerm {
                                constraints: vec![x.and(&y)],
                                coefficient: KernelScalar::Rational(c),
                                phase,
                            },
                            &mut result,
                            &mut 0,
                        )
                        .unwrap();
                    }
                    result
                };
                let left = make(&x, b, k);
                let right = make(&y, d, 7 - k);
                let source = multiply_aggregates(left, right, &mut budget()).unwrap();
                let result = factor(&source, &mut budget()).expect("complete rational rectangle");
                assert_eq!(
                    multiply_aggregates(result[0].clone(), result[1].clone(), &mut budget())
                        .unwrap(),
                    source
                );
                let mut wrong = source.clone();
                let values = wrong.values_mut().next().unwrap();
                let key = values.keys().last().unwrap().clone();
                values.insert(key, KernelScalar::Rational(integer(17)));
                assert!(factor(&wrong, &mut budget()).is_none());
                let mut wrong = source.clone();
                let values = wrong.values_mut().next().unwrap();
                let key = values.keys().last().unwrap().clone();
                let c = values.remove(&key).unwrap();
                let mut p = key;
                p.add_boolean(&x.and(&y), PhaseCoefficient::rational(ratio(1, 8)));
                values.insert(p, c);
                assert!(factor(&wrong, &mut budget()).is_none());
                let mut missing = source.clone();
                missing.values_mut().next().unwrap().pop_last();
                assert!(factor(&missing, &mut budget()).is_none());
                let mut limited = 0;
                assert!(factor(&source, &mut limited).is_none());
                let mut owned = Some(source.clone());
                assert!(super::factor(&mut owned, &mut limited).is_none());
                assert_eq!(owned, Some(source.clone()));
                assert!(super::factor(&mut owned, &mut budget()).is_some());
                assert!(owned.is_none());
            }
        }
    }
}
