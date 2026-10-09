use super::super::collection::ExactEntry;
use super::super::{KernelPhasePolynomial, KernelVariable};
use super::*;
use crate::ir::{AstIdGenerator, NumericConstant};

fn split(source: ExactAggregate, algebra: &mut ConstantBudget) -> bool {
    super::super::free_split::prove_zero(source, &mut 4095, 0, 12, &mut |leaf| {
        constant_is_zero(leaf, algebra)
    })
}
fn phase(turns: BigRational) -> KernelPhasePolynomial {
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(
        &KernelBooleanPolynomial::one(),
        PhaseCoefficient::rational(turns),
    );
    phase
}

fn aggregate(
    constraints: Vec<KernelBooleanPolynomial>,
    terms: Vec<(BigRational, KernelScalar)>,
) -> ExactAggregate {
    BTreeMap::from([(
        ExactEntry { constraints },
        terms.into_iter().map(|(p, c)| (phase(p), c)).collect(),
    )])
}

#[test]
fn constant_algebra_rejects_free_and_bound_dependencies_in_every_field() {
    for variable in [
        KernelVariable::InputKet(0),
        KernelVariable::PathKet { term: 0, path: 0 },
    ] {
        let value = KernelBooleanPolynomial::variable(variable);
        let guarded = aggregate(
            vec![value.clone()],
            vec![(integer(0), KernelScalar::Rational(integer(1)))],
        );
        let selected = aggregate(
            vec![],
            vec![(
                integer(0),
                KernelScalar::Select {
                    condition: value.clone(),
                    when_true: Box::new(KernelScalar::Rational(integer(1))),
                    when_false: Box::new(KernelScalar::Rational(integer(0))),
                },
            )],
        );
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(&value, PhaseCoefficient::rational(ratio(1, 2)));
        let phased = BTreeMap::from([(
            ExactEntry {
                constraints: vec![],
            },
            BTreeMap::from([(phase, KernelScalar::Rational(integer(1)))]),
        )]);
        for source in [guarded, selected, phased] {
            assert!(constant_monomial(&source, &mut ConstantBudget::default()).is_none());
            assert!(!constant_is_zero(&source, &mut ConstantBudget::default()));
        }
    }
}

#[test]
fn constant_scalar_normalization_retains_radical_products_and_phase() {
    let root = KernelScalar::Sqrt(Box::new(KernelScalar::Rational(integer(3))));
    let product = KernelScalar::Mul(Box::new(root.clone()), Box::new(root));
    let source = aggregate(vec![], vec![(ratio(1, 8), product)]);
    assert_eq!(
        constant_monomial(&source, &mut ConstantBudget::default()),
        Some((integer(3), ratio(1, 8))),
    );
    for (condition, expected) in [
        (KernelBooleanPolynomial::zero(), integer(2)),
        (KernelBooleanPolynomial::one(), integer(1)),
    ] {
        let source = aggregate(
            vec![],
            vec![(
                integer(0),
                KernelScalar::Select {
                    condition,
                    when_true: Box::new(KernelScalar::Rational(integer(1))),
                    when_false: Box::new(KernelScalar::Rational(integer(2))),
                },
            )],
        );
        assert_eq!(
            constant_monomial(&source, &mut ConstantBudget::default()),
            Some((expected, integer(0))),
        );
    }
}

#[test]
fn cyclotomic_products_cover_all_root_pairs_and_exact_cancellation() {
    for left in 0..256 {
        for right in 0..256 {
            let mut budget = Budget::default();
            let a =
                Cyclotomic::monomial(left * (ROOT_ORDER / 256), ratio(2, 3), &mut budget).unwrap();
            let b =
                Cyclotomic::monomial(right * (ROOT_ORDER / 256), ratio(3, 5), &mut budget).unwrap();
            let power = ((left + right) % 256) * (ROOT_ORDER / 256);
            let expected = BTreeMap::from([(
                power % DEGREE,
                if power >= DEGREE {
                    ratio(-2, 5)
                } else {
                    ratio(2, 5)
                },
            )]);
            assert_eq!(a.multiply(&b, &mut budget).unwrap().0, expected);
        }
    }
    let mut sum = Cyclotomic::default();
    let mut budget = Budget::default();
    for power in 0..256 {
        sum.add_term(power * (ROOT_ORDER / 256), integer(1), &mut budget)
            .unwrap();
    }
    assert!(sum.0.is_empty());
}

#[test]
fn sparse_high_order_powers_and_representation_boundaries() {
    let powers = [0, 1, 2, DEGREE - 1, DEGREE, DEGREE + 1, ROOT_ORDER - 1];
    for left in powers {
        for right in powers {
            let mut budget = Budget::default();
            let a = Cyclotomic::monomial(left, integer(1), &mut budget).unwrap();
            let b = Cyclotomic::monomial(right, integer(1), &mut budget).unwrap();
            let power = (left + right) % ROOT_ORDER;
            assert_eq!(
                a.multiply(&b, &mut budget).unwrap().0,
                BTreeMap::from([(
                    power % DEGREE,
                    integer(if power >= DEGREE { -1 } else { 1 })
                )])
            );
        }
    }
    assert_eq!(
        exponent(&PhaseCoefficient::rational(ratio(1, ROOT_ORDER as i64))),
        Some(1)
    );
    assert_eq!(
        exponent(&PhaseCoefficient::rational(BigRational::new(
            BigInt::from(1),
            BigInt::from(ROOT_ORDER) * 2,
        ))),
        None
    );
    let mut budget = Budget::default();
    let mut value = Cyclotomic::default();
    for power in 0..MAX_VALUE_TERMS {
        value
            .add_term(power as u64, integer(1), &mut budget)
            .unwrap();
    }
    assert!(
        value
            .add_term(MAX_VALUE_TERMS as u64, integer(1), &mut budget)
            .is_none()
    );
}

#[test]
fn exact_trigonometric_values_and_nonnegative_radicals() {
    for numerator in 0..256 {
        let mut ids = AstIdGenerator::default();
        let pi = ids.node(NumericExprKind::Constant(NumericConstant::Pi));
        let scale = ids.node(NumericExprKind::Rational(ratio(numerator, 128)));
        let angle = ids.node(NumericExprKind::Mul(Box::new(pi), Box::new(scale)));
        let mut budget = Budget::default();
        let sin = scalar(&KernelScalar::Sin(angle.clone()), &mut budget).unwrap();
        let cos = scalar(&KernelScalar::Cos(angle), &mut budget).unwrap();
        let squares = sin
            .multiply(&sin, &mut budget)
            .unwrap()
            .add(cos.multiply(&cos, &mut budget).unwrap(), &mut budget)
            .unwrap();
        assert_eq!(squares.0, BTreeMap::from([(0, integer(1))]));
        if numerator == 64 {
            assert_eq!(sin.0, BTreeMap::from([(0, integer(1))]));
        }
    }
    for value in [
        ratio(0, 1),
        ratio(1, 2),
        ratio(2, 1),
        ratio(8, 9),
        ratio(9, 2),
    ] {
        let mut budget = Budget::default();
        let root = scalar(
            &KernelScalar::Sqrt(Box::new(KernelScalar::Rational(value.clone()))),
            &mut budget,
        )
        .unwrap();
        let square = root.multiply(&root, &mut budget).unwrap();
        let expected = Cyclotomic::monomial(0, value, &mut budget).unwrap();
        assert_eq!(square, expected);
    }
}

#[test]
fn constant_zero_budget_is_shared_and_all_free_branches_must_pass() {
    let terms = vec![
        (ratio(1, 8), KernelScalar::Rational(integer(1))),
        (ratio(3, 8), KernelScalar::Rational(integer(-1))),
        (
            integer(0),
            KernelScalar::Neg(Box::new(KernelScalar::Sqrt(Box::new(
                KernelScalar::Rational(integer(2)),
            )))),
        ),
    ];
    let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
    let mut source = aggregate(vec![x.clone()], terms.clone());
    source.extend(aggregate(vec![x.complement()], terms));
    let mut algebra = ConstantBudget(Budget {
        nodes: 1,
        ..Budget::default()
    });
    assert!(!split(source.clone(), &mut algebra));
    assert!(split(source, &mut ConstantBudget::default()));
    let mut nonzero = aggregate(
        vec![x.clone()],
        vec![(integer(0), KernelScalar::Rational(integer(1)))],
    );
    nonzero.extend(aggregate(
        vec![x.complement()],
        vec![(integer(0), KernelScalar::Rational(integer(-1)))],
    ));
    assert!(!split(nonzero, &mut ConstantBudget::default()));
}

#[test]
fn euler_identity_cancels_exactly_but_a_tiny_residual_does_not() {
    // 1 + i - sqrt(2) * exp(i*pi/4) = 0.
    let source = aggregate(
        vec![],
        vec![
            (integer(0), KernelScalar::Rational(integer(1))),
            (ratio(1, 4), KernelScalar::Rational(integer(1))),
            (
                ratio(1, 8),
                KernelScalar::Neg(Box::new(KernelScalar::Sqrt(Box::new(
                    KernelScalar::Rational(integer(2)),
                )))),
            ),
        ],
    );
    assert!(constant_is_zero(&source, &mut ConstantBudget::default()));
    let mut perturbed = source;
    let tiny = BigRational::new(BigInt::from(1), BigInt::from(1) << 100);
    perturbed
        .values_mut()
        .next()
        .unwrap()
        .insert(phase(integer(0)), KernelScalar::Rational(integer(1) + tiny));
    assert!(!constant_is_zero(
        &perturbed,
        &mut ConstantBudget::default()
    ));
}

#[test]
fn unsupported_constants_are_not_zero_certificates() {
    let mut ids = AstIdGenerator::default();
    let radian = ids.node(NumericExprKind::Rational(integer(1)));
    for coefficient in [
        KernelScalar::Sqrt(Box::new(KernelScalar::Rational(integer(-1)))),
        KernelScalar::Sqrt(Box::new(KernelScalar::Rational(integer(3)))),
        KernelScalar::Inverse(Box::new(KernelScalar::Rational(integer(0)))),
        KernelScalar::Sin(radian.clone()),
        KernelScalar::Cos(radian),
    ] {
        let source = aggregate(vec![], vec![(integer(0), coefficient)]);
        assert!(!constant_is_zero(&source, &mut ConstantBudget::default()));
        assert!(constant_monomial(&source, &mut ConstantBudget::default()).is_none());
    }
    let outside_field = aggregate(
        vec![],
        vec![(ratio(1, 3), KernelScalar::Rational(integer(1)))],
    );
    assert!(!constant_is_zero(
        &outside_field,
        &mut ConstantBudget::default()
    ));
    assert!(constant_monomial(&outside_field, &mut ConstantBudget::default()).is_none());
}

#[test]
fn unresolved_xag_guards_and_phases_refuse_without_anf_expansion() {
    let graph_var = |i| KernelBooleanPolynomial::variable(KernelVariable::InputKet(i)).as_graph();
    let graph =
        KernelBooleanPolynomial::from_graph(graph_var(0).and(&graph_var(1).xor(&graph_var(2))));
    let guarded = aggregate(
        vec![graph.clone()],
        vec![(integer(0), KernelScalar::Rational(integer(1)))],
    );
    let selected = aggregate(
        vec![],
        vec![(
            integer(0),
            KernelScalar::Select {
                condition: graph.clone(),
                when_true: Box::new(KernelScalar::Rational(integer(1))),
                when_false: Box::new(KernelScalar::Rational(integer(0))),
            },
        )],
    );
    let mut p = KernelPhasePolynomial::default();
    p.add_boolean(&graph, PhaseCoefficient::rational(ratio(1, 4)));
    let phased = BTreeMap::from([(
        ExactEntry {
            constraints: vec![],
        },
        BTreeMap::from([(p, KernelScalar::Rational(integer(1)))]),
    )]);
    for source in [guarded, selected, phased] {
        assert!(!constant_is_zero(&source, &mut ConstantBudget::default()));
        assert!(constant_monomial(&source, &mut ConstantBudget::default()).is_none());
    }
}

#[test]
fn exact_zero_needs_complete_arithmetic_and_nonzero_values_keep_their_phase() {
    let zero = aggregate(
        vec![],
        vec![
            (integer(0), KernelScalar::Rational(integer(1))),
            (ratio(1, 2), KernelScalar::Rational(integer(1))),
        ],
    );
    assert!(constant_is_zero(&zero, &mut ConstantBudget::default()));
    for (nodes, work, arithmetic) in [
        (0, MAX_WORK, MAX_ARITHMETIC),
        (MAX_CONSTANT_LEAVES, 0, MAX_ARITHMETIC),
        (MAX_CONSTANT_LEAVES, MAX_WORK, 0),
    ] {
        assert!(!constant_is_zero(
            &zero,
            &mut ConstantBudget(Budget {
                nodes,
                work,
                arithmetic
            })
        ));
    }
    let negative = aggregate(
        vec![],
        vec![(ratio(1, 8), KernelScalar::Rational(integer(-3)))],
    );
    assert_eq!(
        constant_monomial(&negative, &mut ConstantBudget::default()),
        Some((integer(3), ratio(5, 8)))
    );
    let disabled = aggregate(
        vec![KernelBooleanPolynomial::one()],
        vec![(integer(0), KernelScalar::Rational(integer(7)))],
    );
    assert!(constant_is_zero(&disabled, &mut ConstantBudget::default()));
}
