use super::*;
use crate::symbolic::PhaseCoefficient;

fn q(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}
fn path(i: usize) -> KernelVariable {
    KernelVariable::PathKet { term: 0, path: i }
}
fn bit(i: usize) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(path(i))
}
fn rational(n: i64) -> KernelScalar {
    KernelScalar::Rational(q(n, 1))
}
fn value(n: i64) -> Cyclotomic {
    Cyclotomic::from_terms([(0, q(n, 1))], &mut Budget::new(100)).unwrap()
}
fn run(
    paths: &BTreeSet<KernelVariable>,
    guards: &[KernelBooleanPolynomial],
    scalar: &KernelScalar,
    phase: &KernelPhasePolynomial,
) -> Cyclotomic {
    evaluate(paths, guards, scalar, phase, &mut Budget::new(2_000_000)).unwrap()
}

#[test]
fn complete_sums_preserve_interference_and_vacuous_factors() {
    for n in 0..=4 {
        assert_eq!(
            run(
                &(0..n).map(path).collect(),
                &[],
                &rational(1),
                &KernelPhasePolynomial::default()
            ),
            value(1 << n)
        );
    }
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(&bit(7), PhaseCoefficient::rational(q(1, 2)));
    assert!(run(&[path(7)].into(), &[], &rational(1), &phase).is_zero());
    assert_eq!(
        run(&[path(7)].into(), &[bit(7)], &rational(1), &phase),
        value(1)
    );
}

#[test]
fn select_weights_and_quarter_turns_are_summed_as_amplitudes() {
    let weight = KernelScalar::Select {
        condition: bit(9),
        when_true: Box::new(rational(3)),
        when_false: Box::new(rational(1)),
    };
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(&bit(9), PhaseCoefficient::rational(q(1, 4)));
    let result = run(&[path(9)].into(), &[], &weight, &phase);
    let expected = Cyclotomic::from_terms(
        [(0, q(1, 1)), (super::super::cyclotomic::ORDER / 4, q(3, 1))],
        &mut Budget::new(100),
    )
    .unwrap();
    assert_eq!(result, expected);
    assert_eq!(
        result.norm_squared(&mut Budget::new(100)).unwrap(),
        value(10)
    );
}

#[test]
fn generated_half_turn_sums_match_independent_integer_enumeration() {
    let paths = [path(2), path(7), path(19)].into();
    for seed in 0..16 {
        let condition = bit(2).xor(&bit(7).and(&bit(19)));
        let guard = if seed & 1 == 0 {
            bit(2).xor(&bit(7))
        } else {
            bit(19)
        };
        let sign = if seed & 2 == 0 {
            bit(7).and(&bit(19))
        } else {
            bit(2).xor(&bit(19))
        };
        let weight = KernelScalar::Select {
            condition,
            when_true: Box::new(rational(seed - 3)),
            when_false: Box::new(rational(2)),
        };
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(&sign, PhaseCoefficient::rational(q(1, 2)));
        let mut expected = 0;
        for mask in 0..8 {
            let (a, b, c) = (mask & 1 != 0, mask & 2 != 0, mask & 4 != 0);
            if if seed & 1 == 0 { a ^ b } else { c } {
                continue;
            }
            let weight = if a ^ (b & c) { seed - 3 } else { 2 };
            let negative = if seed & 2 == 0 { b & c } else { a ^ c };
            expected += if negative { -weight } else { weight };
        }
        assert_eq!(run(&paths, &[guard], &weight, &phase), value(expected));
    }
}

#[test]
fn invalid_dead_branches_and_false_guards_do_not_hide_errors() {
    let bad = KernelScalar::Inverse(Box::new(rational(0)));
    let select = KernelScalar::Select {
        condition: KernelBooleanPolynomial::zero(),
        when_true: Box::new(bad.clone()),
        when_false: Box::new(rational(1)),
    };
    for weight in [bad, select] {
        assert!(
            evaluate(
                &BTreeSet::new(),
                &[KernelBooleanPolynomial::one()],
                &weight,
                &KernelPhasePolynomial::default(),
                &mut Budget::new(1000)
            )
            .is_none()
        );
    }
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(&bit(0), PhaseCoefficient::rational(q(1, 3)));
    assert!(
        evaluate(
            &[path(0)].into(),
            &[KernelBooleanPolynomial::one()],
            &rational(1),
            &phase,
            &mut Budget::new(1000)
        )
        .is_none()
    );
}

#[test]
fn free_and_undeclared_variables_refuse_in_all_positions() {
    for p in [
        bit(99),
        KernelBooleanPolynomial::variable(KernelVariable::InputKet(0)),
    ] {
        let paths = [path(0)].into();
        let empty = KernelPhasePolynomial::default();
        assert!(
            evaluate(
                &paths,
                &[p.clone()],
                &rational(1),
                &empty,
                &mut Budget::new(1000)
            )
            .is_none()
        );
        let mut phase = empty.clone();
        phase.add_boolean(&p, PhaseCoefficient::rational(q(1, 2)));
        assert!(evaluate(&paths, &[], &rational(1), &phase, &mut Budget::new(1000)).is_none());
        let weight = KernelScalar::Select {
            condition: p,
            when_true: Box::new(rational(1)),
            when_false: Box::new(rational(2)),
        };
        assert!(evaluate(&paths, &[], &weight, &empty, &mut Budget::new(1000)).is_none());
    }
    assert!(
        evaluate(
            &[KernelVariable::InputKet(0)].into(),
            &[],
            &rational(1),
            &KernelPhasePolynomial::default(),
            &mut Budget::new(1000)
        )
        .is_none()
    );
}

#[test]
fn every_budget_returns_either_the_complete_sum_or_refusal() {
    let paths = [path(0), path(1), path(2)].into();
    let phase = KernelPhasePolynomial::default();
    let mut successes = 0;
    let mut refusals = 0;
    for work in 0..200 {
        match evaluate(&paths, &[], &rational(1), &phase, &mut Budget::new(work)) {
            Some(result) => {
                assert_eq!(result, value(8));
                successes += 1;
            }
            None => refusals += 1,
        }
    }
    assert!(successes > 0 && refusals > 0);
    assert!(
        evaluate(
            &(0..17).map(path).collect(),
            &[],
            &rational(1),
            &phase,
            &mut Budget::new(2_000_000)
        )
        .is_none()
    );
}
