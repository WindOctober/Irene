use super::*;
use crate::equivalence::kernel::KernelVariable;
use crate::symbolic::PhaseCoefficient;
use num_rational::BigRational;

fn integer(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}
fn input() -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(KernelVariable::InputKet(0))
}
fn term(coefficient: i64, quarter_turns: i64) -> ExactTerm {
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(
        &KernelBooleanPolynomial::one(),
        PhaseCoefficient::rational(ratio(quarter_turns, 4)),
    );
    ExactTerm {
        constraints: vec![],
        coefficient: KernelScalar::Rational(integer(coefficient)),
        phase,
    }
}
fn collect(terms: impl IntoIterator<Item = ExactTerm>) -> ExactAggregate {
    let mut result = ExactAggregate::new();
    let mut atoms = 0;
    for t in terms {
        accumulate_exact_term(t, &mut result, &mut atoms).unwrap();
        assert_eq!(atoms, result.values().map(BTreeMap::len).sum::<usize>());
    }
    result.retain(|_, c| !c.is_empty());
    result
}

// Independent exact Q(i) evaluation of complete selector-bearing terms.
// Structural non-equality is deliberately not treated as semantic inequality.
fn evaluate(t: &ExactTerm, x: bool) -> (BigRational, BigRational) {
    let boolean = |p: &KernelBooleanPolynomial| {
        p.as_graph()
            .evaluate::<std::convert::Infallible>(|v| {
                assert_eq!(
                    KernelVariable::from_graph_variable(v),
                    KernelVariable::InputKet(0)
                );
                Ok(x)
            })
            .unwrap()
    };
    if t.constraints.iter().any(boolean) {
        return (integer(0), integer(0));
    }
    let KernelScalar::Rational(weight) = &t.coefficient else {
        panic!("test expects a rational coefficient")
    };
    let mut turns = integer(0);
    for (p, coefficient) in t.phase.selectors() {
        if boolean(&p) {
            turns += coefficient.as_rational().unwrap();
        }
    }
    let quarters = turns * integer(4);
    assert!(quarters.is_integer());
    let exponent = i64::try_from(quarters.to_integer()).unwrap().rem_euclid(4);
    match exponent {
        0 => (weight.clone(), integer(0)),
        1 => (integer(0), weight.clone()),
        2 => (-weight.clone(), integer(0)),
        3 => (integer(0), -weight.clone()),
        _ => unreachable!(),
    }
}
fn evaluate_sum(sum: &ExactAggregate, x: bool) -> (BigRational, BigRational) {
    let mut result = (integer(0), integer(0));
    for (entry, coefficients) in sum {
        for (phase, coefficient) in coefficients {
            let value = evaluate(
                &ExactTerm {
                    constraints: entry.constraints.clone(),
                    coefficient: coefficient.clone(),
                    phase: phase.clone(),
                },
                x,
            );
            result.0 += value.0;
            result.1 += value.1;
        }
    }
    result
}

#[test]
fn same_selector_and_phase_combine_and_cancel_coherently() {
    for a in -3..=3 {
        for b in -3..=3 {
            let mut left = term(a, 1);
            left.constraints.push(input());
            let mut right = term(b, 1);
            right.constraints.push(input());
            let mut expected = term(a + b, 1);
            expected.constraints.push(input());
            assert_eq!(collect([left, right]), collect([expected]));
        }
    }
}

#[test]
fn half_turn_folding_preserves_both_constant_and_input_dependent_phases() {
    for quarter in -8..=8 {
        for coefficient in -3..=3 {
            let mut original = term(coefficient, quarter);
            original
                .phase
                .add_boolean(&input(), PhaseCoefficient::rational(ratio(1, 4)));
            let collected = collect([original.clone()]);
            for x in [false, true] {
                assert_eq!(evaluate_sum(&collected, x), evaluate(&original, x));
            }
            let mut opposite = original.clone();
            opposite.phase.add_boolean(
                &KernelBooleanPolynomial::one(),
                PhaseCoefficient::rational(ratio(1, 2)),
            );
            assert!(collect([original, opposite]).is_empty());
        }
    }
}

#[test]
fn overlapping_different_selectors_are_not_erased_or_merged() {
    let all = term(2, 0);
    let mut only_zero = term(-2, 0);
    only_zero.constraints.push(input());
    let sum = collect([all, only_zero]);
    assert_eq!(sum.len(), 2);
    assert_eq!(evaluate_sum(&sum, false), (integer(0), integer(0)));
    assert_eq!(evaluate_sum(&sum, true), (integer(2), integer(0)));
}

#[test]
fn input_dependent_half_turn_is_not_treated_as_a_global_sign() {
    let mut selected_sign = term(1, 0);
    selected_sign
        .phase
        .add_boolean(&input(), PhaseCoefficient::rational(ratio(1, 2)));
    let sum = collect([selected_sign, term(-1, 0)]);
    assert!(!sum.is_empty());
    assert_eq!(evaluate_sum(&sum, false), (integer(0), integer(0)));
    assert_eq!(evaluate_sum(&sum, true), (integer(-2), integer(0)));
}

#[test]
fn left_minus_right_preserves_full_guarded_complex_difference() {
    let mut guarded = term(3, 1);
    guarded.constraints.push(input());
    let left = collect([guarded, term(-2, 0)]);
    let right = collect([term(1, 3), term(4, 0)]);
    let difference = aggregate_difference(left.clone(), right.clone()).unwrap();
    for x in [false, true] {
        let l = evaluate_sum(&left, x);
        let r = evaluate_sum(&right, x);
        assert_eq!(evaluate_sum(&difference, x), (l.0 - r.0, l.1 - r.1));
    }
    assert!(aggregate_difference(left.clone(), left).unwrap().is_empty());
}

#[test]
fn a_nonempty_formal_difference_can_still_be_identically_zero() {
    let mut zero = term(1, 0);
    zero.constraints.push(input());
    let mut one = term(1, 0);
    one.constraints.push(input().complement());
    let difference = aggregate_difference(collect([zero, one]), collect([term(1, 0)])).unwrap();
    assert!(!difference.is_empty());
    for x in [false, true] {
        assert_eq!(evaluate_sum(&difference, x), (integer(0), integer(0)));
    }
}

#[test]
fn cancellation_releases_atom_budget_and_zero_terms_use_no_slots() {
    let mut sum = ExactAggregate::new();
    let mut atoms = 0;
    for (coefficient, expected) in [(0, 0), (2, 1), (3, 1), (-5, 0)] {
        accumulate_exact_term(term(coefficient, 0), &mut sum, &mut atoms).unwrap();
        assert_eq!(atoms, expected);
    }
    assert!(sum.values().all(BTreeMap::is_empty));
    for exhausted in [MAX_AGGREGATE_ATOMS, usize::MAX] {
        let mut sum = ExactAggregate::new();
        let mut atoms = exhausted;
        assert!(accumulate_exact_term(term(1, 0), &mut sum, &mut atoms).is_none());
        // None is a refusal, never a zero/equality certificate; discard this map.
    }
}

#[test]
fn oversized_scalar_refuses_collection_instead_of_reporting_success() {
    // Balanced shape exercises the node cap without relying on deep recursion.
    let mut coefficient = KernelScalar::Rational(integer(1));
    for _ in 0..16 {
        coefficient = KernelScalar::Add(Box::new(coefficient.clone()), Box::new(coefficient));
    }
    let mut too_large = term(1, 0);
    too_large.coefficient = coefficient;
    let mut sum = collect([term(2, 1)]);
    assert!(accumulate_exact_term(too_large, &mut sum, &mut 1).is_none());
}
