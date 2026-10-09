use super::super::collection::ExactEntry;
use super::super::scalar::ratio;
use super::super::{KernelBooleanPolynomial, KernelVariable};
use super::*;
use crate::symbolic::PhaseCoefficient;

type Complex = (BigRational, BigRational);
fn multiply(a: Complex, b: Complex) -> Complex {
    (&a.0 * &b.0 - &a.1 * &b.1, a.0 * b.1 + a.1 * b.0)
}
fn variable(i: usize) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(KernelVariable::InputKet(i))
}
fn boolean(p: &KernelBooleanPolynomial, inputs: &[bool]) -> bool {
    p.as_graph()
        .evaluate::<()>(|v| {
            let KernelVariable::InputKet(i) = KernelVariable::from_graph_variable(v) else {
                panic!("unexpected test variable")
            };
            Ok(inputs[i])
        })
        .unwrap()
}
fn scalar(s: &KernelScalar, inputs: &[bool]) -> BigRational {
    match s {
        KernelScalar::Rational(r) => r.clone(),
        KernelScalar::Add(a, b) => scalar(a, inputs) + scalar(b, inputs),
        KernelScalar::Mul(a, b) => scalar(a, inputs) * scalar(b, inputs),
        KernelScalar::Neg(a) => -scalar(a, inputs),
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => scalar(
            if boolean(condition, inputs) {
                when_true
            } else {
                when_false
            },
            inputs,
        ),
        _ => panic!("unsupported test coefficient"),
    }
}
// Independent Q(i) interpretation: no production normalization or replay.
fn exponential(p: &KernelPhasePolynomial, inputs: &[bool]) -> Complex {
    let mut turns = integer(0);
    for (condition, coefficient) in p.selectors() {
        if boolean(&condition, inputs) {
            turns += coefficient.as_rational().unwrap();
        }
    }
    let quarters = turns * integer(4);
    assert!(quarters.is_integer());
    match i64::try_from(quarters.to_integer()).unwrap().rem_euclid(4) {
        0 => (integer(1), integer(0)),
        1 => (integer(0), integer(1)),
        2 => (integer(-1), integer(0)),
        3 => (integer(0), integer(-1)),
        _ => unreachable!(),
    }
}
fn value(s: &ExactAggregate, inputs: &[bool]) -> Complex {
    let mut result = (integer(0), integer(0));
    for (entry, coefficients) in s {
        if entry.constraints.iter().any(|p| boolean(p, inputs)) {
            continue;
        }
        for (p, a) in coefficients {
            let v = multiply((scalar(a, inputs), integer(0)), exponential(p, inputs));
            result.0 += v.0;
            result.1 += v.1;
        }
    }
    result
}
fn term(
    weight: BigRational,
    guard: Vec<KernelBooleanPolynomial>,
    p: KernelPhasePolynomial,
) -> ExactTerm {
    ExactTerm {
        constraints: guard,
        coefficient: KernelScalar::Rational(weight),
        phase: p,
    }
}
fn collect(terms: impl IntoIterator<Item = ExactTerm>) -> ExactAggregate {
    let mut result = ExactAggregate::new();
    for t in terms {
        accumulate_exact_term(t, &mut result, &mut 0).unwrap();
    }
    result.retain(|_, coefficients| !coefficients.is_empty());
    result
}
fn phase(conditions: &[(KernelBooleanPolynomial, i64)]) -> KernelPhasePolynomial {
    let mut p = KernelPhasePolynomial::default();
    for (condition, quarter_turns) in conditions {
        p.add_boolean(
            condition,
            PhaseCoefficient::rational(ratio(*quarter_turns, 4)),
        );
    }
    p
}
fn check_all(source: ExactAggregate, bits: usize) {
    let (normalized, scale, p) = normalize(source.clone()).unwrap();
    assert_ne!(scale, integer(0));
    for assignment in 0..(1 << bits) {
        let inputs = (0..bits)
            .map(|i| assignment & (1 << i) != 0)
            .collect::<Vec<_>>();
        let unit = multiply((scale.clone(), integer(0)), exponential(&p, &inputs));
        assert_eq!(
            value(&source, &inputs),
            multiply(unit, value(&normalized, &inputs)),
            "assignment={assignment}"
        );
    }
}

#[test]
fn rational_scales_signs_and_input_dependent_phases_reconstruct_exactly() {
    for a in [-3, -1, 1, 2] {
        for b in [-2, -1, 1, 3] {
            for offset in 0..4 {
                let common = phase(&[(variable(0), 1), (KernelBooleanPolynomial::one(), offset)]);
                let mut shifted = common.clone();
                shifted.add_boolean(&variable(1), PhaseCoefficient::rational(ratio(1, 2)));
                check_all(
                    collect([
                        term(ratio(a, 3), vec![], common),
                        term(ratio(b, 5), vec![], shifted),
                    ]),
                    2,
                );
            }
        }
    }
}

#[test]
fn differently_guarded_entries_and_their_zero_sets_are_preserved() {
    let x = variable(0);
    let y = variable(1);
    check_all(
        collect([
            term(integer(2), vec![x.clone()], phase(&[(y.clone(), 1)])),
            term(integer(-3), vec![x.complement()], phase(&[(y.clone(), 2)])),
            term(ratio(1, 2), vec![y], KernelPhasePolynomial::default()),
        ]),
        2,
    );
}

#[test]
fn variable_scalar_is_transformed_but_is_not_used_as_a_divisor() {
    let x = variable(0);
    let mut selected = term(integer(1), vec![], phase(&[(variable(1), 1)]));
    selected.coefficient = KernelScalar::Select {
        condition: x,
        when_true: Box::new(KernelScalar::Rational(integer(0))),
        when_false: Box::new(KernelScalar::Rational(integer(3))),
    };
    // The selected coefficient may vanish. The other rational atom supplies
    // a safe pivot; the entire selected expression must remain in the result.
    check_all(
        collect([
            selected.clone(),
            term(integer(2), vec![], KernelPhasePolynomial::default()),
        ]),
        2,
    );
    assert!(normalize(collect([selected])).is_none());
}

#[test]
fn zero_and_oversized_or_nonrational_pivots_refuse() {
    assert!(normalize(ExactAggregate::new()).is_none());
    for coefficient in [
        KernelScalar::Rational(integer(0)),
        KernelScalar::Rational(BigRational::from_integer(
            num_bigint::BigInt::from(1) << 4096,
        )),
        KernelScalar::Sqrt(Box::new(KernelScalar::Rational(integer(2)))),
    ] {
        let source = BTreeMap::from([(
            ExactEntry {
                constraints: vec![],
            },
            BTreeMap::from([(KernelPhasePolynomial::default(), coefficient)]),
        )]);
        assert!(normalize(source).is_none());
    }
}

#[test]
fn scalar_graph_conditions_and_nonlinear_guards_remain_semantic() {
    let graph = KernelBooleanPolynomial::from_graph(
        variable(0)
            .as_graph()
            .and(&variable(1).as_graph().xor(&variable(2).as_graph())),
    );
    let mut selected = term(integer(1), vec![graph.clone()], phase(&[(variable(1), 1)]));
    selected.coefficient = KernelScalar::Select {
        condition: graph,
        when_true: Box::new(KernelScalar::Rational(integer(5))),
        when_false: Box::new(KernelScalar::Rational(integer(-2))),
    };
    check_all(
        collect([
            selected,
            term(integer(3), vec![], phase(&[(variable(2), 2)])),
        ]),
        3,
    );
}

#[test]
fn unflattened_phase_refusal_cannot_erase_its_selector() {
    let graph = KernelBooleanPolynomial::from_graph(
        variable(0)
            .as_graph()
            .and(&variable(1).as_graph().xor(&variable(2).as_graph())),
    );
    let p = phase(&[(graph, 1)]);
    let source = collect([term(integer(2), vec![], p)]);
    // The replay helper admits flat phase polynomials only. Preserve the
    // original expression at the caller rather than dropping a graph phase.
    assert!(normalize(source).is_none());
}
