use super::super::scalar::{integer, ratio};
use super::*;
use crate::equivalence::kernel::{KernelPhasePolynomial, KernelScalar};
use crate::symbolic::PhaseCoefficient;
use num_rational::BigRational;

fn var(v: KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v)
}
fn term(weight: i64, guards: Vec<KernelBooleanPolynomial>) -> ExactTerm {
    ExactTerm {
        constraints: guards,
        coefficient: KernelScalar::Rational(integer(weight)),
        phase: KernelPhasePolynomial::default(),
    }
}
fn collect(terms: impl IntoIterator<Item = ExactTerm>) -> ExactAggregate {
    let mut result = ExactAggregate::new();
    let mut count = 0;
    for mut t in terms {
        t.constraints.sort();
        t.constraints.dedup();
        accumulate_exact_term(t, &mut result, &mut count).unwrap();
    }
    result.retain(|_, c| !c.is_empty());
    result
}

// Independent exact evaluator for rational coefficients and Q(i) test phases.
// Unsupported expressions and missing assignments refuse, never approximate.
type Values = BTreeMap<KernelVariable, bool>;
fn boolean(p: &KernelBooleanPolynomial, values: &Values) -> Option<bool> {
    p.as_graph()
        .evaluate::<()>(|v| {
            values
                .get(&KernelVariable::from_graph_variable(v))
                .copied()
                .ok_or(())
        })
        .ok()
}
fn scalar(s: &KernelScalar, values: &Values) -> Option<BigRational> {
    match s {
        KernelScalar::Rational(r) => Some(r.clone()),
        KernelScalar::Add(a, b) => Some(scalar(a, values)? + scalar(b, values)?),
        KernelScalar::Mul(a, b) => Some(scalar(a, values)? * scalar(b, values)?),
        KernelScalar::Neg(a) => Some(-scalar(a, values)?),
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => scalar(
            if boolean(condition, values)? {
                when_true
            } else {
                when_false
            },
            values,
        ),
        _ => None,
    }
}
fn value(sum: &ExactAggregate, values: &Values) -> Option<(BigRational, BigRational)> {
    let mut result = (integer(0), integer(0));
    for (entry, coefficients) in sum {
        let mut enabled = true;
        for row in &entry.constraints {
            enabled &= !boolean(row, values)?;
        }
        if !enabled {
            continue;
        }
        for (phase, coefficient) in coefficients {
            let weight = scalar(coefficient, values)?;
            let mut turns = integer(0);
            for (p, c) in phase.selectors() {
                if boolean(&p, values)? {
                    turns += c.as_rational()?;
                }
            }
            let quarters = turns * integer(4);
            if !quarters.is_integer() {
                return None;
            }
            match i64::try_from(quarters.to_integer()).ok()?.rem_euclid(4) {
                0 => result.0 += weight,
                1 => result.1 += weight,
                2 => result.0 -= weight,
                3 => result.1 -= weight,
                _ => unreachable!(),
            }
        }
    }
    Some(result)
}
fn constant_zero(sum: &ExactAggregate) -> bool {
    value(sum, &Values::new()).is_some_and(|v| v == (integer(0), integer(0)))
}
fn prove(sum: ExactAggregate, mut budget: usize, limit: usize) -> bool {
    prove_zero(sum, &mut budget, 0, limit, &mut constant_zero)
}

#[test]
fn complementary_partitions_prove_zero_for_every_free_coordinate_kind() {
    for v in [
        KernelVariable::InputKet(0),
        KernelVariable::InputBra(0),
        KernelVariable::QuantumOutputKet(0),
        KernelVariable::QuantumOutputBra(0),
        KernelVariable::ClassicalOutput(0),
    ] {
        let x = var(v);
        let difference = collect([
            term(3, vec![x.clone()]),
            term(3, vec![x.complement()]),
            term(-3, vec![]),
        ]);
        assert!(!difference.is_empty());
        assert!(!prove(difference.clone(), 0, 12));
        assert!(!prove(difference.clone(), 1, 0));
        assert!(prove(difference, 1, 12));
    }
}

#[test]
fn opposite_free_branch_values_do_not_cancel_and_both_branches_must_pass() {
    let x = var(KernelVariable::InputKet(0));
    let opposite = collect([term(2, vec![x.clone()]), term(-1, vec![])]);
    assert!(!prove(opposite, 100, 12));
    for condition in [x.clone(), x.complement()] {
        let source = collect([ExactTerm {
            constraints: vec![],
            phase: KernelPhasePolynomial::default(),
            coefficient: KernelScalar::Select {
                condition,
                when_true: Box::new(KernelScalar::Rational(integer(1))),
                when_false: Box::new(KernelScalar::Rational(integer(0))),
            },
        }]);
        assert!(!prove(source, 100, 12));
    }
}

#[test]
fn common_selector_removal_is_only_a_sufficient_zero_obligation() {
    let x = var(KernelVariable::InputKet(0));
    let source = collect([ExactTerm {
        constraints: vec![x.clone()],
        phase: KernelPhasePolynomial::default(),
        coefficient: KernelScalar::Select {
            condition: x,
            when_true: Box::new(KernelScalar::Rational(integer(1))),
            when_false: Box::new(KernelScalar::Rational(integer(0))),
        },
    }]);
    for bit in [false, true] {
        assert_eq!(
            value(&source, &[(KernelVariable::InputKet(0), bit)].into()),
            Some((integer(0), integer(0)))
        );
    }
    // Dropping [x=0] leaves x, which is not identically zero. Refusal cannot be NEQ.
    assert!(!prove(source, 10, 12));
}

#[test]
fn common_free_phase_is_removed_without_spending_split_budget_on_its_variables() {
    let x = var(KernelVariable::InputBra(0));
    let mut terms = [
        term(3, vec![x.clone()]),
        term(3, vec![x.complement()]),
        term(-3, vec![]),
    ];
    for t in &mut terms {
        for i in 0..20 {
            t.phase.add_boolean(
                &var(KernelVariable::InputKet(i)),
                PhaseCoefficient::rational(ratio(1, 7)),
            );
        }
    }
    assert!(prove(collect(terms), 1, 12));
}

#[test]
fn relative_phase_across_distinct_selectors_is_preserved() {
    let x = var(KernelVariable::InputKet(0));
    let mut phased = term(1, vec![]);
    phased
        .phase
        .add_boolean(&x, PhaseCoefficient::rational(ratio(1, 2)));
    assert!(prove(
        collect([
            phased.clone(),
            term(-1, vec![x.clone()]),
            term(1, vec![x.complement()])
        ]),
        1,
        12
    ));
    assert!(!prove(collect([phased, term(-1, vec![])]), 10, 12));
}

#[test]
fn restriction_preserves_complete_scalar_phase_and_guard_semantics() {
    let x = var(KernelVariable::InputKet(0));
    let y = var(KernelVariable::InputBra(0));
    let mut a = term(1, vec![x.xor(&y)]);
    a.phase
        .add_boolean(&x.and(&y), PhaseCoefficient::rational(ratio(1, 4)));
    a.coefficient = KernelScalar::Select {
        condition: x.clone(),
        when_true: Box::new(KernelScalar::Rational(integer(2))),
        when_false: Box::new(KernelScalar::Rational(integer(3))),
    };
    let source = collect([a, term(-2, vec![y])]);
    for bit in [false, true] {
        let restricted = restrict_aggregate(&source, &KernelVariable::InputKet(0), bit).unwrap();
        for other in [false, true] {
            let inputs = [
                (KernelVariable::InputKet(0), bit),
                (KernelVariable::InputBra(0), other),
            ]
            .into();
            assert_eq!(value(&source, &inputs), value(&restricted, &inputs));
        }
    }
}

#[test]
fn uneliminated_bound_paths_and_inconclusive_constants_do_not_prove_equality() {
    let bound = var(KernelVariable::PathKet { term: 0, path: 0 });
    let source = collect([
        term(3, vec![bound.clone()]),
        term(3, vec![bound.complement()]),
        term(-3, vec![]),
    ]);
    assert!(!prove(source, 100, 12));
    let constant = collect([term(1, vec![])]);
    let mut calls = 0;
    assert!(!prove_zero(constant, &mut 1, 0, 12, &mut |_| {
        calls += 1;
        false
    }));
    assert_eq!(calls, 1);
}

#[test]
fn recursive_free_cases_share_budget_instead_of_accepting_a_successful_prefix() {
    let x = var(KernelVariable::InputKet(0));
    let y = var(KernelVariable::InputBra(0));
    let source = collect([
        term(1, vec![x.clone(), y.clone()]),
        term(1, vec![x.clone(), y.complement()]),
        term(1, vec![x.complement(), y.clone()]),
        term(1, vec![x.complement(), y.complement()]),
        term(-1, vec![]),
    ]);
    assert!(!prove(source.clone(), 2, 12));
    assert!(!prove(source.clone(), 3, 1));
    assert!(prove(source, 3, 12));
}
