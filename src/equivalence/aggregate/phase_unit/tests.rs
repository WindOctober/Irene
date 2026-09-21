use super::super::KernelMonomial;
use super::super::scalar::{integer, ratio};
use super::*;
use crate::symbolic::PhaseCoefficient;

fn selected(condition: KernelBooleanPolynomial, yes: i64, no: i64) -> KernelScalar {
    KernelScalar::Select {
        condition,
        when_true: Box::new(KernelScalar::Rational(integer(yes))),
        when_false: Box::new(KernelScalar::Rational(integer(no))),
    }
}

fn aggregate(coefficient: KernelScalar) -> ExactAggregate {
    BTreeMap::from([(
        ExactEntry {
            constraints: vec![],
        },
        BTreeMap::from([(KernelPhasePolynomial::default(), coefficient)]),
    )])
}

#[test]
fn final_branch_zero_or_different_magnitude_refuses_the_entire_reconstruction() {
    let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
    let y = KernelBooleanPolynomial::variable(KernelVariable::InputBra(0));
    let z = KernelBooleanPolynomial::variable(KernelVariable::ClassicalOutput(0));
    for last in [0, 2] {
        let source = aggregate(selected(x.and(&y).and(&z), last, 1));
        let original = source.clone();
        assert!(collapse(&source).is_none());
        assert_eq!(source, original);
    }
}

#[test]
fn all_free_coordinate_kinds_can_be_reconstructed_but_bound_paths_cannot() {
    for variable in [
        KernelVariable::InputKet(0),
        KernelVariable::InputBra(0),
        KernelVariable::QuantumOutputKet(0),
        KernelVariable::QuantumOutputBra(0),
        KernelVariable::ClassicalOutput(0),
    ] {
        let source = aggregate(selected(
            KernelBooleanPolynomial::variable(variable.clone()),
            -2,
            2,
        ));
        let unit = collapse(&source).unwrap();
        for (bit, expected_turns) in [(false, integer(0)), (true, ratio(1, 2))] {
            let at_bit = restrict_aggregate(&unit, &variable, bit).unwrap();
            assert_eq!(
                witness::constant_monomial(&at_bit, &mut witness::ConstantBudget::default()),
                Some((integer(2), expected_turns))
            );
        }
    }
    for variable in [
        KernelVariable::PathKet { term: 0, path: 0 },
        KernelVariable::PathBra { term: 0, path: 0 },
    ] {
        let source = aggregate(selected(KernelBooleanPolynomial::variable(variable), -2, 2));
        assert!(collapse(&source).is_none());
    }
}

#[test]
fn shared_free_budget_cannot_return_a_partially_reconstructed_function() {
    let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
    let y = KernelBooleanPolynomial::variable(KernelVariable::InputBra(0));
    let z = KernelBooleanPolynomial::variable(KernelVariable::ClassicalOutput(0));
    let source = aggregate(selected(x.xor(&y).xor(&z), -1, 1));
    let original = source.clone();
    assert!(
        super::collapse(
            &source,
            &mut 2_000_000,
            &mut 6,
            &mut witness::ConstantBudget::default()
        )
        .is_none()
    );
    assert_eq!(source, original);
    let unit = super::collapse(
        &source,
        &mut 2_000_000,
        &mut 7,
        &mut witness::ConstantBudget::default(),
    )
    .unwrap();
    for assignment in 0u32..8 {
        let mut leaf = unit.clone();
        for (bit, variable) in [
            KernelVariable::InputKet(0),
            KernelVariable::InputBra(0),
            KernelVariable::ClassicalOutput(0),
        ]
        .iter()
        .enumerate()
        {
            leaf = restrict_aggregate(&leaf, variable, assignment & (1 << bit) != 0).unwrap();
        }
        assert_eq!(
            witness::constant_monomial(&leaf, &mut witness::ConstantBudget::default()),
            Some((integer(1), ratio((assignment.count_ones() % 2) as i64, 2)))
        );
    }
}

#[test]
fn unsupported_graphs_and_distinct_selectors_are_not_silently_omitted() {
    let v = |i| KernelBooleanPolynomial::variable(KernelVariable::InputKet(i));
    let graph = KernelBooleanPolynomial::from_graph(
        v(0).as_graph().and(&v(1).as_graph().xor(&v(2).as_graph())),
    );
    let guarded = BTreeMap::from([(
        ExactEntry {
            constraints: vec![graph.clone()],
        },
        BTreeMap::from([(
            KernelPhasePolynomial::default(),
            KernelScalar::Rational(integer(1)),
        )]),
    )]);
    assert!(collapse(&guarded).is_none());
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(&graph, PhaseCoefficient::rational(ratio(1, 4)));
    let phased = BTreeMap::from([(
        ExactEntry {
            constraints: vec![],
        },
        BTreeMap::from([(phase, KernelScalar::Rational(integer(1)))]),
    )]);
    assert!(collapse(&phased).is_none());
    let mut distinct = aggregate(KernelScalar::Rational(integer(1)));
    distinct.insert(
        ExactEntry {
            constraints: vec![v(0)],
        },
        BTreeMap::from([(
            KernelPhasePolynomial::default(),
            KernelScalar::Rational(integer(1)),
        )]),
    );
    assert!(collapse(&distinct).is_none());
    assert!(collapse(&ExactAggregate::new()).is_none());
}

fn collapse(source: &ExactAggregate) -> Option<ExactAggregate> {
    let mut free = 4095;
    super::collapse(
        source,
        &mut 2_000_000,
        &mut free,
        &mut witness::ConstantBudget::default(),
    )
}

#[test]
fn phase_unit_interpolation_checks_every_cofactor_and_retains_selector() {
    let x = KernelVariable::InputKet(0);
    let y = KernelVariable::InputBra(0);
    let selector = vec![KernelBooleanPolynomial::variable(
        KernelVariable::ClassicalOutput(0),
    )];
    // All 256 functions from two bits to the four quarter-turn roots.
    // Build from independent minterm selectors; verify the returned
    // polynomial against the original integer table, not its own replay.
    for table in 0..256usize {
        let mut source = ExactAggregate::new();
        for assignment in 0..4 {
            let mut condition = KernelBooleanPolynomial::one();
            for (bit, variable) in [x.clone(), y.clone()].into_iter().enumerate() {
                let literal = KernelBooleanPolynomial::variable(variable);
                condition = condition.and(&if assignment & (1 << bit) != 0 {
                    literal
                } else {
                    literal.complement()
                });
            }
            let mut phase = KernelPhasePolynomial::default();
            phase.add_boolean(
                &KernelBooleanPolynomial::one(),
                PhaseCoefficient::rational(ratio(((table >> (2 * assignment)) & 3) as i64, 4)),
            );
            accumulate_exact_term(
                ExactTerm {
                    constraints: selector.clone(),
                    phase,
                    coefficient: KernelScalar::Select {
                        condition,
                        when_true: Box::new(KernelScalar::Rational(integer(3))),
                        when_false: Box::new(KernelScalar::Rational(integer(0))),
                    },
                },
                &mut source,
                &mut 0,
            )
            .unwrap();
        }
        let unit = collapse(&source).unwrap();
        assert_eq!(unit.len(), 1);
        let (entry, values) = unit.first_key_value().unwrap();
        assert_eq!(entry.constraints, selector);
        assert_eq!(values.len(), 1);
        // Accumulation may move a half turn to the signed scalar.
        let (phase, KernelScalar::Rational(scalar)) = values.first_key_value().unwrap() else {
            panic!("not a unit");
        };
        for assignment in 0..4 {
            let mut phase = phase.clone();
            for (bit, variable) in [&x, &y].into_iter().enumerate() {
                phase.substitute(
                    variable,
                    &KernelBooleanPolynomial::from(assignment & (1 << bit) != 0),
                );
            }
            let mut expected =
                PhaseCoefficient::rational(ratio(((table >> (2 * assignment)) & 3) as i64, 4));
            if *scalar == integer(-3) {
                expected = PhaseCoefficient::rational(ratio(
                    ((table >> (2 * assignment)) & 3) as i64 + 2,
                    4,
                ));
            } else {
                assert_eq!(*scalar, integer(3));
            }
            assert_eq!(phase.coefficient(&KernelMonomial::one()), expected);
            assert!(phase.variables().is_empty());
        }
    }
}

#[test]
fn phase_unit_interpolation_refuses_zero_variable_magnitude_and_budget() {
    let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
    for true_value in [0, 2] {
        let source = BTreeMap::from([(
            ExactEntry {
                constraints: vec![x.clone()],
            },
            BTreeMap::from([(
                KernelPhasePolynomial::default(),
                KernelScalar::Select {
                    condition: x.clone(),
                    when_true: Box::new(KernelScalar::Rational(integer(true_value))),
                    when_false: Box::new(KernelScalar::Rational(integer(1))),
                },
            )]),
        )]);
        // Even an inactive selector branch is checked: no zero-factor
        // division or assumption that the selector makes a unit nonzero.
        assert!(collapse(&source).is_none());
    }
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(&x, PhaseCoefficient::rational(ratio(1, 8)));
    let source = BTreeMap::from([(
        ExactEntry {
            constraints: Vec::new(),
        },
        BTreeMap::from([(phase.clone(), KernelScalar::Rational(integer(1)))]),
    )]);
    assert!(collapse(&source).is_some());
    let mut free = 4095;
    assert!(
        super::collapse(
            &source,
            &mut 0,
            &mut free,
            &mut witness::ConstantBudget::default()
        )
        .is_none()
    );
    assert!(
        super::collapse(
            &source,
            &mut 2_000_000,
            &mut 0,
            &mut witness::ConstantBudget::default()
        )
        .is_none()
    );
    for index in 1..9 {
        phase.add_boolean(
            &KernelBooleanPolynomial::variable(KernelVariable::InputKet(index)),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    let oversized = BTreeMap::from([(
        ExactEntry {
            constraints: Vec::new(),
        },
        BTreeMap::from([(phase, KernelScalar::Rational(integer(1)))]),
    )]);
    assert!(collapse(&oversized).is_none());
    let mut unsupported = KernelPhasePolynomial::default();
    unsupported.add_boolean(
        &KernelBooleanPolynomial::one(),
        PhaseCoefficient::rational(ratio(1, 3)),
    );
    let unsupported = BTreeMap::from([(
        ExactEntry {
            constraints: Vec::new(),
        },
        BTreeMap::from([(unsupported, KernelScalar::Rational(integer(1)))]),
    )]);
    assert!(collapse(&unsupported).is_none());
}
