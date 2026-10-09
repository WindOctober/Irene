use super::super::scalar::{normalize_scalar, ratio};
use super::super::{ConstraintNormalization, KernelMonomial, normalize_constraint_span};
use super::*;
use crate::symbolic::PhaseCoefficient;

fn atom_sum(
    selector: Vec<KernelBooleanPolynomial>,
    phases: Vec<KernelPhasePolynomial>,
) -> ExactAggregate {
    let mut sum = ExactAggregate::new();
    for phase in phases {
        accumulate_exact_term(
            ExactTerm {
                constraints: selector.clone(),
                coefficient: KernelScalar::Rational(integer(1)),
                phase,
            },
            &mut sum,
            &mut 0,
        )
        .unwrap();
    }
    sum
}
fn phase(variable: KernelVariable, denominator: i64) -> KernelPhasePolynomial {
    let mut result = KernelPhasePolynomial::default();
    result.add_boolean(
        &KernelBooleanPolynomial::variable(variable),
        PhaseCoefficient::rational(ratio(1, denominator)),
    );
    result
}
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
fn equal(
    left: &ExactAggregate,
    right: &ExactAggregate,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
) -> bool {
    left == right
        || super::super::collection::aggregate_difference(left.clone(), right.clone()).is_some_and(
            |difference| {
                super::super::free_split::prove_zero(difference, free, 0, 12, &mut |s| {
                    witness::constant_is_zero(s, algebra)
                })
            },
        )
}

fn checked_match(
    left: &ExactAggregate,
    right: &ExactAggregate,
    mut probes: usize,
) -> Option<ExactAggregate> {
    matching_unit(
        left,
        right,
        &mut 250_000,
        &mut 4095,
        &mut witness::ConstantBudget::default(),
        &mut probes,
        &mut |unit, cells, free, algebra| {
            multiply_aggregates(right.clone(), unit.clone(), cells)
                .map(|r| equal(left, &r, free, algebra))
        },
    )
}

#[test]
fn atom_ratio_candidate_requires_complete_replay_not_just_one_matching_atom() {
    // Nine coordinates exclude exhaustive interpolation. The fallback must
    // propose a ratio from atoms, then verify the complete guarded equation.
    let mut p = KernelPhasePolynomial::default();
    for i in 0..9 {
        p.add_boolean(
            &KernelBooleanPolynomial::variable(KernelVariable::InputKet(i)),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    let guard = vec![KernelBooleanPolynomial::variable(
        KernelVariable::ClassicalOutput(0),
    )];
    let right = atom_sum(guard.clone(), vec![KernelPhasePolynomial::default()]);
    let mut left = atom_sum(guard.clone(), vec![p.clone()]);
    *left
        .values_mut()
        .next()
        .unwrap()
        .values_mut()
        .next()
        .unwrap() = KernelScalar::Rational(integer(2));
    assert!(
        relative_phase_unit(
            &left,
            &right,
            &mut 250_000,
            &mut 4095,
            &mut witness::ConstantBudget::default()
        )
        .is_none()
    );
    let unit = checked_match(&left, &right, 128).unwrap();
    assert!(equal(
        &left,
        &multiply_aggregates(right.clone(), unit, &mut 250_000).unwrap(),
        &mut 4095,
        &mut witness::ConstantBudget::default()
    ));
    let mut calls = 0;
    assert!(
        matching_unit(
            &left,
            &right,
            &mut 250_000,
            &mut 4095,
            &mut witness::ConstantBudget::default(),
            &mut 128,
            &mut |_, _, _, _| {
                calls += 1;
                Some(false)
            }
        )
        .is_none()
    );
    assert!(calls > 0);
    assert!(checked_match(&left, &right, 0).is_none());
    accumulate_exact_term(
        ExactTerm {
            constraints: guard,
            coefficient: KernelScalar::Rational(integer(1)),
            phase: KernelPhasePolynomial::default(),
        },
        &mut left,
        &mut 0,
    )
    .unwrap();
    assert!(checked_match(&left, &right, 128).is_none());
}

#[test]
fn reconstructed_candidate_still_requires_the_original_guarded_relation() {
    let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
    let right = atom_sum(vec![x.clone()], vec![KernelPhasePolynomial::default()]);
    let mut left = right.clone();
    *left
        .values_mut()
        .next()
        .unwrap()
        .values_mut()
        .next()
        .unwrap() = KernelScalar::Rational(integer(2));
    assert!(
        relative_phase_unit(
            &left,
            &right,
            &mut 250_000,
            &mut 4095,
            &mut witness::ConstantBudget::default()
        )
        .is_some()
    );
    assert!(
        matching_unit(
            &left,
            &right,
            &mut 250_000,
            &mut 4095,
            &mut witness::ConstantBudget::default(),
            &mut 128,
            &mut |_, _, _, _| Some(false)
        )
        .is_none()
    );
    assert!(checked_match(&left, &right, 128).is_some());
    let differently_guarded =
        atom_sum(vec![x.complement()], vec![KernelPhasePolynomial::default()]);
    assert!(checked_match(&left, &differently_guarded, 128).is_none());
}

#[test]
fn unresolved_graph_phases_do_not_enter_the_binomial_polynomial_template() {
    let v = |i| KernelBooleanPolynomial::variable(KernelVariable::InputKet(i)).as_graph();
    let graph = KernelBooleanPolynomial::from_graph(v(0).and(&v(1).xor(&v(2))));
    let mut p = KernelPhasePolynomial::default();
    p.add_boolean(&graph, PhaseCoefficient::rational(ratio(1, 4)));
    let sum = atom_sum(vec![], vec![KernelPhasePolynomial::default(), p]);
    assert!(conditional_binomial_unit(&sum, &sum, &mut 250_000).is_none());
    assert!(
        relative_phase_unit(
            &sum,
            &sum,
            &mut 250_000,
            &mut 4095,
            &mut witness::ConstantBudget::default()
        )
        .is_none()
    );
}

#[test]
fn relative_unit_interpolation_checks_zero_leaves_scale_and_every_phase() {
    let variables = [
        KernelVariable::InputKet(0),
        KernelVariable::InputBra(0),
        KernelVariable::ClassicalOutput(0),
        KernelVariable::ClassicalOutput(1),
    ];
    let [x, y, c, d] = variables.clone().map(KernelBooleanPolynomial::variable);
    let mut p = KernelPhasePolynomial::default();
    for (row, turns) in [(&y, ratio(1, 2)), (&c, ratio(3, 4)), (&d, ratio(1, 2))] {
        p.add_boolean(row, PhaseCoefficient::rational(turns));
    }
    // L=[x=y]+[x=y XOR c](-1)^(y+d)(-i)^c.
    let mut left = atom_sum(vec![x.xor(&y)], vec![KernelPhasePolynomial::default()]);
    for (entry, coefficients) in atom_sum(vec![x.xor(&y).xor(&c)], vec![p]) {
        for (phase, coefficient) in coefficients {
            accumulate_exact_term(
                ExactTerm {
                    constraints: entry.constraints.clone(),
                    coefficient,
                    phase,
                },
                &mut left,
                &mut 0,
            )
            .unwrap();
        }
    }
    // R=(1+(-1)^(x+d)i^c)(1+(-1)^(y+d)i^c).
    let factors = [&x, &y].map(|row| {
        let mut p = KernelPhasePolynomial::default();
        p.add_boolean(&row.xor(&d), PhaseCoefficient::rational(ratio(1, 2)));
        p.add_boolean(&c, PhaseCoefficient::rational(ratio(1, 4)));
        atom_sum(vec![], vec![KernelPhasePolynomial::default(), p])
    });
    let right = multiply_aggregates(factors[0].clone(), factors[1].clone(), &mut 250_000).unwrap();
    let unit = relative_phase_unit(
        &left,
        &right,
        &mut 250_000,
        &mut 4095,
        &mut witness::ConstantBudget::default(),
    )
    .unwrap();
    let reconstructed = multiply_aggregates(right.clone(), unit.clone(), &mut 250_000).unwrap();
    assert!(equal(
        &left,
        &reconstructed,
        &mut 4095,
        &mut witness::ConstantBudget::default()
    ));
    // Independent integer bit formula for the ratio on all nonzero
    // entries: magnitude 1/2, quarter-turn exponent -c*(1+2*(y+d)).
    // R is zero precisely when c=0 and either x!=d or y!=d.
    for assignment in 0..16 {
        let bits = std::array::from_fn::<_, 4, _>(|i| (assignment >> i) & 1);
        let mut at_point = unit.clone();
        for (variable, bit) in variables.iter().zip(bits) {
            at_point = restrict_aggregate(&at_point, variable, bit != 0).unwrap();
        }
        if bits[2] == 0 && (bits[0] != bits[3] || bits[1] != bits[3]) {
            continue;
        }
        let (magnitude, turns) =
            witness::constant_monomial(&at_point, &mut witness::ConstantBudget::default()).unwrap();
        assert_eq!(magnitude, ratio(1, 2));
        let exponent: i64 = -(bits[2] as i64) * (1 + 2 * (bits[1] + bits[3]) as i64);
        assert_eq!(
            PhaseCoefficient::rational(turns),
            PhaseCoefficient::rational(ratio(exponent, 4))
        );
    }
    let propose = |l: &ExactAggregate, r: &ExactAggregate| {
        relative_phase_unit(
            l,
            r,
            &mut 250_000,
            &mut 4095,
            &mut witness::ConstantBudget::default(),
        )
    };
    let mut wrong_scale = left.clone();
    for coefficients in wrong_scale.values_mut() {
        for scalar in coefficients.values_mut() {
            *scalar = scalar.clone().multiply(KernelScalar::Select {
                condition: c.clone(),
                when_true: Box::new(KernelScalar::Rational(integer(2))),
                when_false: Box::new(KernelScalar::Rational(integer(1))),
            });
        }
    }
    assert!(propose(&wrong_scale, &right).is_none()); // agrees at all-zero
    let mut missing = left.clone();
    missing.pop_last();
    assert!(propose(&missing, &right).is_none());
    let zero = ExactAggregate::new();
    assert!(propose(&left, &zero).is_none());
    assert!(propose(&zero, &right).is_none());
    let mut exhausted = 0;
    assert!(
        relative_phase_unit(
            &left,
            &right,
            &mut exhausted,
            &mut 4095,
            &mut witness::ConstantBudget::default()
        )
        .is_none()
    );
    assert!(
        relative_phase_unit(
            &left,
            &right,
            &mut 250_000,
            &mut 0,
            &mut witness::ConstantBudget::default()
        )
        .is_none()
    );
    // Common selectors may be removed only as a stronger proof. A
    // different selector on one side remains and prevents the identity.
    let guard = atom_sum(
        vec![KernelBooleanPolynomial::variable(KernelVariable::InputKet(
            50,
        ))],
        vec![KernelPhasePolynomial::default()],
    );
    let guarded_left = multiply_aggregates(left, guard.clone(), &mut 250_000).unwrap();
    let guarded_right = multiply_aggregates(right.clone(), guard, &mut 250_000).unwrap();
    assert!(propose(&guarded_left, &guarded_right).is_some());
    assert!(propose(&guarded_left, &right).is_none());
    let too_many = atom_sum(
        vec![],
        vec![{
            let mut p = KernelPhasePolynomial::default();
            for i in 0..9 {
                p.add_boolean(
                    &KernelBooleanPolynomial::variable(KernelVariable::InputKet(i)),
                    PhaseCoefficient::rational(ratio(1, 8)),
                );
            }
            p
        }],
    );
    assert!(propose(&too_many, &too_many).is_none());
}

#[test]
fn conditional_binomial_orientation_replays_all_flip_assignments() {
    let a = KernelVariable::QuantumOutputKet(1);
    let b = KernelVariable::QuantumOutputBra(1);
    let flip = KernelBooleanPolynomial::variable(a.clone())
        .xor(&KernelBooleanPolynomial::variable(b.clone()));
    let mut right_phase = phase(KernelVariable::InputKet(0), 2);
    right_phase.add_boolean(
        &KernelBooleanPolynomial::one(),
        PhaseCoefficient::rational(ratio(1, 1024)),
    );
    right_phase.add_boolean(
        &KernelBooleanPolynomial::variable(a.clone()),
        PhaseCoefficient::rational(ratio(1, 4)),
    );
    let mut budget = 250_000;
    let unit_phase = negative_gated_phase(&right_phase, &flip, &mut budget).unwrap();
    let mut left_phase = right_phase.clone();
    add_phase(&mut left_phase, &unit_phase).unwrap();
    add_phase(&mut left_phase, &unit_phase).unwrap();
    let guard = KernelBooleanPolynomial::variable(KernelVariable::InputBra(7));
    let left = atom_sum(
        vec![guard.clone()],
        vec![KernelPhasePolynomial::default(), left_phase.clone()],
    );
    let right = atom_sum(
        vec![guard.clone()],
        vec![KernelPhasePolynomial::default(), right_phase],
    );
    let unit = conditional_binomial_unit(&left, &right, &mut budget).unwrap();
    let replay = multiply_aggregates(right.clone(), unit, &mut budget).unwrap();
    for x in [false, true] {
        for y in [false, true] {
            // Independent literal cofactors check the whole guarded sum.
            let restrict = |source| {
                restrict_aggregate(&restrict_aggregate(source, &a, x).unwrap(), &b, y).unwrap()
            };
            assert_eq!(restrict(&left), restrict(&replay));
        }
    }
    let mut bad_phase = left_phase;
    bad_phase.add_boolean(
        &KernelBooleanPolynomial::one(),
        PhaseCoefficient::rational(ratio(1, 16)),
    );
    let wrong = atom_sum(
        vec![guard],
        vec![KernelPhasePolynomial::default(), bad_phase],
    );
    assert!(conditional_binomial_unit(&wrong, &right, &mut budget).is_none());
    let mut exhausted = 0;
    assert!(conditional_binomial_unit(&left, &right, &mut exhausted).is_none());
}

#[test]
fn orientation_tree_handles_nonlinear_flips_and_refuses_one_bad_branch() {
    let a = KernelVariable::QuantumOutputKet(0);
    let b = KernelVariable::QuantumOutputBra(0);
    let flip = KernelBooleanPolynomial::variable(a.clone())
        .and(&KernelBooleanPolynomial::variable(b.clone()))
        .complement();
    let right_phase = phase(KernelVariable::InputKet(0), 8);
    let mut budget = 250_000;
    let unit = negative_gated_phase(&right_phase, &flip, &mut budget).unwrap();
    let mut left_phase = right_phase.clone();
    add_phase(&mut left_phase, &unit).unwrap();
    add_phase(&mut left_phase, &unit).unwrap();
    let proved = orientation_phase(&left_phase, &right_phase, &mut budget, 0).unwrap();
    for x in [false, true] {
        for y in [false, true] {
            for input in [false, true] {
                let specialize = |mut phase: KernelPhasePolynomial| {
                    for (variable, value) in [
                        (a.clone(), x),
                        (b.clone(), y),
                        (KernelVariable::InputKet(0), input),
                    ] {
                        phase.substitute(&variable, &KernelBooleanPolynomial::from(value));
                    }
                    phase
                };
                assert_eq!(specialize(proved.clone()), specialize(unit.clone()));
            }
        }
    }
    assert!(orientation_phase(&left_phase, &right_phase, &mut budget, 4).is_none());
    left_phase.add_boolean(
        &KernelBooleanPolynomial::variable(a).and(&KernelBooleanPolynomial::variable(b)),
        PhaseCoefficient::rational(ratio(1, 16)),
    );
    assert!(orientation_phase(&left_phase, &right_phase, &mut budget, 0).is_none());
}

#[test]
fn wide_orientation_proves_all_eight_branches_with_bounded_syntax() {
    let variables = [
        KernelVariable::QuantumOutputKet(0),
        KernelVariable::QuantumOutputBra(0),
        KernelVariable::QuantumOutputBra(1),
    ];
    let flip = variables
        .iter()
        .fold(KernelBooleanPolynomial::zero(), |sum, var| {
            sum.xor(&KernelBooleanPolynomial::variable(var.clone()))
        });
    let make = |count| {
        let mut right = KernelPhasePolynomial::default();
        for index in 0..count {
            right.add_boolean(
                &KernelBooleanPolynomial::variable(KernelVariable::InputKet(index)),
                PhaseCoefficient::rational(ratio(1, 64)),
            );
        }
        let mut left = right.clone();
        for (monomial, coefficient) in right.terms() {
            left.add_boolean(
                &flip.and(&KernelBooleanPolynomial::from_monomial(monomial.clone())),
                coefficient.scaled(BigInt::from(-2)),
            );
        }
        (left, right)
    };
    let (left, right) = make(64);
    assert_eq!(left.term_count(), MAX_ORIENTATION_LEFT_TERMS);
    let mut budget = 250_000;
    let unit = orientation_phase(&left, &right, &mut budget, 0).unwrap();
    let proposed = parity_orientation_phase(&left, &right, &mut 250_000).unwrap();
    assert_eq!(proposed, unit);
    let negative = KernelPhasePolynomial::difference(&KernelPhasePolynomial::default(), &right);
    for bits in 0u8..8 {
        let mut actual = unit.clone();
        let mut oriented = left.clone();
        for (index, variable) in variables.iter().enumerate() {
            let value = KernelBooleanPolynomial::from(bits & (1 << index) != 0);
            actual.substitute(variable, &value);
            oriented.substitute(variable, &value);
        }
        // Check the entire remaining 64-coordinate polynomial, not a
        // sample of those inputs. The expected parity is computed here
        // directly from the eight literal assignments.
        let odd = bits.count_ones() % 2 != 0;
        assert_eq!(
            actual,
            if odd {
                negative.clone()
            } else {
                KernelPhasePolynomial::default()
            }
        );
        assert_eq!(oriented, if odd { negative.clone() } else { right.clone() });
    }
    let mut wrong = left.clone();
    let corner = variables
        .iter()
        .fold(KernelBooleanPolynomial::one(), |term, var| {
            term.and(&KernelBooleanPolynomial::variable(var.clone()))
        });
    // Reuse an existing monomial: stay within 512 terms, but corrupt
    // exactly the all-one orientation branch.
    wrong.add_boolean(
        &corner.and(&KernelBooleanPolynomial::variable(
            KernelVariable::InputKet(0),
        )),
        PhaseCoefficient::rational(ratio(1, 128)),
    );
    assert_eq!(wrong.term_count(), left.term_count());
    assert!(parity_orientation_phase(&wrong, &right, &mut 250_000).is_none());
    assert!(orientation_phase(&wrong, &right, &mut 250_000, 0).is_none());
    let (oversized, oversized_right) = make(65);
    assert!(orientation_phase(&oversized, &oversized_right, &mut 250_000, 0).is_none());
    let mut exhausted = 1;
    assert!(orientation_phase(&left, &right, &mut exhausted, 0).is_none());
    assert!(parity_orientation_phase(&left, &right, &mut exhausted).is_none());
}

#[test]
fn large_parity_orientation_checks_all_sixty_four_branches_and_whole_polynomials() {
    let variables = (0..6)
        .map(KernelVariable::QuantumOutputBra)
        .collect::<Vec<_>>();
    let flip = variables
        .iter()
        .fold(KernelBooleanPolynomial::zero(), |p, v| {
            p.xor(&KernelBooleanPolynomial::variable(v.clone()))
        });
    let mut right = KernelPhasePolynomial::default();
    for i in 0..24 {
        right.add_boolean(
            &KernelBooleanPolynomial::variable(KernelVariable::InputKet(i)),
            PhaseCoefficient::rational(ratio(1, 4096)),
        );
    }
    let mut left = right.clone();
    for (m, c) in right.terms() {
        left.add_boolean(
            &flip.and(&KernelBooleanPolynomial::from_monomial(m.clone())),
            c.scaled(BigInt::from(-2)),
        );
    }
    assert_eq!(left.term_count(), 1536);
    assert!(orientation_phase(&left, &right, &mut 250_000, 0).is_none());
    let mut budget = 250_000;
    let unit = large_parity_orientation_phase(&left, &right, &mut budget).unwrap();
    let needed = 250_000 - budget;
    let selector = vec![KernelBooleanPolynomial::variable(KernelVariable::InputBra(
        99,
    ))];
    let l = atom_sum(
        selector.clone(),
        vec![KernelPhasePolynomial::default(), left.clone()],
    );
    let r = atom_sum(
        selector.clone(),
        vec![KernelPhasePolynomial::default(), right.clone()],
    );
    let certified = conditional_binomial_unit(&l, &r, &mut 250_000).unwrap();
    assert_eq!(certified, atom_sum(Vec::new(), vec![unit.clone()]));
    assert!(
        conditional_binomial_unit(
            &l,
            &atom_sum(
                Vec::new(),
                vec![KernelPhasePolynomial::default(), right.clone()]
            ),
            &mut 250_000
        )
        .is_none()
    );
    let mut wrong_weight = r.clone();
    *wrong_weight
        .values_mut()
        .next()
        .unwrap()
        .values_mut()
        .next()
        .unwrap() = KernelScalar::Rational(integer(2));
    assert!(conditional_binomial_unit(&l, &wrong_weight, &mut 250_000).is_none());
    for bits in 0u32..64 {
        let specialize = |mut p: KernelPhasePolynomial| {
            for (i, v) in variables.iter().enumerate() {
                p.substitute(v, &KernelBooleanPolynomial::from(bits & (1 << i) != 0));
            }
            p
        };
        let negative = KernelPhasePolynomial::difference(&KernelPhasePolynomial::default(), &right);
        assert_eq!(
            specialize(unit.clone()),
            if bits.count_ones() % 2 != 0 {
                negative.clone()
            } else {
                KernelPhasePolynomial::default()
            }
        );
        assert_eq!(
            specialize(left.clone()),
            if bits.count_ones() % 2 != 0 {
                negative
            } else {
                right.clone()
            }
        );
    }
    let mut wrong = left.clone();
    wrong.add_term(
        KernelMonomial::from_variables(
            variables
                .iter()
                .cloned()
                .chain([KernelVariable::InputKet(0)]),
        ),
        PhaseCoefficient::rational(ratio(1, 4096)),
    );
    assert_eq!(wrong.term_count(), 1536);
    assert!(large_parity_orientation_phase(&wrong, &right, &mut 250_000).is_none());
    let mut short = needed - 1;
    assert!(large_parity_orientation_phase(&left, &right, &mut short).is_none());
    let mut exact = needed;
    assert!(large_parity_orientation_phase(&left, &right, &mut exact).is_some());
    assert_eq!(exact, 0);
    let mut bound = left.clone();
    bound.add_term(
        KernelMonomial::variable(KernelVariable::PathKet { term: 0, path: 0 }),
        PhaseCoefficient::rational(ratio(1, 8)),
    );
    assert!(large_parity_orientation_phase(&bound, &right, &mut 250_000).is_none());
    let mut oversized = left;
    for i in 100..2200 {
        oversized.add_term(
            KernelMonomial::variable(KernelVariable::InputKet(i)),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    assert!(large_parity_orientation_phase(&oversized, &right, &mut 250_000).is_none());
}

#[test]
fn literal_gate_charges_its_actual_single_product_bound() {
    let flip = KernelBooleanPolynomial::variable(KernelVariable::InputBra(0));
    let mut source = KernelPhasePolynomial::default();
    let mut expected = KernelPhasePolynomial::default();
    for index in 0..64 {
        let variable = KernelBooleanPolynomial::variable(KernelVariable::InputKet(index));
        source.add_boolean(&variable, PhaseCoefficient::rational(ratio(1, 8)));
        expected.add_boolean(
            &variable.and(&flip),
            PhaseCoefficient::rational(ratio(-1, 8)),
        );
    }
    let mut budget = 64 * 3; // 64 products, each one monomial + two variables.
    assert_eq!(
        negative_gated_phase(&source, &flip, &mut budget),
        Some(expected)
    );
    assert_eq!(budget, 0);
    budget = 64 * 3 - 1;
    assert!(negative_gated_phase(&source, &flip, &mut budget).is_none());
    assert_eq!(source.term_count(), 64);
}
