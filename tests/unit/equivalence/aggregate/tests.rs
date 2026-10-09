use super::super::kernel::KernelClassicalOutput;
use super::*;

fn kernel(terms: Vec<KernelTerm>) -> DensityKernel {
    DensityKernel {
        input_pairs: Vec::new(),
        quantum_output_count: 0,
        classical_output_count: 0,
        terms,
    }
}

fn term(coefficient: i64) -> KernelTerm {
    KernelTerm {
        ket_guard: Vec::new(),
        bra_guard: Vec::new(),
        history_equalities: Vec::new(),
        ket_paths: BTreeSet::new(),
        bra_paths: BTreeSet::new(),
        quantum_outputs_ket: Vec::new(),
        quantum_outputs_bra: Vec::new(),
        classical_outputs: Vec::new(),
        weight: super::super::kernel::KernelWeight {
            ket: rational(coefficient),
            bra: rational(1),
        },
        phase: super::super::kernel::KernelPhaseDifference {
            ket: KernelPhasePolynomial::default(),
            bra: KernelPhasePolynomial::default(),
        },
    }
}

fn rational(value: i64) -> KernelScalar {
    KernelScalar::Rational(integer(value))
}

fn multiply(left: KernelScalar, right: KernelScalar) -> KernelScalar {
    KernelScalar::Mul(Box::new(left), Box::new(right))
}

fn variable(variable: KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(variable)
}

fn affine(variables: impl IntoIterator<Item = KernelVariable>) -> KernelBooleanPolynomial {
    variables
        .into_iter()
        .fold(KernelBooleanPolynomial::zero(), |value, variable| {
            value.xor(&KernelBooleanPolynomial::variable(variable))
        })
}

#[test]
fn sparse_kernel_substitutions_match_distributive_reference() {
    let variables = [
        KernelVariable::InputKet(0),
        KernelVariable::PathBra { term: 0, path: 0 },
    ];
    let x = variable(variables[0].clone());
    let y = variable(variables[1].clone());
    let atoms = [
        KernelBooleanPolynomial::one(),
        x.clone(),
        y.clone(),
        x.and(&y),
    ];
    let polynomial = |bits: usize| {
        atoms
            .iter()
            .enumerate()
            .fold(KernelBooleanPolynomial::zero(), |sum, (i, m)| {
                if bits & (1 << i) == 0 {
                    sum
                } else {
                    sum.xor(m)
                }
            })
    };
    for bits in 0..16 {
        let source = polynomial(bits);
        for replacement_bits in 0..16 {
            let replacement = polynomial(replacement_bits);
            for v in &variables {
                let expand = |monomial: &KernelMonomial| {
                    monomial
                        .variables()
                        .fold(KernelBooleanPolynomial::one(), |product, current| {
                            product.and(&if current == v {
                                replacement.clone()
                            } else {
                                variable(current.clone())
                            })
                        })
                };
                let reference = source
                    .terms()
                    .fold(KernelBooleanPolynomial::zero(), |sum, monomial| {
                        sum.xor(&expand(monomial))
                    });
                assert_eq!(source.substitute(v, &replacement), reference);
                let mut phase = KernelPhasePolynomial::default();
                for (i, monomial) in source.terms().enumerate() {
                    phase.add_boolean(
                        &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                        crate::symbolic::PhaseCoefficient::rational(ratio(1, [8, 3, 4, 7][i])),
                    );
                }
                let mut reference = KernelPhasePolynomial::default();
                for (monomial, coefficient) in phase.terms() {
                    reference.add_boolean(&expand(monomial), coefficient.clone());
                }
                phase.substitute(v, &replacement);
                assert_eq!(phase, reference);
            }
        }
    }
}

#[test]
fn multi_term_coefficients_are_added_coherently() {
    let left = kernel(vec![term(1), term(2)]);
    let right = kernel(vec![term(3)]);

    assert!(exact_aggregate_match(&left, &right));
}

#[test]
fn multi_term_coefficients_cancel_exactly() {
    let left = kernel(vec![term(1), term(-1)]);
    let right = kernel(Vec::new());

    assert!(exact_aggregate_match(&left, &right));
}

#[test]
fn path_dependent_outputs_are_alpha_renamed_by_free_index_reification() {
    fn with_paths(owner: usize, ket_path: usize, bra_path: usize) -> DensityKernel {
        let mut value = term(1);
        let ket = KernelVariable::PathKet {
            term: owner,
            path: ket_path,
        };
        let bra = KernelVariable::PathBra {
            term: owner,
            path: bra_path,
        };
        value.ket_paths.insert(ket.clone());
        value.bra_paths.insert(bra.clone());
        value.quantum_outputs_ket = vec![variable(ket)];
        value.quantum_outputs_bra = vec![variable(bra)];
        DensityKernel {
            input_pairs: Vec::new(),
            quantum_output_count: 1,
            classical_output_count: 0,
            terms: vec![value],
        }
    }

    assert!(exact_aggregate_match(
        &with_paths(0, 0, 1),
        &with_paths(91, 17, 23)
    ));
}

#[test]
fn free_indices_are_never_accepted_as_bound_paths() {
    let mut malformed = term(1);
    malformed
        .ket_paths
        .insert(KernelVariable::QuantumOutputKet(0));

    assert!(exact_aggregate_match(
        &kernel(vec![malformed.clone()]),
        &kernel(vec![term(1)])
    ));
    assert!(!exact_aggregate_match(
        &kernel(vec![malformed]),
        &kernel(vec![term(2)])
    ));
}

#[test]
fn quantum_ket_and_bra_output_indices_remain_distinct() {
    let ket_input = variable(KernelVariable::InputKet(0));
    let bra_input = variable(KernelVariable::InputBra(0));
    let mut direct = term(1);
    direct.quantum_outputs_ket = vec![ket_input.clone()];
    direct.quantum_outputs_bra = vec![bra_input.clone()];
    let mut swapped = term(1);
    swapped.quantum_outputs_ket = vec![bra_input];
    swapped.quantum_outputs_bra = vec![ket_input];

    let mut left = kernel(vec![direct]);
    left.quantum_output_count = 1;
    let mut right = kernel(vec![swapped]);
    right.quantum_output_count = 1;
    assert!(!exact_aggregate_match(&left, &right));
}

#[test]
fn one_shared_classical_index_enforces_both_dephasing_deltas() {
    let ket = variable(KernelVariable::InputKet(0));
    let bra = variable(KernelVariable::InputBra(0));
    let mut dephased = term(1);
    dephased.classical_outputs = vec![KernelClassicalOutput {
        ket: ket.clone(),
        bra,
    }];
    let mut diagonal_only = term(1);
    diagonal_only.classical_outputs = vec![KernelClassicalOutput {
        ket: ket.clone(),
        bra: ket,
    }];

    let mut left = kernel(vec![dephased]);
    left.classical_output_count = 1;
    let mut right = kernel(vec![diagonal_only]);
    right.classical_output_count = 1;
    assert!(!exact_aggregate_match(&left, &right));

    let aggregate = reduce_kernel(&left).expect("the affine deltas reduce exactly");
    let variables = aggregate
        .keys()
        .flat_map(|entry| &entry.constraints)
        .flat_map(KernelBooleanPolynomial::variables)
        .collect::<BTreeSet<_>>();
    assert!(variables.contains(&KernelVariable::ClassicalOutput(0)));
    assert!(!variables.contains(&KernelVariable::QuantumOutputKet(0)));
    assert!(!variables.contains(&KernelVariable::QuantumOutputBra(0)));
}

#[test]
fn dependent_affine_constraint_bases_have_one_exact_rref() {
    let a = KernelVariable::InputKet(0);
    let b = KernelVariable::InputKet(1);
    let c = KernelVariable::InputKet(2);
    let mut left = term(1);
    left.ket_guard = vec![
        affine([a.clone(), b.clone()]),
        affine([b.clone(), c.clone()]),
    ];
    let mut right = term(1);
    right.ket_guard = vec![affine([a, c.clone()]), affine([b, c])];

    assert!(exact_aggregate_match(
        &kernel(vec![left]),
        &kernel(vec![right])
    ));
}

#[test]
fn nonlinear_constraint_row_operations_preserve_the_selector() {
    let x = variable(KernelVariable::InputKet(0));
    let y = variable(KernelVariable::InputKet(1));
    let z = variable(KernelVariable::InputKet(2));
    let xy = x.and(&y);
    let xz = x.and(&z);
    let mut original = term(1);
    original.ket_guard = vec![xy.clone(), xz.clone()];
    let mut changed_basis = term(1);
    changed_basis.ket_guard = vec![xy.xor(&xz), xz];

    assert!(exact_aggregate_match(
        &kernel(vec![original]),
        &kernel(vec![changed_basis])
    ));
}

#[test]
fn constraint_span_is_sufficient_not_a_complete_boolean_ideal() {
    let x = variable(KernelVariable::InputKet(0));
    let y = variable(KernelVariable::InputKet(1));
    let mut left = term(1);
    left.ket_guard = vec![x.clone()];
    let mut right = term(1);
    // xy=0 follows from x=0, but is not in its linear ANF span.
    right.ket_guard = vec![x.clone(), x.and(&y)];
    assert!(matches!(
        normalize_constraint_span(&mut left.ket_guard),
        ConstraintNormalization::Normalized
    ));
    assert!(matches!(
        normalize_constraint_span(&mut right.ket_guard),
        ConstraintNormalization::Normalized
    ));
    assert_ne!(left.ket_guard, right.ket_guard);
    // The selector layer can now discharge this particular implication
    // using x=0, without claiming completeness for general Boolean ideals.
    assert!(exact_aggregate_match(
        &kernel(vec![left]),
        &kernel(vec![right])
    ));
}

#[test]
fn nonlinear_selector_difference_is_not_erased() {
    let x = variable(KernelVariable::InputKet(0));
    let y = variable(KernelVariable::InputKet(1));
    let mut left = term(1);
    left.ket_guard = vec![x.and(&y)];
    let mut right = term(1);
    right.ket_guard = vec![x.xor(&y)];
    assert!(!exact_aggregate_match(
        &kernel(vec![left]),
        &kernel(vec![right])
    ));
}

#[test]
fn affine_selector_substitution_preserves_free_coordinates() {
    let x = variable(KernelVariable::InputKet(0));
    let y = variable(KernelVariable::QuantumOutputKet(0));
    let mut restricted = term(1);
    restricted.ket_guard = vec![x.xor(&y)];
    assert!(!exact_aggregate_match(
        &kernel(vec![restricted]),
        &kernel(vec![term(1)])
    ));
}

#[test]
fn boolean_preflight_fast_bound_matches_full_monomial_count() {
    let x = KernelVariable::InputKet(0);
    let y = KernelVariable::InputKet(1);
    let basis = [
        KernelBooleanPolynomial::one(),
        variable(x.clone()),
        variable(y.clone()),
        variable(x.clone()).and(&variable(y.clone())),
    ];
    let polynomial = |mask: u8| {
        basis
            .iter()
            .enumerate()
            .fold(KernelBooleanPolynomial::zero(), |sum, (index, term)| {
                if mask & (1 << index) != 0 {
                    sum.xor(term)
                } else {
                    sum
                }
            })
    };
    let check = |source: &KernelBooleanPolynomial, replacement: &KernelBooleanPolynomial| {
        let expected = source
            .terms()
            .map(|term| {
                if term.contains(&x) {
                    replacement.term_count()
                } else {
                    1
                }
            })
            .sum::<usize>()
            <= MAX_BOOLEAN_TERMS;
        let actual = boolean_substitution_within_budget(source, &x, replacement);
        assert_eq!(actual, expected);
        actual
    };
    for left in 0..16 {
        for right in 0..16 {
            check(&polynomial(left), &polynomial(right));
        }
    }
    let mut source = KernelBooleanPolynomial::zero();
    let mut replacement = KernelBooleanPolynomial::zero();
    for index in 2..2002 {
        source = source.xor(&variable(KernelVariable::InputKet(index)));
        if index < 102 {
            replacement = replacement.xor(&variable(KernelVariable::InputBra(index)));
        }
    }
    // The loose bound refuses, but the exact fallback distinguishes
    // zero/one/all occurrences of x. No growth is accepted by truncation.
    assert!(check(&source, &replacement));
    assert!(check(&source.xor(&variable(x.clone())), &replacement));
    assert!(!check(&source.and(&variable(x.clone())), &replacement));
}

#[test]
fn equal_size_pivots_keep_candidate_order_despite_phase_occurrences() {
    let p = KernelVariable::PathKet { term: 0, path: 0 };
    let q = KernelVariable::PathKet { term: 0, path: 1 };
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(
        &variable(p.clone()),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    let working = WorkingTerm {
        paths: BTreeSet::from([p.clone(), q.clone()]),
        constraints: vec![
            variable(p.clone())
                .xor(&variable(q.clone()))
                .xor(&variable(KernelVariable::InputKet(0))),
        ],
        coefficient: rational(1),
        phase,
    };
    let (chosen, replacement) = working.best_constraint_pivot().unwrap();
    assert_eq!(chosen, p);
    assert_eq!(
        replacement,
        variable(q).xor(&variable(KernelVariable::InputKet(0)))
    );
    assert!(working.substitution_within_budget(&chosen, &replacement));
}

#[test]
fn sparse_pivot_search_preserves_the_original_candidate_order() {
    let paths = BTreeSet::from([
        KernelVariable::PathKet { term: 0, path: 0 },
        KernelVariable::PathBra { term: 0, path: 0 },
        KernelVariable::PathBra { term: 0, path: 99 },
    ]);
    let x = variable(paths.first().unwrap().clone());
    let y = variable(KernelVariable::PathBra { term: 0, path: 0 });
    let atoms = [
        KernelBooleanPolynomial::one(),
        x.clone(),
        y.clone(),
        x.and(&y),
    ];
    let polynomial = |bits: usize| {
        atoms
            .iter()
            .enumerate()
            .fold(KernelBooleanPolynomial::zero(), |sum, (i, m)| {
                if bits & (1 << i) == 0 {
                    sum
                } else {
                    sum.xor(m)
                }
            })
    };
    for f in 0..16 {
        for g in 0..16 {
            let working = WorkingTerm {
                paths: paths.clone(),
                constraints: vec![polynomial(f), polynomial(g)],
                coefficient: rational(1),
                phase: KernelPhasePolynomial::default(),
            };
            let reference = working
                .constraints
                .iter()
                .flat_map(|equation| {
                    paths.iter().filter_map(move |v| {
                        let atom = KernelMonomial::variable(v.clone());
                        if !equation.has_term(&atom)
                            || equation
                                .terms()
                                .any(|term| term != &atom && term.contains(v))
                        {
                            return None;
                        }
                        Some((v.clone(), equation.xor(&variable(v.clone()))))
                    })
                })
                .min_by_key(|(_, replacement)| replacement.term_count());
            assert_eq!(working.best_constraint_pivot(), reference);
        }
    }
}

#[test]
fn affine_selector_substitution_preserves_phase_and_scalar_pointwise() {
    let x = variable(KernelVariable::InputKet(0));
    let y = variable(KernelVariable::InputBra(0));
    let monomials = [
        KernelBooleanPolynomial::one(),
        x.clone(),
        y.clone(),
        x.and(&y),
    ];
    for bits in 0..16 {
        let extra =
            monomials
                .iter()
                .enumerate()
                .fold(KernelBooleanPolynomial::zero(), |sum, (i, m)| {
                    if bits & (1 << i) == 0 {
                        sum
                    } else {
                        sum.xor(m)
                    }
                });
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(
            &x.and(&y),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        let coefficient = KernelScalar::Select {
            condition: x.clone(),
            when_true: Box::new(rational(2)),
            when_false: Box::new(rational(3)),
        };
        let constraints = vec![x.xor(&y).complement(), extra];
        let mut working = WorkingTerm {
            paths: BTreeSet::new(),
            constraints: constraints.clone(),
            coefficient: coefficient.clone(),
            phase: phase.clone(),
        };
        let result = working.normalize_selector();
        assert!(!matches!(result, ConstraintNormalization::BudgetExceeded));
        for assignment in 0..4 {
            let values = [
                (
                    KernelVariable::InputKet(0),
                    KernelBooleanPolynomial::from(assignment & 1 != 0),
                ),
                (
                    KernelVariable::InputBra(0),
                    KernelBooleanPolynomial::from(assignment & 2 != 0),
                ),
            ];
            let holds = |rows: &[KernelBooleanPolynomial]| {
                rows.iter().all(|row| {
                    values
                        .iter()
                        .fold(row.clone(), |row, (v, f)| row.substitute(v, f))
                        .is_zero()
                })
            };
            let before = holds(&constraints);
            assert_eq!(
                before,
                !matches!(result, ConstraintNormalization::Contradiction)
                    && holds(&working.constraints)
            );
            if before {
                let eval_scalar = |scalar: &KernelScalar| {
                    normalize_scalar(
                        values
                            .iter()
                            .fold(scalar.clone(), |s, (v, f)| s.substitute(v, f)),
                    )
                };
                let eval_phase = |phase: &KernelPhasePolynomial| {
                    let mut phase = phase.clone();
                    for (v, f) in &values {
                        phase.substitute(v, f);
                    }
                    phase
                };
                assert_eq!(eval_scalar(&coefficient), eval_scalar(&working.coefficient));
                assert_eq!(eval_phase(&phase), eval_phase(&working.phase));
            }
        }
    }
}

#[test]
fn affine_selector_exposes_new_equalities_in_nonlinear_rows() {
    let x = variable(KernelVariable::InputKet(0));
    let y = variable(KernelVariable::InputKet(1));
    let z = variable(KernelVariable::InputKet(2));
    let mut original = term(1);
    original.ket_guard = vec![x.xor(&y), x.and(&y).xor(&z), x.xor(&z).complement()];
    // x=y implies xy=x, so the other two equations contradict each other.
    assert!(exact_aggregate_match(
        &kernel(vec![original]),
        &kernel(Vec::new())
    ));
}

#[test]
fn constraint_span_refuses_an_oversized_matrix() {
    let mut constraints = vec![variable(KernelVariable::InputKet(0)); 4_000];
    constraints[0] = affine((0..3_000).map(KernelVariable::InputKet));
    assert!(matches!(
        normalize_constraint_span(&mut constraints),
        ConstraintNormalization::BudgetExceeded
    ));
}

#[test]
fn nonlinear_row_span_preserves_all_two_variable_equation_pairs() {
    let x = variable(KernelVariable::InputKet(0));
    let y = variable(KernelVariable::InputKet(1));
    let monomials = [
        KernelBooleanPolynomial::one(),
        x.clone(),
        y.clone(),
        x.and(&y),
    ];
    let polynomial = |bits: usize| {
        monomials
            .iter()
            .enumerate()
            .fold(KernelBooleanPolynomial::zero(), |sum, (i, m)| {
                if bits & (1 << i) == 0 {
                    sum
                } else {
                    sum.xor(m)
                }
            })
    };
    let holds = |rows: &[KernelBooleanPolynomial], bits: usize| {
        rows.iter().all(|row| {
            row.substitute(
                &KernelVariable::InputKet(0),
                &KernelBooleanPolynomial::from(bits & 1 != 0),
            )
            .substitute(
                &KernelVariable::InputKet(1),
                &KernelBooleanPolynomial::from(bits & 2 != 0),
            )
            .is_zero()
        })
    };
    for f in 0..16 {
        for g in 0..16 {
            let original = vec![polynomial(f), polynomial(g)];
            let mut reduced = original.clone();
            let result = normalize_constraint_span(&mut reduced);
            assert!(!matches!(result, ConstraintNormalization::BudgetExceeded));
            for input in 0..4 {
                let reduced_holds = !matches!(result, ConstraintNormalization::Contradiction)
                    && holds(&reduced, input);
                assert_eq!(
                    holds(&original, input),
                    reduced_holds,
                    "f={f} g={g} input={input}"
                );
            }
            let mut changed = vec![
                polynomial(f ^ g),
                polynomial(f),
                KernelBooleanPolynomial::zero(),
            ];
            let changed_result = normalize_constraint_span(&mut changed);
            assert_eq!(
                matches!(result, ConstraintNormalization::Contradiction),
                matches!(changed_result, ConstraintNormalization::Contradiction)
            );
            if matches!(result, ConstraintNormalization::Normalized) {
                assert_eq!(reduced, changed);
            }
        }
    }
}

#[test]
fn bounded_residual_weight_sum_adds_both_branches_exactly() {
    let mut residual = term(1);
    let path = KernelVariable::PathKet { term: 0, path: 0 };
    residual.ket_paths.insert(path.clone());
    residual.weight.ket = KernelScalar::Select {
        condition: variable(path),
        when_true: Box::new(rational(3)),
        when_false: Box::new(rational(5)),
    };
    assert!(exact_aggregate_match(
        &kernel(vec![residual.clone()]),
        &kernel(vec![term(8)])
    ));
    assert!(!exact_aggregate_match(
        &kernel(vec![residual]),
        &kernel(vec![term(4)])
    ));
}

#[test]
fn residual_sum_preserves_interference_and_half_turn_cancellation() {
    let path = KernelVariable::PathKet { term: 0, path: 0 };
    let mut summed = term(1);
    summed.ket_paths.insert(path.clone());
    summed.weight.ket = KernelScalar::Select {
        condition: variable(path.clone()),
        when_true: Box::new(rational(3)),
        when_false: Box::new(rational(5)),
    };
    summed.phase.ket.add_boolean(
        &variable(path),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
    );
    assert!(exact_aggregate_match(
        &kernel(vec![summed.clone()]),
        &kernel(vec![term(2)])
    ));
    assert!(!exact_aggregate_match(
        &kernel(vec![summed]),
        &kernel(vec![term(8)])
    ));

    let mut negative = term(1);
    negative.phase.ket.add_boolean(
        &KernelBooleanPolynomial::one(),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
    );
    assert!(exact_aggregate_match(
        &kernel(vec![term(1), negative]),
        &kernel(Vec::new())
    ));
    let mut imaginary = term(1);
    imaginary.phase.ket.add_boolean(
        &KernelBooleanPolynomial::one(),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 4)),
    );
    assert!(!exact_aggregate_match(
        &kernel(vec![imaginary]),
        &kernel(vec![term(1)])
    ));
}

#[test]
fn residual_sum_keeps_free_input_phase_dependence() {
    let path = KernelVariable::PathKet { term: 0, path: 0 };
    let input = variable(KernelVariable::InputKet(0));
    let mut summed = term(1);
    summed.ket_paths.insert(path.clone());
    summed.weight.ket = KernelScalar::Select {
        condition: variable(path.clone()),
        when_true: Box::new(rational(3)),
        when_false: Box::new(rational(5)),
    };
    summed.phase.ket.add_boolean(
        &variable(path).and(&input),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
    );
    let mut expected = term(3);
    expected.phase.ket.add_boolean(
        &input,
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
    );
    assert!(exact_aggregate_match(
        &kernel(vec![summed.clone()]),
        &kernel(vec![term(5), expected])
    ));
    assert!(!exact_aggregate_match(
        &kernel(vec![summed]),
        &kernel(vec![term(8)])
    ));
}

#[test]
fn free_cofactors_prove_complementary_selector_partitions() {
    let x = variable(KernelVariable::InputKet(0));
    let mut zero = term(3);
    zero.ket_guard = vec![x.clone()];
    let mut one = term(3);
    one.ket_guard = vec![x.complement()];
    assert!(exact_aggregate_match(
        &kernel(vec![zero.clone(), one.clone()]),
        &kernel(vec![term(3)])
    ));
    let difference = aggregate_difference(
        reduce_kernel(&kernel(vec![zero, one])).unwrap(),
        reduce_kernel(&kernel(vec![term(3)])).unwrap(),
    )
    .unwrap();
    assert!(!zero_by_free_splitting(difference.clone(), &mut 0, 0));
    assert!(!zero_by_free_splitting(
        difference.clone(),
        &mut 1,
        MAX_FREE_SPLIT_DEPTH
    ));
    assert!(zero_by_free_splitting(difference, &mut 1, 0));
}

#[test]
fn free_branches_must_each_match_not_cancel_each_other() {
    let mut one_branch = term(2);
    one_branch.ket_guard = vec![variable(KernelVariable::InputBra(0))];
    // The two programs have equal sums over the free coordinate (2), but
    // their pointwise values are (2,0) and (1,1). Never sum these branches.
    assert!(!exact_aggregate_match(
        &kernel(vec![one_branch]),
        &kernel(vec![term(1)])
    ));
}

#[test]
fn common_selector_can_be_factored_out_but_does_not_prove_nonzero_coefficients() {
    let common = variable(KernelVariable::InputKet(0));
    let x = variable(KernelVariable::InputBra(0));
    let mut zero = term(3);
    zero.ket_guard = vec![common.clone(), x.clone()];
    let mut one = term(3);
    one.ket_guard = vec![common.clone(), x.complement()];
    let mut whole = term(3);
    whole.ket_guard = vec![common.clone()];
    let difference = aggregate_difference(
        reduce_kernel(&kernel(vec![zero, one])).unwrap(),
        reduce_kernel(&kernel(vec![whole.clone()])).unwrap(),
    )
    .unwrap();
    // Only x needs a split, not the common guard's independent variable.
    assert!(zero_by_free_splitting(difference, &mut 1, 0));
    assert!(!zero_by_free_splitting(
        reduce_kernel(&kernel(vec![whole])).unwrap(),
        &mut 1,
        0
    ));
    let mut complement = term(3);
    complement.ket_guard = vec![common.complement()];
    let mut selected = term(3);
    selected.ket_guard = vec![common];
    assert!(!exact_aggregate_match(
        &kernel(vec![selected]),
        &kernel(vec![complement])
    ));
}

#[test]
fn common_free_phase_does_not_consume_free_split_depth() {
    let mut phased = term(1);
    for input in 0..20 {
        phased.phase.ket.add_boolean(
            &variable(KernelVariable::InputKet(input)),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 7)),
        );
    }
    let split = variable(KernelVariable::InputBra(0));
    let mut zero = phased.clone();
    zero.ket_guard.push(split.clone());
    let mut one = phased.clone();
    one.ket_guard.push(split.complement());
    one.weight.ket = rational(-1);
    phased.phase.ket.add_boolean(
        &split,
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
    );
    let difference = aggregate_difference(
        reduce_kernel(&kernel(vec![phased.clone()])).unwrap(),
        reduce_kernel(&kernel(vec![zero, one])).unwrap(),
    )
    .unwrap();
    assert!(zero_by_free_splitting(difference, &mut 1, 0));
    assert!(!exact_aggregate_match(
        &kernel(vec![phased]),
        &kernel(vec![term(1)])
    ));
}

#[test]
fn removing_common_phase_reconstructs_the_original_exact_sum() {
    let x = variable(KernelVariable::InputKet(0));
    let y = variable(KernelVariable::InputBra(0));
    for numerator in 1..7 {
        let mut left = term(3);
        left.ket_guard
            .push(variable(KernelVariable::ClassicalOutput(0)));
        left.phase.ket.add_boolean(
            &x.and(&y),
            crate::symbolic::PhaseCoefficient::rational(ratio(numerator, 7)),
        );
        let mut right = left.clone();
        right.ket_guard.clear();
        right.weight.ket = rational(5);
        right
            .phase
            .ket
            .add_boolean(&x, crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)));
        let source = reduce_kernel(&kernel(vec![left.clone(), right])).unwrap();
        let reduced = remove_common_phase(source.clone()).unwrap();
        left.ket_guard.clear();
        left.weight.ket = rational(1);
        let common = reduce_kernel(&kernel(vec![left])).unwrap();
        let mut budget = ReductionBudget {
            splits: 0,
            products: MAX_FACTOR_PRODUCTS,
            phase_cells: MAX_FACTOR_PHASE_CELLS,
        };
        assert_eq!(
            multiply_aggregates(common, reduced, &mut budget).unwrap(),
            source
        );
    }
}

#[test]
fn tensor_certificate_checks_smaller_pointwise_equalities() {
    let x = variable(KernelVariable::InputKet(0));
    let y = variable(KernelVariable::InputKet(1));
    let b = variable(KernelVariable::InputBra(0));
    let mut left = term(1);
    left.phase.ket.add_boolean(
        &x.and(&y),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
    );
    left.phase
        .ket
        .add_boolean(&b, crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)));
    let right = [
        KernelBooleanPolynomial::zero(),
        x.clone(),
        y.clone(),
        x.xor(&y),
    ]
    .into_iter()
    .enumerate()
    .map(|(index, parity)| {
        let mut leaf = term(1);
        leaf.weight.ket = KernelScalar::Rational(ratio(if index == 3 { -1 } else { 1 }, 2));
        leaf.phase.ket.add_boolean(
            &parity,
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
        leaf.phase
            .ket
            .add_boolean(&b, crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)));
        leaf
    })
    .collect();
    let left = reduce_kernel(&kernel(vec![left])).unwrap();
    let right = reduce_kernel(&kernel(right)).unwrap();
    assert_ne!(left, right);
    let mut free_budget = MAX_FREE_SPLITS;
    assert!(tensor_aggregate_match(&left, &right, &mut free_budget));
    assert!(!tensor_aggregate_match(&left, &right, &mut 0));
    let wrong = reduce_kernel(&kernel(vec![term(2)])).unwrap();
    free_budget = MAX_FREE_SPLITS;
    assert!(!tensor_aggregate_match(&left, &wrong, &mut free_budget));
}

#[test]
fn tensor_reconstruction_rejects_missing_cells_and_mixed_phases() {
    let mut ket = term(3);
    ket.phase.ket.add_boolean(
        &variable(KernelVariable::InputKet(0)),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    let mut bra = term(5);
    bra.phase.ket.add_boolean(
        &variable(KernelVariable::InputBra(0)),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 7)),
    );
    let mut budget = ReductionBudget {
        splits: 0,
        products: MAX_FACTOR_PRODUCTS,
        phase_cells: MAX_FACTOR_PHASE_CELLS,
    };
    let source = multiply_aggregates(
        reduce_kernel(&kernel(vec![term(1), ket])).unwrap(),
        reduce_kernel(&kernel(vec![term(2), bra])).unwrap(),
        &mut budget,
    )
    .unwrap();
    assert!(factor_free_tensor(&source, &mut budget).is_some());
    let mut missing = source.clone();
    missing.values_mut().next().unwrap().pop_first();
    assert!(factor_free_tensor(&missing, &mut budget).is_none());
    let mut wrong_sign = source;
    let value = wrong_sign
        .values_mut()
        .next()
        .unwrap()
        .values_mut()
        .next()
        .unwrap();
    *value = normalize_scalar(KernelScalar::Neg(Box::new(value.clone())));
    assert!(factor_free_tensor(&wrong_sign, &mut budget).is_none());
    let mut mixed = term(1);
    mixed.phase.ket.add_boolean(
        &variable(KernelVariable::InputKet(0)).and(&variable(KernelVariable::InputBra(0))),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    assert!(
        factor_free_tensor(&reduce_kernel(&kernel(vec![mixed])).unwrap(), &mut budget).is_none()
    );
}

#[test]
fn tensor_factors_preserve_shared_selector_parameters_and_exponential_pivots() {
    let parameter = variable(KernelVariable::QuantumOutputBra(1));
    let mut common = term(2);
    common.phase.ket.add_boolean(
        &parameter,
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 9)),
    );
    let mut ket = term(3);
    ket.phase.ket.add_boolean(
        &variable(KernelVariable::InputKet(0)).and(&parameter),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    let mut bra = term(5);
    bra.phase.ket.add_boolean(
        &variable(KernelVariable::InputBra(0)).and(&parameter),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 7)),
    );
    let mut budget = ReductionBudget {
        splits: 0,
        products: MAX_FACTOR_PRODUCTS,
        phase_cells: MAX_FACTOR_PHASE_CELLS,
    };
    let product = multiply_aggregates(
        reduce_kernel(&kernel(vec![term(1), ket])).unwrap(),
        reduce_kernel(&kernel(vec![term(1), bra])).unwrap(),
        &mut budget,
    )
    .unwrap();
    let product = multiply_aggregates(
        reduce_kernel(&kernel(vec![common])).unwrap(),
        product,
        &mut budget,
    )
    .unwrap();
    let mut guarded = ExactAggregate::new();
    guarded.insert(
        ExactEntry {
            constraints: vec![variable(KernelVariable::InputKet(2)).xor(&parameter)],
        },
        product.values().next().unwrap().clone(),
    );
    assert!(factor_free_tensor(&product, &mut budget).is_none());
    let [ket, bra] = factor_free_tensor(&guarded, &mut budget).unwrap();
    assert_eq!(multiply_aggregates(ket, bra, &mut budget).unwrap(), product);
    // Both values of the shared parameter are compared pointwise; neither
    // a renamed parameter nor the sum of its two values is a certificate.
    let wrong = restrict_aggregate(&guarded, &KernelVariable::QuantumOutputBra(1), false).unwrap();
    let mut free_budget = MAX_FREE_SPLITS;
    assert!(!tensor_aggregate_match(&guarded, &wrong, &mut free_budget));
}

#[test]
fn free_splitting_preserves_relative_phase_across_selectors() {
    let x = variable(KernelVariable::InputKet(0));
    let mut phase = term(1);
    phase
        .phase
        .ket
        .add_boolean(&x, crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)));
    let mut zero = term(1);
    zero.ket_guard = vec![x.clone()];
    let mut one = term(-1);
    one.ket_guard = vec![x.complement()];
    assert!(exact_aggregate_match(
        &kernel(vec![phase.clone()]),
        &kernel(vec![zero, one])
    ));
    assert!(!exact_aggregate_match(
        &kernel(vec![phase]),
        &kernel(vec![term(1)])
    ));
}

fn eighth_turn_residual(paths: usize) -> KernelTerm {
    let mut summed = term(1);
    for path in 0..paths {
        let v = KernelVariable::PathKet { term: 0, path };
        summed.ket_paths.insert(v.clone());
        summed.phase.ket.add_boolean(
            &variable(v),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    summed
}

#[test]
fn residual_split_unlocks_factors_before_exhausting_depth() {
    let mut source = eighth_turn_residual(10);
    let blocker = KernelVariable::PathKet { term: 0, path: 9 };
    let free = variable(KernelVariable::InputKet(0));
    source.ket_guard.push(variable(blocker.clone()).and(&free));
    let Reduction::Sum(residual) = reduce_term(&source) else {
        panic!("nonlinear selector keeps a genuine bound residual");
    };
    assert_ne!(residual.paths.first(), Some(&blocker));
    assert_eq!(residual.residual_split_variable(), Some(blocker));
    // The two literal blocker branches retain every independent factor,
    // with the original selector applying only to the one branch.
    let zero = eighth_turn_residual(9);
    let mut one = zero.clone();
    one.ket_guard.push(free);
    one.phase.ket.add_boolean(
        &KernelBooleanPolynomial::one(),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    assert!(reduce_kernel(&kernel(vec![source.clone()])).is_some());
    assert!(exact_aggregate_match(
        &kernel(vec![source]),
        &kernel(vec![zero, one])
    ));
}

#[test]
fn residual_split_preserves_weight_branches_and_bounds_order_search() {
    let mut source = eighth_turn_residual(10);
    let blocker = KernelVariable::PathKet { term: 0, path: 9 };
    source.weight.ket = KernelScalar::Select {
        condition: variable(blocker.clone()),
        when_true: Box::new(rational(3)),
        when_false: Box::new(rational(5)),
    };
    let Reduction::Sum(mut residual) = reduce_term(&source) else {
        panic!("path-dependent scalar prevents phase factorization");
    };
    assert_eq!(residual.residual_split_variable(), Some(blocker.clone()));
    let mut zero = eighth_turn_residual(9);
    zero.weight.ket = rational(5);
    let mut one = zero.clone();
    one.weight.ket = rational(3);
    one.phase.ket.add_boolean(
        &KernelBooleanPolynomial::one(),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    assert!(exact_aggregate_match(
        &kernel(vec![source]),
        &kernel(vec![zero, one])
    ));

    residual.constraints = vec![
        affine((0..MAX_RESIDUAL_ORDER_VISITS).map(KernelVariable::InputKet))
            .xor(&variable(blocker)),
    ];
    let before = residual.clone();
    assert_eq!(
        residual.residual_split_variable().as_ref(),
        residual.paths.first()
    );
    assert_eq!(residual.constraints, before.constraints);
    assert_eq!(residual.coefficient, before.coefficient);
    assert_eq!(residual.phase, before.phase);
    assert_eq!(residual.paths, before.paths);
}

fn weighted_eighth_turn_residual(paths: usize) -> KernelTerm {
    let mut summed = eighth_turn_residual(paths);
    for path in &summed.ket_paths {
        summed.weight.ket = multiply(
            summed.weight.ket,
            KernelScalar::Select {
                condition: variable(path.clone()),
                when_true: Box::new(rational(3)),
                when_false: Box::new(rational(5)),
            },
        );
    }
    summed
}

#[test]
fn separated_phase_sums_match_literal_enumeration_with_shared_free_coordinates() {
    let mut source = eighth_turn_residual(9);
    let input = variable(KernelVariable::InputKet(0));
    source.ket_guard.push(variable(KernelVariable::InputBra(0)));
    source.weight.ket = KernelScalar::Select {
        condition: input.clone(),
        when_true: Box::new(rational(3)),
        when_false: Box::new(rational(5)),
    };
    source.phase.ket.add_boolean(
        &input,
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 7)),
    );
    // The same free input is shared by all factors, not summed or renamed.
    for path in &source.ket_paths {
        source.phase.ket.add_boolean(
            &variable(path.clone()).and(&input),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    let expected = (0..512)
        .map(|bits| {
            let mut leaf = source.clone();
            for (index, path) in source.ket_paths.iter().enumerate() {
                leaf.phase.ket.substitute(
                    path,
                    &KernelBooleanPolynomial::from(bits & (1 << index) != 0),
                );
            }
            leaf.ket_paths.clear();
            leaf
        })
        .collect();
    assert!(reduce_kernel(&kernel(vec![source.clone()])).is_some());
    assert!(exact_aggregate_match(
        &kernel(vec![source]),
        &kernel(expected)
    ));
}

#[test]
fn phase_factorization_respects_mixed_monomials_guards_and_scalar_conditions() {
    let source = eighth_turn_residual(3);
    let Reduction::Sum(mut working) = reduce_term(&source) else {
        panic!("residual expected")
    };
    assert_eq!(factor_phase_sums(&working).unwrap().len(), 4);
    let paths = working.paths.iter().cloned().collect::<Vec<_>>();
    working.phase.add_boolean(
        &variable(paths[0].clone()).and(&variable(paths[1].clone())),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    let factors = factor_phase_sums(&working).unwrap();
    assert_eq!(factors.len(), 3);
    assert!(
        factors
            .iter()
            .any(|f| f.paths.contains(&paths[0]) && f.paths.contains(&paths[1]))
    );
    working.constraints.push(variable(paths[2].clone()));
    let factors = factor_phase_sums(&working).unwrap();
    assert_eq!(factors.len(), 3);
    assert!(factors.iter().any(
        |factor| factor.paths.contains(&paths[2]) && factor.constraints == working.constraints
    ));
    // A whole XOR row connects even separate monomials; it must not be
    // split into two indicators with a stronger zero set.
    working
        .constraints
        .push(variable(paths[0].clone()).xor(&variable(paths[2].clone())));
    assert!(factor_phase_sums(&working).is_none());
    working.constraints.clear();
    working.coefficient = KernelScalar::Select {
        condition: variable(paths[2].clone()),
        when_true: Box::new(rational(3)),
        when_false: Box::new(rational(5)),
    };
    assert!(factor_phase_sums(&working).is_none());
    working.coefficient = rational(1);
    working.phase.add_boolean(
        &variable(paths[1].clone()).and(&variable(paths[2].clone())),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    assert!(factor_phase_sums(&working).is_none());
}

#[test]
fn factorization_shares_split_and_product_budgets_and_refuses_partial_results() {
    for (splits, products) in [(2, MAX_FACTOR_PRODUCTS), (MAX_RESIDUAL_SPLITS, 2)] {
        let mut aggregate = reduce_kernel(&kernel(vec![term(7)])).unwrap();
        let mut atoms = 1;
        let mut budget = ReductionBudget {
            splits,
            products,
            phase_cells: MAX_FACTOR_PHASE_CELLS,
        };
        assert!(
            accumulate_reduction(
                reduce_term(&eighth_turn_residual(3)),
                &mut aggregate,
                &mut atoms,
                &mut budget,
                0
            )
            .is_none()
        );
    }
    let mut budget = ReductionBudget {
        splits: 0,
        products: 1,
        phase_cells: MAX_FACTOR_PHASE_CELLS,
    };
    let single = reduce_kernel(&kernel(vec![term(3)])).unwrap();
    assert!(multiply_aggregates(single.clone(), single.clone(), &mut budget).is_some());
    assert_eq!(budget.products, 0);
    assert!(multiply_aggregates(single.clone(), single, &mut budget).is_none());
}

#[test]
fn factor_phase_copy_budget_refuses_before_convolution() {
    let mut phased = term(1);
    phased.phase.ket.add_boolean(
        &variable(KernelVariable::InputKet(0)),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    let source = reduce_kernel(&kernel(vec![phased])).unwrap();
    let mut budget = ReductionBudget {
        splits: 0,
        products: 10,
        phase_cells: 3,
    };
    // Each of the two operands contributes one phase term and one variable.
    assert!(multiply_aggregates(source.clone(), source.clone(), &mut budget).is_none());
    budget.phase_cells = 4;
    assert!(multiply_aggregates(source.clone(), source.clone(), &mut budget).is_some());
    assert_eq!(budget.phase_cells, 0);
    assert!(multiply_aggregates(source.clone(), source, &mut budget).is_none());
}

#[test]
fn residual_depth_refusal_does_not_return_a_partial_aggregate() {
    let too_large = kernel(vec![
        term(7),
        weighted_eighth_turn_residual(MAX_SPLIT_DEPTH + 1),
    ]);
    assert!(reduce_kernel(&too_large).is_none());
    assert!(!exact_aggregate_match(&too_large, &kernel(vec![term(7)])));
}

#[test]
fn residual_split_budget_is_shared_across_component_terms() {
    assert!(reduce_kernel(&kernel(vec![weighted_eighth_turn_residual(8)])).is_some());
    assert!(
        reduce_kernel(&kernel(vec![
            weighted_eighth_turn_residual(8),
            eighth_turn_residual(1)
        ]))
        .is_none()
    );
}

#[test]
fn phase_lift_budget_uses_modular_denominator_degree() {
    let half = crate::symbolic::PhaseCoefficient::rational(ratio(1, 2));
    let quarter = crate::symbolic::PhaseCoefficient::rational(ratio(1, 4));
    let eighth = crate::symbolic::PhaseCoefficient::rational(ratio(1, 8));

    assert_eq!(lifted_boolean_term_bound(1_000, &half), Some(1_000));
    assert_eq!(lifted_boolean_term_bound(446, &quarter), Some(99_681));
    assert_eq!(lifted_boolean_term_bound(447, &quarter), None);
    assert_eq!(lifted_boolean_term_bound(50, &eighth), Some(20_875));
    assert_eq!(lifted_boolean_term_bound(100, &eighth), None);
}

#[test]
fn constraint_span_recovers_a_small_pivot_before_refusing_large_expansion() {
    let path = KernelVariable::PathKet { term: 0, path: 0 };
    let output = variable(KernelVariable::QuantumOutputKet(0));
    let expression = (0..100).fold(KernelBooleanPolynomial::zero(), |sum, index| {
        sum.xor(
            &variable(KernelVariable::InputKet(index))
                .and(&variable(KernelVariable::InputKet(index + 100))),
        )
    });
    let mut left = term(1);
    left.ket_paths.insert(path.clone());
    left.ket_guard = vec![
        variable(path.clone()).xor(&expression),
        output.xor(&expression),
    ];
    left.phase.ket.add_boolean(
        &variable(path),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    assert!(
        lifted_boolean_term_bound(
            expression.term_count(),
            &crate::symbolic::PhaseCoefficient::rational(ratio(1, 8))
        )
        .is_none()
    );
    let mut right = term(1);
    right.ket_guard = vec![output.xor(&expression)];
    right.phase.ket.add_boolean(
        &output,
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    assert!(exact_aggregate_match(
        &kernel(vec![left]),
        &kernel(vec![right])
    ));
}

#[test]
fn stalled_nonlinear_rows_expose_unique_paths_without_shannon_enumeration() {
    let mut left = term(1);
    let mut right = term(1);
    for index in 0..9 {
        let path = KernelVariable::PathKet {
            term: 0,
            path: index,
        };
        let a = variable(KernelVariable::InputKet(3 * index));
        let b = variable(KernelVariable::InputKet(3 * index + 1));
        let c = variable(KernelVariable::InputKet(3 * index + 2));
        let equation = a.and(&variable(path.clone())).xor(&b);
        left.ket_guard.push(equation.clone());
        left.ket_guard
            .push(equation.xor(&variable(path.clone())).xor(&c));
        left.phase.ket.add_boolean(
            &variable(path.clone()),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        left.ket_paths.insert(path);
        right.ket_guard.push(a.and(&c).xor(&b));
        right
            .phase
            .ket
            .add_boolean(&c, crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)));
    }
    // Each original row contains its path only nonlinearly or also in
    // a nonlinear monomial. Row addition exposes v=c for all nine paths.
    assert!(matches!(reduce_term(&left), Reduction::Exact(_)));
    assert!(exact_aggregate_match(
        &kernel(vec![left]),
        &kernel(vec![right])
    ));
}

#[test]
fn bounded_phase_recovery_preserves_selectors_multiplicity_and_weight_dependence() {
    let value = KernelVariable::PathKet { term: 0, path: 0 };
    let fourier = KernelVariable::PathBra { term: 0, path: 0 };
    let definition = (0..100).fold(KernelBooleanPolynomial::zero(), |sum, index| {
        sum.xor(
            &variable(KernelVariable::InputKet(2 * index))
                .and(&variable(KernelVariable::InputKet(2 * index + 1))),
        )
    });
    let mut left = term(1);
    left.ket_paths.insert(value.clone());
    left.bra_paths.insert(fourier.clone());
    left.ket_guard
        .push(variable(value.clone()).xor(&definition));
    left.phase.ket.add_boolean(
        &variable(value.clone()),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    left.phase.ket.add_boolean(
        &variable(value).and(&variable(fourier.clone())),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
    );
    let mut right = term(2);
    right.ket_guard.push(definition);
    // sum_w (-1)^(wv) imposes v=0 before v's large definition needs
    // arithmetic lifting. The remaining exact selector is F=0. This is
    // now a bounded recovery case; unrestricted phase-first recovery
    // remains disabled after its earlier real-case runtime regression.
    assert!(exact_aggregate_match(
        &kernel(vec![left.clone()]),
        &kernel(vec![right.clone()])
    ));
    let mut with_absent = left.clone();
    with_absent
        .ket_paths
        .extend((1..=3).map(|path| KernelVariable::PathKet { term: 0, path }));
    right.weight.ket = rational(16);
    assert!(exact_aggregate_match(
        &kernel(vec![with_absent]),
        &kernel(vec![right])
    ));
    let mut too_many_paths = left.clone();
    too_many_paths.ket_paths.extend(
        (1..=MAX_DEFERRED_PHASE_PATHS).map(|path| KernelVariable::PathKet { term: 0, path }),
    );
    assert!(matches!(reduce_term(&too_many_paths), Reduction::Residual));
    let mut exhausted_probes = left.clone();
    exhausted_probes.ket_paths.extend(
        (1..=MAX_DEFERRED_PHASE_PROBES).map(|path| KernelVariable::PathKet { term: 0, path }),
    );
    assert!(matches!(
        reduce_term(&exhausted_probes),
        Reduction::Residual
    ));
    let mut too_many_terms = left.clone();
    for index in 0..MAX_DEFERRED_PHASE_TERMS {
        too_many_terms.phase.ket.add_boolean(
            &variable(KernelVariable::InputKet(1000 + index)),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    assert!(matches!(reduce_term(&too_many_terms), Reduction::Residual));
    // A weight depending on w prevents that Fourier rule. It must not be
    // dropped simply because the direct v substitution does not fit.
    left.weight.bra = KernelScalar::Select {
        condition: variable(fourier),
        when_true: Box::new(rational(3)),
        when_false: Box::new(rational(5)),
    };
    assert!(matches!(reduce_term(&left), Reduction::Residual));
}

#[test]
fn a_refused_early_span_probe_does_not_block_late_small_exact_recovery() {
    let mut left = term(1);
    for index in 0..400 {
        let path = KernelVariable::PathKet {
            term: 0,
            path: index,
        };
        let definition = (0..65).fold(KernelBooleanPolynomial::zero(), |sum, offset| {
            let input = 2 * (65 * index + offset);
            sum.xor(
                &variable(KernelVariable::InputKet(input))
                    .and(&variable(KernelVariable::InputKet(input + 1))),
            )
        });
        left.ket_guard.push(variable(path.clone()).xor(&definition));
        left.ket_paths.insert(path);
    }
    let path = KernelVariable::PathKet { term: 0, path: 400 };
    let output = variable(KernelVariable::QuantumOutputKet(0));
    let definition = (0..100).fold(KernelBooleanPolynomial::zero(), |sum, offset| {
        sum.xor(
            &variable(KernelVariable::InputBra(2 * offset))
                .and(&variable(KernelVariable::InputBra(2 * offset + 1))),
        )
    });
    left.ket_guard.extend([
        variable(path.clone()).xor(&definition),
        output.xor(&definition),
    ]);
    left.ket_paths.insert(path.clone());
    left.phase.ket.add_boolean(
        &variable(path),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    assert!(matches!(
        normalize_constraint_span(&mut left.ket_guard.clone()),
        ConstraintNormalization::BudgetExceeded
    ));
    let mut right = term(1);
    right.ket_guard.push(output.xor(&definition));
    right.phase.ket.add_boolean(
        &output,
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    // The 400 cheap unique definitions disappear without a matrix. Only
    // then does the small remaining span expose the safe literal pivot.
    assert!(exact_aggregate_match(
        &kernel(vec![left]),
        &kernel(vec![right])
    ));
}

#[test]
fn initial_alias_compaction_must_reenter_original_representation_budget() {
    let bound = KernelVariable::PathKet { term: 0, path: 0 };
    let free = KernelVariable::InputKet(0);
    let guard = variable(KernelVariable::InputBra(0));
    let mut source = WorkingTerm {
        paths: BTreeSet::from([bound.clone()]),
        constraints: vec![
            variable(bound.clone()).xor(&variable(free.clone())),
            guard.clone(),
        ],
        coefficient: rational(3),
        phase: KernelPhasePolynomial::default(),
    };
    for index in 1..=50_001 {
        let x = variable(KernelVariable::InputKet(index));
        source.phase.add_boolean(
            &variable(bound.clone()).and(&x),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        source.phase.add_boolean(
            &variable(free.clone()).and(&x),
            crate::symbolic::PhaseCoefficient::rational(ratio(7, 8)),
        );
    }
    assert_eq!(source.phase.term_count(), 100_002);
    assert!(!source.within_budget());
    assert!(source.initial_alias_compaction_within_budget());
    let Reduction::Exact(result) = reduce_working_term(source.clone()) else {
        panic!("unique bound alias must compact before the original cap");
    };
    assert_eq!(result.phase.term_count(), 0);
    assert_eq!(result.coefficient, rational(3));
    assert_eq!(result.constraints, vec![guard]);

    // Merely equal free-looking coordinates cannot be identified or
    // canceled: the oversized phase must still refuse after the probe.
    source.paths.clear();
    assert!(matches!(
        reduce_working_term(source.clone()),
        Reduction::Residual
    ));
    // A high-degree encoding can exceed the independent syntax entrance
    // even when it is below the compaction-only 200000-term admission.
    let mut high = KernelBooleanPolynomial::one();
    for index in 50_002..50_010 {
        high = high.and(&variable(KernelVariable::InputKet(index)));
    }
    source.phase = KernelPhasePolynomial::default();
    for index in 1..=100_001 {
        source.phase.add_boolean(
            &high.and(&variable(KernelVariable::InputBra(index))),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    assert!(!source.initial_alias_compaction_within_budget());
    assert!(matches!(reduce_working_term(source), Reduction::Residual));
}

#[test]
fn literal_alias_batch_preserves_every_free_kernel_entry_and_weight() {
    fn entries(
        source: &WorkingTerm,
        free: &[(KernelVariable, bool)],
    ) -> BTreeMap<KernelPhasePolynomial, BigRational> {
        let paths = source.paths.iter().cloned().collect::<Vec<_>>();
        let mut result = BTreeMap::new();
        for bits in 0..(1usize << paths.len()) {
            let mut instance = source.clone();
            for (variable, value) in free.iter().cloned().chain(
                paths
                    .iter()
                    .enumerate()
                    .map(|(index, path)| (path.clone(), bits & (1 << index) != 0)),
            ) {
                instance.substitute(&variable, &KernelBooleanPolynomial::from(value));
            }
            if instance.constraints.iter().any(|value| !value.is_zero()) {
                assert!(
                    instance
                        .constraints
                        .iter()
                        .all(|v| v.is_zero() || v.is_one())
                );
                continue;
            }
            let KernelScalar::Rational(weight) = normalize_scalar(instance.coefficient) else {
                panic!("the fully assigned test weight must be rational")
            };
            *result.entry(instance.phase).or_insert_with(|| integer(0)) += weight;
        }
        result.retain(|_, value| value != &integer(0));
        result
    }

    let ket = KernelVariable::PathKet { term: 0, path: 0 };
    let bra = KernelVariable::PathBra { term: 0, path: 0 };
    let other = KernelVariable::PathKet { term: 1, path: 0 };
    let free = [
        KernelVariable::InputKet(0),
        KernelVariable::InputBra(0),
        KernelVariable::QuantumOutputKet(0),
        KernelVariable::QuantumOutputBra(0),
        KernelVariable::ClassicalOutput(0),
    ];
    let product = variable(ket.clone()).and(&variable(other.clone()));
    let condition = variable(other.clone()).and(&variable(free[4].clone()));
    let mut phase = KernelPhasePolynomial::default();
    for (value, coefficient) in [
        (product.clone(), ratio(1, 8)),
        (variable(bra.clone()), ratio(1, 8)),
        (variable(free[0].clone()), ratio(-1, 4)),
    ] {
        phase.add_boolean(
            &value,
            crate::symbolic::PhaseCoefficient::rational(coefficient),
        );
    }
    let source = WorkingTerm {
        paths: BTreeSet::from([ket.clone(), bra.clone(), other.clone()]),
        constraints: vec![
            affine([ket.clone(), bra.clone()]),
            affine([bra.clone(), other.clone()]),
            affine([other.clone(), free[0].clone()]),
            affine([ket.clone(), free[1].clone()]),
            variable(free[2].clone()).xor(&condition),
            affine([free[3].clone(), free[1].clone()]),
            product.xor(&variable(bra.clone())),
        ],
        coefficient: KernelScalar::Select {
            condition: affine([ket, bra]),
            when_true: Box::new(rational(13)),
            when_false: Box::new(KernelScalar::Select {
                condition,
                when_true: Box::new(rational(3)),
                when_false: Box::new(rational(5)),
            }),
        },
        phase,
    };
    let mut renamed = source.clone();
    renamed.eliminate_literal_aliases();
    assert!(renamed.paths.is_empty());
    assert_eq!(renamed.phase.term_count(), 0);
    assert!(
        renamed
            .constraints
            .contains(&affine([free[0].clone(), free[1].clone()]))
    );
    for bits in 0..(1usize << free.len()) {
        let assignment = free
            .iter()
            .enumerate()
            .map(|(index, variable)| (variable.clone(), bits & (1 << index) != 0))
            .collect::<Vec<_>>();
        assert_eq!(
            entries(&source, &assignment),
            entries(&renamed, &assignment)
        );
    }
}

#[test]
fn literal_alias_cycles_keep_one_binder_and_do_not_hide_contradictions() {
    let paths = [
        KernelVariable::PathKet { term: 0, path: 0 },
        KernelVariable::PathBra { term: 0, path: 0 },
        KernelVariable::PathKet { term: 1, path: 0 },
    ];
    let mut source = term(1);
    source
        .ket_paths
        .extend([paths[0].clone(), paths[2].clone()]);
    source.bra_paths.insert(paths[1].clone());
    source.ket_guard = vec![
        affine([paths[0].clone(), paths[1].clone()]),
        affine([paths[1].clone(), paths[2].clone()]),
        affine([paths[2].clone(), paths[0].clone()]),
    ];
    assert!(exact_aggregate_match(
        &kernel(vec![source.clone()]),
        &kernel(vec![term(2)])
    ));
    assert!(!exact_aggregate_match(
        &kernel(vec![source.clone()]),
        &kernel(vec![term(1)])
    ));
    source
        .ket_guard
        .push(affine([paths[0].clone(), paths[2].clone()]).complement());
    assert!(matches!(reduce_term(&source), Reduction::Zero));

    let mut unbound = WorkingTerm {
        paths: BTreeSet::new(),
        constraints: vec![affine([paths[0].clone(), paths[1].clone()])],
        coefficient: rational(1),
        phase: KernelPhasePolynomial::default(),
    };
    let original = unbound.constraints.clone();
    unbound.eliminate_literal_aliases();
    assert_eq!(unbound.constraints, original);
}

#[test]
fn sparse_unique_pivots_do_not_require_an_initial_dense_matrix() {
    let mut left = term(1);
    for index in 0..2240 {
        let path = KernelVariable::PathKet {
            term: 0,
            path: index,
        };
        left.ket_paths.insert(path.clone());
        left.ket_guard
            .push(variable(path).xor(&variable(KernelVariable::InputKet(index))));
    }
    assert!(left.ket_guard.len() * left.ket_paths.len() * 2 > MAX_AFFINE_MATRIX_CELLS);
    let mut working = WorkingTerm {
        constraints: left.ket_guard.clone(),
        paths: left.ket_paths.clone(),
        coefficient: rational(1),
        phase: KernelPhasePolynomial::default(),
    };
    let before = working.constraints.clone();
    assert!(matches!(
        working.normalize_constraints(),
        ConstraintNormalization::BudgetExceeded
    ));
    assert_eq!(working.constraints, before);
    // The failed optional normalization left the original complete
    // equations available, each with exactly one bound solution.
    assert!(exact_aggregate_match(
        &kernel(vec![left]),
        &kernel(vec![term(1)])
    ));
}

#[test]
fn alternative_pivot_probes_are_bounded_read_only_and_preflighted() {
    let p = KernelVariable::PathKet { term: 0, path: 0 };
    let q = KernelVariable::PathKet { term: 0, path: 1 };
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(
        &variable(p.clone()),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 1 << 20)),
    );
    let working = WorkingTerm {
        paths: BTreeSet::from([p.clone(), q.clone()]),
        constraints: vec![
            variable(p.clone()).xor(&affine((0..17).map(KernelVariable::InputKet))),
            variable(q.clone()).xor(&affine((17..35).map(KernelVariable::InputKet))),
        ],
        coefficient: rational(1),
        phase,
    };
    let before = working.clone();
    let first = working.best_constraint_pivot().unwrap();
    assert_eq!(first.0, p);
    assert!(!working.substitution_within_budget(&first.0, &first.1));
    let mut probes = 1;
    assert!(working.budget_safe_constraint_pivot(&mut probes).is_none());
    assert_eq!(probes, 0);
    let mut probes = 2;
    let alternative = working.budget_safe_constraint_pivot(&mut probes).unwrap();
    assert_eq!(alternative.0, q);
    assert_eq!(
        alternative.1,
        affine((17..35).map(KernelVariable::InputKet))
    );
    assert_eq!(probes, 0);
    assert!(working.budget_safe_constraint_pivot(&mut probes).is_none());
    assert_eq!(working.constraints, before.constraints);
    assert_eq!(working.paths, before.paths);
    assert_eq!(working.phase, before.phase);
    assert_eq!(working.coefficient, before.coefficient);
}

#[test]
fn oversized_pivot_does_not_hide_a_later_zero_fourier_sum() {
    let p = KernelVariable::PathKet { term: 0, path: 0 };
    let q = KernelVariable::PathKet { term: 0, path: 1 };
    let mut source = term(1);
    source.ket_paths = BTreeSet::from([p.clone(), q.clone()]);
    source.ket_guard =
        vec![variable(p.clone()).xor(&affine((0..17).map(KernelVariable::InputKet)))];
    source.phase.ket.add_boolean(
        &variable(p),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 1 << 20)),
    );
    source.phase.ket.add_boolean(
        &variable(q.clone()),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
    );
    // For every free input, the independent q sum is 1 + (-1) = 0.
    assert!(matches!(reduce_term(&source), Reduction::Zero));
    source
        .phase
        .ket
        .substitute(&q, &KernelBooleanPolynomial::zero());
    // An unused q contributes 2, not 0; the unsafe p remains a refusal.
    assert!(matches!(reduce_term(&source), Reduction::Residual));
}

#[test]
fn oversized_omega_does_not_hide_a_later_zero_fourier_sum() {
    let p = KernelVariable::PathKet { term: 0, path: 0 };
    let q = KernelVariable::PathKet { term: 0, path: 1 };
    let mut source = term(1);
    source.ket_paths = BTreeSet::from([p.clone(), q.clone()]);
    source.phase.ket.add_boolean(
        &variable(p.clone()),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 4)),
    );
    for input in 0..447 {
        source.phase.ket.add_boolean(
            &variable(p.clone()).and(&variable(KernelVariable::InputKet(input))),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
    }
    source.phase.ket.add_boolean(
        &variable(q.clone()),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
    );
    assert!(matches!(reduce_term(&source), Reduction::Zero));
    source
        .phase
        .ket
        .substitute(&q, &KernelBooleanPolynomial::zero());
    assert!(matches!(reduce_term(&source), Reduction::Residual));
}

#[test]
fn omega_rule_rejects_large_parity_before_lifting() {
    let mut residual = term(1);
    let path = KernelVariable::PathKet { term: 0, path: 0 };
    let path_polynomial = KernelBooleanPolynomial::variable(path.clone());
    residual.ket_paths.insert(path);
    residual.phase.ket.add_boolean(
        &path_polynomial,
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 4)),
    );
    for input in 0..447 {
        let product = path_polynomial.and(&KernelBooleanPolynomial::variable(
            KernelVariable::InputKet(input),
        ));
        residual.phase.ket.add_boolean(
            &product,
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
    }

    assert!(matches!(reduce_term(&residual), Reduction::Residual));
}

#[test]
fn affine_rref_refuses_a_matrix_beyond_its_work_budget() {
    let width = 3_163usize;
    assert!(width * width > MAX_AFFINE_MATRIX_CELLS);
    let mut residual = term(1);
    residual.ket_guard = (0..width)
        .map(|input| variable(KernelVariable::InputKet(input)))
        .collect();

    assert!(matches!(reduce_term(&residual), Reduction::Residual));
}
