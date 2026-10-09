use super::super::kernel::DensityKernel;
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

fn sqrt_ratio(numerator: i64, denominator: i64) -> KernelScalar {
    KernelScalar::Sqrt(Box::new(KernelScalar::Rational(ratio(
        numerator,
        denominator,
    ))))
}

fn variable(variable: KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(variable)
}

#[test]
fn free_indices_are_never_accepted_as_bound_paths() {
    let mut malformed = term(1);
    malformed
        .ket_paths
        .insert(KernelVariable::QuantumOutputKet(0));

    assert!(local_forms_match(
        &kernel(vec![malformed.clone()]),
        &kernel(vec![term(1)])
    ));
    assert!(!local_forms_match(
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
    assert!(!local_forms_match(&left, &right));
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
    assert!(!local_forms_match(&left, &right));

    let Reduction::Exact(exact) = reduce_term(&left.terms[0]) else {
        panic!("expected exact local result");
    };
    let variables = exact
        .constraints
        .iter()
        .flat_map(KernelBooleanPolynomial::variables)
        .collect::<BTreeSet<_>>();
    assert!(variables.contains(&KernelVariable::ClassicalOutput(0)));
    assert!(!variables.contains(&KernelVariable::QuantumOutputKet(0)));
    assert!(!variables.contains(&KernelVariable::QuantumOutputBra(0)));
}

#[test]
fn triangular_selector_preserves_nonlinear_definitions_pointwise() {
    let variables = [
        KernelVariable::InputKet(0),
        KernelVariable::InputBra(0),
        KernelVariable::QuantumOutputKet(0),
    ];
    let x = variable(variables[0].clone());
    let y = variable(variables[1].clone());
    let z = variable(variables[2].clone());
    let monomials = (0..8)
        .map(|bits| {
            variables
                .iter()
                .enumerate()
                .fold(KernelBooleanPolynomial::one(), |product, (i, v)| {
                    if bits & (1 << i) == 0 {
                        product
                    } else {
                        product.and(&variable(v.clone()))
                    }
                })
        })
        .collect::<Vec<_>>();
    let holds = |rows: &[KernelBooleanPolynomial], assignment: usize| {
        rows.iter().all(|row| {
            variables
                .iter()
                .enumerate()
                .fold(row.clone(), |row, (i, v)| {
                    row.substitute(
                        v,
                        &KernelBooleanPolynomial::from(assignment & (1 << i) != 0),
                    )
                })
                .is_zero()
        })
    };
    for bits in 0..256 {
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
        for complement in [false, true] {
            let constraints = vec![
                x.xor(&y.and(&z))
                    .xor(&KernelBooleanPolynomial::from(complement)),
                extra.clone(),
            ];
            let mut working = WorkingTerm {
                constraints: constraints.clone(),
                paths: BTreeSet::new(),
                coefficient: rational(1),
                phase: KernelPhasePolynomial::default(),
            };
            let status = working.normalize_selector();
            assert!(!matches!(status, ConstraintNormalization::BudgetExceeded));
            for assignment in 0..8 {
                assert_eq!(
                    holds(&constraints, assignment),
                    !matches!(status, ConstraintNormalization::Contradiction)
                        && holds(&working.constraints, assignment),
                    "bits={bits} complement={complement} assignment={assignment}"
                );
            }
        }
    }
}

#[test]
fn triangular_selector_substitutes_phase_and_weight_without_dropping_guard() {
    let x = variable(KernelVariable::InputKet(0));
    let yz =
        variable(KernelVariable::InputBra(0)).and(&variable(KernelVariable::QuantumOutputKet(0)));
    let make = |value: &KernelBooleanPolynomial, guarded: bool| {
        let mut source = term(1);
        if guarded {
            source.ket_guard = vec![x.xor(&yz)];
        }
        source.weight.ket = KernelScalar::Select {
            condition: value.clone(),
            when_true: Box::new(rational(3)),
            when_false: Box::new(rational(5)),
        };
        source.phase.ket.add_boolean(
            value,
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        kernel(vec![source])
    };
    assert!(local_forms_match(&make(&x, true), &make(&yz, true)));
    assert!(!local_forms_match(&make(&x, true), &make(&yz, false)));
}

#[test]
fn self_dependent_nonlinear_selector_is_not_used_as_a_definition() {
    let x = variable(KernelVariable::InputKet(0));
    let y = variable(KernelVariable::InputBra(0));
    let equation = x.xor(&x.and(&y));
    let mut working = WorkingTerm {
        constraints: vec![equation.clone()],
        paths: BTreeSet::new(),
        coefficient: rational(1),
        phase: KernelPhasePolynomial::default(),
    };
    assert!(matches!(
        working.normalize_selector(),
        ConstraintNormalization::Normalized
    ));
    assert_eq!(working.constraints, vec![equation]);
}

#[test]
fn path_elimination_counts_exact_solutions_without_repeated_rref() {
    let x = KernelVariable::InputKet(0);
    let p = KernelVariable::PathKet { term: 0, path: 0 };
    let q = KernelVariable::PathBra { term: 0, path: 0 };
    let variables = [x.clone(), p.clone(), q.clone()];
    let monomials = (0..8)
        .map(|bits| {
            variables
                .iter()
                .enumerate()
                .fold(KernelBooleanPolynomial::one(), |product, (i, v)| {
                    if bits & (1 << i) == 0 {
                        product
                    } else {
                        product.and(&variable(v.clone()))
                    }
                })
        })
        .collect::<Vec<_>>();
    let eval = |row: &KernelBooleanPolynomial, values: usize| {
        variables
            .iter()
            .enumerate()
            .fold(row.clone(), |row, (i, v)| {
                row.substitute(v, &KernelBooleanPolynomial::from(values & (1 << i) != 0))
            })
            .is_zero()
    };
    let mut certified = 0;
    for bits in 0..256 {
        let f =
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
        for g in [&p, &q] {
            let mut source = term(1);
            source.ket_paths.insert(p.clone());
            source.bra_paths.insert(q.clone());
            source.ket_guard = vec![f.clone(), variable(g.clone()).xor(&variable(x.clone()))];
            let reduction = reduce_term(&source);
            if matches!(reduction, Reduction::Residual | Reduction::Sum(_)) {
                continue;
            }
            certified += 1;
            for input in 0..2 {
                let count = (0..4)
                    .filter(|paths| {
                        source
                            .ket_guard
                            .iter()
                            .all(|row| eval(row, (paths << 1) | input))
                    })
                    .count();
                let actual = match &reduction {
                    Reduction::Zero => rational(0),
                    Reduction::Exact(term) => {
                        assert_eq!(term.phase, KernelPhasePolynomial::default());
                        if term.constraints.iter().all(|row| eval(row, input)) {
                            normalize_scalar(
                                term.coefficient
                                    .substitute(&x, &KernelBooleanPolynomial::from(input != 0)),
                            )
                        } else {
                            rational(0)
                        }
                    }
                    Reduction::Residual | Reduction::Sum(_) => unreachable!(),
                };
                assert_eq!(actual, rational(count as i64), "bits={bits} input={input}");
            }
        }
    }
    assert!(certified > 100);
}

#[test]
fn nonlinear_contradiction_annihilates_the_whole_term() {
    let xy = variable(KernelVariable::InputKet(0)).and(&variable(KernelVariable::InputBra(0)));
    let mut impossible = term(7);
    impossible.ket_guard = vec![xy.clone(), xy.complement()];
    assert!(local_forms_match(
        &kernel(vec![impossible]),
        &kernel(Vec::new())
    ));
}

#[test]
fn bound_phase_cancels_under_retained_free_selector() {
    let path = KernelVariable::PathKet { term: 0, path: 0 };
    let x = variable(KernelVariable::InputKet(0));
    let y = variable(KernelVariable::InputBra(0));
    let mut source = term(1);
    source.ket_paths.insert(path.clone());
    source.ket_guard.push(x.xor(&y));
    source.phase.ket.add_boolean(
        &variable(path.clone()).and(&x),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    source.phase.ket.add_boolean(
        &variable(path).and(&y),
        crate::symbolic::PhaseCoefficient::rational(ratio(-1, 8)),
    );
    let mut expected = term(2);
    expected.ket_guard.push(x.xor(&y));
    // Local reduction itself succeeds, without Shannon enumeration.
    assert!(matches!(reduce_term(&source), Reduction::Exact(_)));
    assert!(local_forms_match(
        &kernel(vec![source.clone()]),
        &kernel(vec![expected.clone()])
    ));
    // Retaining the selector is essential. Outside x=y the path sum is
    // 1+exp(±i*pi/4), not 2; it must not become the guarded channel.
    source.ket_guard.clear();
    assert!(!local_forms_match(
        &kernel(vec![source]),
        &kernel(vec![expected])
    ));
}

#[test]
fn vacuous_path_sum_contributes_exact_factor_two() {
    let mut summed = term(1);
    summed
        .ket_paths
        .insert(KernelVariable::PathKet { term: 0, path: 0 });

    assert!(local_forms_match(
        &kernel(vec![summed]),
        &kernel(vec![term(2)])
    ));
}

#[test]
fn fourier_path_sum_emits_an_affine_delta() {
    let path = KernelVariable::PathKet { term: 0, path: 0 };
    let input = variable(KernelVariable::InputKet(0));
    let mut summed = term(1);
    summed.ket_paths.insert(path.clone());
    summed.phase.ket.add_boolean(
        &variable(path).and(&input),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
    );
    let mut expected = term(2);
    expected.ket_guard = vec![input];

    assert!(local_forms_match(
        &kernel(vec![summed]),
        &kernel(vec![expected])
    ));
}

#[test]
fn contradictory_fourier_delta_annihilates_the_term() {
    let path = KernelVariable::PathKet { term: 0, path: 0 };
    let mut summed = term(1);
    summed.ket_paths.insert(path.clone());
    summed.phase.ket.add_boolean(
        &variable(path),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
    );

    assert!(matches!(reduce_term(&summed), Reduction::Zero));
    assert!(local_forms_match(
        &kernel(vec![summed]),
        &kernel(Vec::new())
    ));
}

#[test]
fn omega_path_sum_rewrites_coefficient_and_phase_exactly() {
    let path = KernelVariable::PathKet { term: 0, path: 0 };
    let parity = variable(KernelVariable::InputKet(0));
    let path_polynomial = variable(path.clone());
    let mut summed = term(1);
    summed.ket_paths.insert(path);
    summed.phase.ket.add_boolean(
        &path_polynomial,
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 4)),
    );
    summed.phase.ket.add_boolean(
        &path_polynomial.and(&parity),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
    );

    let mut expected = term(1);
    expected.weight.ket = sqrt_ratio(2, 1);
    expected.phase.ket.add_boolean(
        &KernelBooleanPolynomial::one(),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    expected.phase.ket.add_boolean(
        &parity,
        crate::symbolic::PhaseCoefficient::rational(ratio(-1, 4)),
    );

    assert!(local_forms_match(
        &kernel(vec![summed]),
        &kernel(vec![expected])
    ));
}

// Test-only comparison against expected local normal forms. No kernel
// aggregation, SMT, or program-level EQ/NEQ inference is exercised here.
fn local_forms_match(a: &DensityKernel, b: &DensityKernel) -> bool {
    let reduce = |k: &DensityKernel| match k.terms.as_slice() {
        [] => Reduction::Zero,
        [t] => reduce_term(t),
        _ => panic!("local fixture must have at most one term"),
    };
    match (reduce(a), reduce(b)) {
        (Reduction::Zero, Reduction::Zero) => true,
        (Reduction::Exact(a), Reduction::Exact(b)) => a == b,
        _ => false,
    }
}

#[test]
fn unresolved_sum_and_resource_refusal_are_distinct_from_zero() {
    let mut source = term(1);
    let v = KernelVariable::PathKet { term: 0, path: 0 };
    source.ket_paths.insert(v.clone());
    source.phase.ket.add_boolean(
        &variable(v.clone()),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 3)),
    );
    let Reduction::Sum(remaining) = reduce_term(&source) else {
        panic!("expected retained sum");
    };
    assert!(remaining.paths.contains(&v));
    assert_eq!(remaining.phase, working_term(&source).phase);

    let mut oversized = working_term(&source);
    oversized.constraints = vec![KernelBooleanPolynomial::zero(); MAX_CONSTRAINTS + 1];
    let mut checkpoint = None;
    assert!(matches!(
        reduce_working_term_with_checkpoint(oversized, Some(&mut checkpoint)),
        Reduction::Residual
    ));
    assert!(checkpoint.is_none());
}

#[test]
fn parsed_hadamard_kernel_reduces_without_summing_free_coordinates() {
    use crate::equivalence::{EquivalenceConfig, kernel_for, prepare_comparison};
    let program = crate::frontend::openqasm3::parse_str(
        "OPENQASM 3.0; include \"stdgates.inc\"; qubit q; h q;",
        "local-reducer.qasm",
    )
    .unwrap();
    let config = EquivalenceConfig::positional(&program, &program).unwrap();
    let prepared = prepare_comparison(&program, &program, &config).unwrap();
    let kernel = kernel_for(&prepared.left).unwrap();
    assert_eq!(kernel.terms.len(), 1);
    let Reduction::Exact(exact) = reduce_term(&kernel.terms[0]) else {
        panic!("H kernel should reduce");
    };
    assert_eq!(exact.coefficient, KernelScalar::Rational(ratio(1, 2)));
    assert!(exact.phase.variables().iter().all(|v| !v.is_bound_path()));
    assert!(
        exact
            .phase
            .variables()
            .contains(&KernelVariable::InputKet(0))
    );
    assert!(
        exact
            .phase
            .variables()
            .contains(&KernelVariable::QuantumOutputBra(0))
    );
}
