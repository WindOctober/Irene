use num_rational::BigRational;
use rug::Float;

use crate::ir::{
    Block, ClassicalBit, ClassicalExpr, Gate, NumericConstant, NumericExpr, OpenQasmVersion,
    Program, Qubit, Register, Statement, SymbolId,
};

use super::{
    BooleanPolynomial, ExecutionConfig, HistoryEntry, Monomial, PhaseCoefficient, Scalar,
    ScalarBindings, SymbolicError, Variable, execute,
};

fn qubit(register: usize, index: usize) -> Qubit {
    Qubit {
        register: SymbolId(register),
        index,
    }
}

fn bit(register: usize, index: usize) -> ClassicalBit {
    ClassicalBit {
        register: SymbolId(register),
        index,
    }
}

fn ratio(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(numerator.into(), denominator.into())
}

fn program(qubits: usize, bits: usize, statements: Vec<Statement>) -> Program {
    Program {
        version: OpenQasmVersion { major: 3, minor: 0 },
        numeric_inputs: Vec::new(),
        quantum_registers: vec![Register {
            id: SymbolId(0),
            name: "q".into(),
            width: qubits,
        }],
        classical_registers: vec![Register {
            id: SymbolId(1),
            name: "c".into(),
            width: bits,
        }],
        body: Block {
            classical_registers: Vec::new(),
            statements,
        },
    }
}

#[test]
fn hadamard_introduces_a_path_and_phase() {
    let q = qubit(0, 0);
    let hps = execute(
        &program(
            1,
            0,
            vec![Statement::Apply {
                gate: Gate::H,
                parameters: Vec::new(),
                qubits: vec![q.clone()],
            }],
        ),
        &ExecutionConfig::all_symbolic(),
    )
    .unwrap();

    let component = &hps.components[0];
    assert_eq!(component.path_support, [0].into());
    assert_eq!(
        component.scalar,
        Scalar::sqrt(Scalar::rational(ratio(1, 2)))
    );
    assert_eq!(
        component.output.quantum[&q],
        BooleanPolynomial::variable(Variable::Path(0))
    );
    let phase_term =
        Monomial::variable(Variable::Input(q)).multiply(&Monomial::variable(Variable::Path(0)));
    assert_eq!(
        component.phase.coefficient(&phase_term),
        PhaseCoefficient::rational(ratio(1, 2))
    );
}

#[test]
fn measurement_controls_distinct_symbolic_branches() {
    let measured = qubit(0, 0);
    let target = qubit(0, 1);
    let outcome = bit(1, 0);
    let hps = execute(
        &program(
            2,
            1,
            vec![
                Statement::Apply {
                    gate: Gate::H,
                    parameters: Vec::new(),
                    qubits: vec![measured.clone()],
                },
                Statement::Measure {
                    qubit: measured,
                    target: outcome.clone(),
                },
                Statement::If {
                    condition: ClassicalExpr::Bit(outcome.clone()),
                    then_branch: Block {
                        classical_registers: Vec::new(),
                        statements: vec![Statement::Apply {
                            gate: Gate::H,
                            parameters: Vec::new(),
                            qubits: vec![target.clone()],
                        }],
                    },
                    else_branch: Block::default(),
                },
            ],
        ),
        &ExecutionConfig::all_symbolic(),
    )
    .unwrap();

    assert_eq!(hps.components.len(), 2);
    assert!(hps.components[0].guard.is_empty());
    assert!(hps.components[1].guard.is_empty());
    assert_eq!(hps.components[0].path_support, [1].into());
    assert!(hps.components[1].path_support.is_empty());
    assert!(matches!(
        &hps.components[0].output.history[0],
        HistoryEntry::Write { target, value }
            if target == &outcome && value.is_one()
    ));
    assert!(matches!(
        &hps.components[1].output.history[0],
        HistoryEntry::Write { target, value }
            if target == &outcome && value.is_zero()
    ));
}

#[test]
fn affine_branch_relations_are_solved_over_gf2() {
    let q0 = qubit(0, 0);
    let q1 = qubit(0, 1);
    let c0 = bit(1, 0);
    let c1 = bit(1, 1);
    let hps = execute(
        &program(
            2,
            2,
            vec![
                Statement::Apply {
                    gate: Gate::H,
                    parameters: Vec::new(),
                    qubits: vec![q0.clone()],
                },
                Statement::Apply {
                    gate: Gate::H,
                    parameters: Vec::new(),
                    qubits: vec![q1.clone()],
                },
                Statement::Measure {
                    qubit: q0,
                    target: c0.clone(),
                },
                Statement::Measure {
                    qubit: q1,
                    target: c1.clone(),
                },
                Statement::If {
                    condition: ClassicalExpr::Xor(
                        Box::new(ClassicalExpr::Bit(c0)),
                        Box::new(ClassicalExpr::Bit(c1)),
                    ),
                    then_branch: Block::default(),
                    else_branch: Block::default(),
                },
            ],
        ),
        &ExecutionConfig::zero(),
    )
    .unwrap();

    assert_eq!(hps.components.len(), 2);
    for component in &hps.components {
        assert!(component.guard.is_empty());
        assert_eq!(component.path_support.len(), 1);
    }
}

#[test]
fn nonlinear_branch_constraints_are_routed_through_a_bdd() {
    let q0 = qubit(0, 0);
    let q1 = qubit(0, 1);
    let c0 = bit(1, 0);
    let c1 = bit(1, 1);
    let hps = execute(
        &program(
            2,
            2,
            vec![
                Statement::Apply {
                    gate: Gate::H,
                    parameters: Vec::new(),
                    qubits: vec![q0.clone()],
                },
                Statement::Apply {
                    gate: Gate::H,
                    parameters: Vec::new(),
                    qubits: vec![q1.clone()],
                },
                Statement::Measure {
                    qubit: q0,
                    target: c0.clone(),
                },
                Statement::Measure {
                    qubit: q1,
                    target: c1.clone(),
                },
                Statement::If {
                    condition: ClassicalExpr::And(
                        Box::new(ClassicalExpr::Bit(c0)),
                        Box::new(ClassicalExpr::Bit(c1)),
                    ),
                    then_branch: Block::default(),
                    else_branch: Block::default(),
                },
            ],
        ),
        &ExecutionConfig::zero(),
    )
    .unwrap();

    let then_component = &hps.components[0];
    assert!(then_component.guard.is_empty());
    assert!(then_component.path_support.is_empty());

    let else_component = &hps.components[1];
    assert_eq!(else_component.path_support, [0, 1].into());
    assert_eq!(else_component.guard.len(), 1);
    assert!(!else_component.guard[0].is_affine());
}

#[test]
fn reading_an_uninitialized_classical_bit_is_rejected() {
    let condition = bit(1, 0);
    let error = execute(
        &program(
            1,
            1,
            vec![Statement::If {
                condition: ClassicalExpr::Bit(condition.clone()),
                then_branch: Block::default(),
                else_branch: Block::default(),
            }],
        ),
        &ExecutionConfig::zero(),
    )
    .unwrap_err();

    assert_eq!(error, SymbolicError::UninitializedClassical(condition));
}

#[test]
fn reset_records_decoherence_before_reinitializing() {
    let q = qubit(0, 0);
    let hps = execute(
        &program(
            1,
            0,
            vec![
                Statement::Apply {
                    gate: Gate::H,
                    parameters: Vec::new(),
                    qubits: vec![q.clone()],
                },
                Statement::Reset(q.clone()),
            ],
        ),
        &ExecutionConfig::all_symbolic(),
    )
    .unwrap();

    let component = &hps.components[0];
    assert_eq!(component.output.quantum[&q], BooleanPolynomial::zero());
    assert_eq!(
        component.output.history,
        vec![HistoryEntry::Discard {
            value: BooleanPolynomial::variable(Variable::Path(0)),
        }]
    );
}

#[test]
fn phase_lifting_preserves_xor_semantics() {
    let control = qubit(0, 0);
    let target = qubit(0, 1);
    let hps = execute(
        &program(
            2,
            0,
            vec![
                Statement::Apply {
                    gate: Gate::Cx,
                    parameters: Vec::new(),
                    qubits: vec![control.clone(), target.clone()],
                },
                Statement::Apply {
                    gate: Gate::T,
                    parameters: Vec::new(),
                    qubits: vec![target.clone()],
                },
            ],
        ),
        &ExecutionConfig::all_symbolic(),
    )
    .unwrap();

    let cross = Monomial::variable(Variable::Input(control))
        .multiply(&Monomial::variable(Variable::Input(target)));
    assert_eq!(
        hps.components[0].phase.coefficient(&cross),
        PhaseCoefficient::rational(ratio(3, 4))
    );
}

#[test]
fn rz_retains_a_source_angle_in_the_phase() {
    let q = qubit(0, 0);
    let angle = NumericExpr::Rational(ratio(1, 10));
    let hps = execute(
        &program(
            1,
            0,
            vec![Statement::Apply {
                gate: Gate::Rz,
                parameters: vec![angle.clone()],
                qubits: vec![q.clone()],
            }],
        ),
        &ExecutionConfig::all_symbolic(),
    )
    .unwrap();

    let input = Monomial::variable(Variable::Input(q));
    assert_eq!(
        hps.components[0].phase.coefficient(&Monomial::one()),
        PhaseCoefficient::angle(angle.clone(), ratio(-1, 2))
    );
    assert_eq!(
        hps.components[0].phase.coefficient(&input),
        PhaseCoefficient::angle(angle, ratio(1, 1))
    );
}

#[test]
fn y_and_controlled_y_have_the_standard_phase_and_permutation() {
    let control = qubit(0, 0);
    let target = qubit(0, 1);
    let hps = execute(
        &program(
            2,
            0,
            vec![Statement::Apply {
                gate: Gate::Cy,
                parameters: Vec::new(),
                qubits: vec![control.clone(), target.clone()],
            }],
        ),
        &ExecutionConfig::all_symbolic(),
    )
    .unwrap();

    let component = &hps.components[0];
    let control_variable = Variable::Input(control.clone());
    let target_variable = Variable::Input(target.clone());
    assert_eq!(
        component.output.quantum[&target],
        BooleanPolynomial::variable(target_variable.clone())
            .xor(&BooleanPolynomial::variable(control_variable.clone()))
    );
    assert_eq!(
        component
            .phase
            .coefficient(&Monomial::variable(control_variable.clone())),
        PhaseCoefficient::rational(ratio(1, 4))
    );
    assert_eq!(
        component.phase.coefficient(
            &Monomial::variable(control_variable).multiply(&Monomial::variable(target_variable))
        ),
        PhaseCoefficient::rational(ratio(1, 2))
    );
}

#[test]
fn controlled_rz_keeps_the_control_dependent_global_phase() {
    let control = qubit(0, 0);
    let target = qubit(0, 1);
    let angle = NumericExpr::Constant(NumericConstant::Pi);
    let hps = execute(
        &program(
            2,
            0,
            vec![Statement::Apply {
                gate: Gate::Crz,
                parameters: vec![angle.clone()],
                qubits: vec![control.clone(), target.clone()],
            }],
        ),
        &ExecutionConfig::all_symbolic(),
    )
    .unwrap();

    let control_term = Monomial::variable(Variable::Input(control));
    let target_term = Monomial::variable(Variable::Input(target));
    assert_eq!(
        hps.components[0].phase.coefficient(&control_term),
        PhaseCoefficient::angle(angle.clone(), ratio(-1, 2))
    );
    assert_eq!(
        hps.components[0]
            .phase
            .coefficient(&control_term.multiply(&target_term)),
        PhaseCoefficient::angle(angle, ratio(1, 1))
    );
}

#[test]
fn default_initial_state_sets_every_qubit_to_zero() {
    let program = program(2, 0, Vec::new());
    let hps = execute(&program, &ExecutionConfig::default()).unwrap();

    assert_eq!(hps.input.quantum[&qubit(0, 0)], BooleanPolynomial::zero());
    assert_eq!(hps.input.quantum[&qubit(0, 1)], BooleanPolynomial::zero());
}

#[test]
fn selected_inputs_are_symbolic_and_other_qubits_are_zero() {
    let symbolic = qubit(0, 1);
    let program = program(2, 0, Vec::new());
    let config = ExecutionConfig::with_symbolic_inputs([symbolic.clone()]);
    let hps = execute(&program, &config).unwrap();

    assert_eq!(hps.input.quantum[&qubit(0, 0)], BooleanPolynomial::zero());
    assert_eq!(
        hps.input.quantum[&symbolic],
        BooleanPolynomial::variable(Variable::Input(symbolic.clone()))
    );
}

#[test]
fn rx_uses_sine_for_flips_and_minus_i_in_the_phase() {
    let q = qubit(0, 0);
    let angle = NumericExpr::Constant(NumericConstant::Pi);
    let hps = execute(
        &program(
            1,
            0,
            vec![Statement::Apply {
                gate: Gate::Rx,
                parameters: vec![angle],
                qubits: vec![q.clone()],
            }],
        ),
        &ExecutionConfig::all_symbolic(),
    )
    .unwrap();

    let component = &hps.components[0];
    let input = Monomial::variable(Variable::Input(q));
    let path = Monomial::variable(Variable::Path(0));
    assert_eq!(component.path_support, [0].into());
    assert_eq!(
        component.phase.coefficient(&input),
        PhaseCoefficient::rational(ratio(3, 4))
    );
    assert_eq!(
        component.phase.coefficient(&path),
        PhaseCoefficient::rational(ratio(3, 4))
    );
    assert_eq!(
        component.phase.coefficient(&input.multiply(&path)),
        PhaseCoefficient::rational(ratio(1, 2))
    );
}

#[test]
fn ry_places_the_minus_sign_only_on_one_to_zero_transitions() {
    let q = qubit(0, 0);
    let hps = execute(
        &program(
            1,
            0,
            vec![Statement::Apply {
                gate: Gate::Ry,
                parameters: vec![NumericExpr::Constant(NumericConstant::Pi)],
                qubits: vec![q.clone()],
            }],
        ),
        &ExecutionConfig::all_symbolic(),
    )
    .unwrap();

    let component = &hps.components[0];
    let input = Monomial::variable(Variable::Input(q));
    let path = Monomial::variable(Variable::Path(0));
    assert_eq!(
        component.phase.coefficient(&input),
        PhaseCoefficient::rational(ratio(1, 2))
    );
    assert_eq!(
        component.phase.coefficient(&input.multiply(&path)),
        PhaseCoefficient::rational(ratio(1, 2))
    );
}

#[test]
fn controlled_rotations_have_no_spurious_path_when_disabled() {
    let control = qubit(0, 0);
    let target = qubit(0, 1);
    for gate in [Gate::Crx, Gate::Cry] {
        let hps = execute(
            &program(
                2,
                0,
                vec![Statement::Apply {
                    gate,
                    parameters: vec![NumericExpr::Constant(NumericConstant::Pi)],
                    qubits: vec![control.clone(), target.clone()],
                }],
            ),
            &ExecutionConfig::all_symbolic(),
        )
        .unwrap();
        let component = &hps.components[0];
        let scalar = &component.scalar;

        let mut bindings = ScalarBindings::default();
        bindings
            .booleans
            .insert(Variable::Input(control.clone()), false);
        bindings
            .booleans
            .insert(Variable::Input(target.clone()), false);
        bindings.booleans.insert(Variable::Path(0), true);
        assert_eq!(scalar.evaluate(256, &bindings).unwrap(), 0);

        bindings.booleans.insert(Variable::Path(0), false);
        assert_eq!(scalar.evaluate(256, &bindings).unwrap(), 1);

        bindings
            .booleans
            .insert(Variable::Input(control.clone()), true);
        bindings.booleans.insert(Variable::Path(0), true);
        assert_close_to_one(scalar.evaluate(256, &bindings).unwrap());

        let control_term = Monomial::variable(Variable::Input(control.clone()));
        let target_term = Monomial::variable(Variable::Input(target.clone()));
        let path_term = Monomial::variable(Variable::Path(0));
        let control_target = control_term.multiply(&target_term);
        let control_path = control_term.multiply(&path_term);
        let control_target_path = control_target.multiply(&path_term);
        match gate {
            Gate::Crx => {
                assert_eq!(
                    component.phase.coefficient(&control_target),
                    PhaseCoefficient::rational(ratio(3, 4))
                );
                assert_eq!(
                    component.phase.coefficient(&control_path),
                    PhaseCoefficient::rational(ratio(3, 4))
                );
                assert_eq!(
                    component.phase.coefficient(&control_target_path),
                    PhaseCoefficient::rational(ratio(1, 2))
                );
            }
            Gate::Cry => {
                assert_eq!(
                    component.phase.coefficient(&control_target),
                    PhaseCoefficient::rational(ratio(1, 2))
                );
                assert_eq!(
                    component.phase.coefficient(&control_target_path),
                    PhaseCoefficient::rational(ratio(1, 2))
                );
            }
            _ => unreachable!(),
        }
    }
}

#[test]
fn scalar_evaluation_uses_requested_precision() {
    let root_half = Scalar::sqrt(Scalar::rational(ratio(1, 2)));
    let squared = root_half.clone().multiply(root_half);
    let mut error = squared.evaluate(256, &ScalarBindings::default()).unwrap();
    error -= Float::with_val(256, 0.5);
    error.abs_mut();

    assert!(error < Float::with_val(256, 1) >> 200);
}

fn assert_close_to_one(mut value: Float) {
    let precision = value.prec();
    value -= 1;
    value.abs_mut();
    assert!(value < Float::with_val(precision, 1) >> (precision - 40));
}
