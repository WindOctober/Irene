use std::cell::RefCell;

use num_rational::BigRational;
use rug::Float;

use crate::frontend::openqasm3::parse_str;
use crate::ir::{
    AstIdGenerator, AstNode, Block, BlockData, ClassicalBit, ClassicalExpr, ClassicalExprKind,
    Gate, NumericConstant, NumericExpr, NumericExprKind, OpenQasmVersion, Program, ProgramData,
    Qubit, RegisterData, Statement, StatementKind, SymbolId,
};

use super::{
    BooleanPolynomial, ExecutionConfig, HistoryEntry, HybridPathSum, Monomial, OutputSelection,
    PhaseCoefficient, Scalar, ScalarBindings, SymbolicError, Variable, execute as execute_observed,
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

fn node<T>(kind: T) -> AstNode<T> {
    thread_local! {
        static IDS: RefCell<AstIdGenerator> = RefCell::new(AstIdGenerator::default());
    }
    IDS.with(|ids| ids.borrow_mut().node(kind))
}

fn statement(kind: StatementKind) -> Statement {
    node(kind)
}

fn block(statements: Vec<Statement>) -> Block {
    node(BlockData {
        classical_registers: Vec::new(),
        statements,
    })
}

fn classical(kind: ClassicalExprKind) -> ClassicalExpr {
    node(kind)
}

fn numeric(kind: NumericExprKind) -> NumericExpr {
    node(kind)
}

fn program(qubits: usize, bits: usize, statements: Vec<Statement>) -> Program {
    node(ProgramData {
        version: OpenQasmVersion { major: 3, minor: 0 },
        numeric_inputs: Vec::new(),
        quantum_registers: vec![node(RegisterData {
            id: SymbolId(0),
            name: "q".into(),
            width: qubits,
        })],
        classical_registers: vec![node(RegisterData {
            id: SymbolId(1),
            name: "c".into(),
            width: bits,
        })],
        body: block(statements),
    })
}

fn execute_all_outputs(
    program: &Program,
    config: &ExecutionConfig,
) -> Result<HybridPathSum, SymbolicError> {
    let quantum = program.quantum_registers.iter().flat_map(|register| {
        (0..register.width).map(|index| Qubit {
            register: register.id,
            index,
        })
    });
    let classical = program.classical_registers.iter().flat_map(|register| {
        (0..register.width).map(|index| ClassicalBit {
            register: register.id,
            index,
        })
    });
    execute_observed(program, config, &OutputSelection::new(quantum, classical))
}

#[test]
fn subroutine_measurement_return_reaches_the_caller() {
    let program = parse_str(
        r#"
        OPENQASM 3.0;
        def read(qubit source) -> bit {
            bit result;
            result = measure source;
            return result;
        }
        qubit data;
        bit result_out;
        result_out = read(data);
        "#,
        "subroutine-return.qasm",
    )
    .unwrap();
    let data = Qubit {
        register: program.quantum_registers[0].id,
        index: 0,
    };
    let output = ClassicalBit {
        register: program.classical_registers[0].id,
        index: 0,
    };

    let hps = execute_observed(
        &program,
        &ExecutionConfig::with_symbolic_inputs([data.clone()]),
        &OutputSelection::new([], [output.clone()]),
    )
    .unwrap();

    assert_eq!(hps.components.len(), 1);
    assert_eq!(
        hps.components[0].output.classical[&output],
        BooleanPolynomial::variable(Variable::Input(data))
    );
}

#[test]
fn register_subroutine_updates_caller_qubits_and_returns_bits() {
    let program = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        def clear_and_read(qubit[2] q) -> bit[2] {
            bit[2] result;
            reset q;
            result = measure q;
            return result;
        }
        qubit[2] data;
        bit[2] result;
        result = clear_and_read(data);
        if (int[2](result) == 0) x data[0];
        "#,
        "register-subroutine.qasm",
    )
    .unwrap();

    let hps = execute_all_outputs(&program, &ExecutionConfig::all_symbolic()).unwrap();
    let data = &program.quantum_registers[0];
    let result = &program.classical_registers[0];
    let component = &hps.components[0];
    assert!(
        component.output.quantum[&Qubit {
            register: data.id,
            index: 0,
        }]
            .is_one()
    );
    assert!(
        component.output.quantum[&Qubit {
            register: data.id,
            index: 1,
        }]
            .is_zero()
    );
    for index in 0..2 {
        assert!(
            component.output.classical[&ClassicalBit {
                register: result.id,
                index,
            }]
                .is_zero()
        );
    }
}

#[test]
fn signed_and_unsigned_casts_interpret_the_same_bits_differently() {
    let program = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        qubit[2] data;
        qubit[2] flags;
        bit[2] bits;
        x data[1];
        bits = measure data;
        if (int[2](bits) == -2) x flags[0];
        if (uint[2](bits) == 2) x flags[1];
        "#,
        "signed-unsigned-casts.qasm",
    )
    .unwrap();

    let hps = execute_all_outputs(&program, &ExecutionConfig::zero()).unwrap();
    assert_eq!(hps.components.len(), 1);
    let component = &hps.components[0];
    let flags = &program.quantum_registers[1];
    for index in 0..2 {
        assert!(
            component.output.quantum[&Qubit {
                register: flags.id,
                index,
            }]
                .is_one()
        );
    }
}

#[test]
fn hadamard_introduces_a_path_and_phase() {
    let q = qubit(0, 0);
    let hps = execute_all_outputs(
        &program(
            1,
            0,
            vec![statement(StatementKind::Apply {
                gate: Gate::H,
                parameters: Vec::new(),
                qubits: vec![q.clone()],
            })],
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
    let hps = execute_all_outputs(
        &program(
            2,
            1,
            vec![
                statement(StatementKind::Apply {
                    gate: Gate::H,
                    parameters: Vec::new(),
                    qubits: vec![measured.clone()],
                }),
                statement(StatementKind::Measure {
                    qubit: measured,
                    target: outcome.clone(),
                }),
                statement(StatementKind::If {
                    condition: classical(ClassicalExprKind::Bit(outcome.clone())),
                    then_branch: block(vec![statement(StatementKind::Apply {
                        gate: Gate::H,
                        parameters: Vec::new(),
                        qubits: vec![target.clone()],
                    })]),
                    else_branch: block(Vec::new()),
                }),
            ],
        ),
        &ExecutionConfig::all_symbolic(),
    )
    .unwrap();

    assert_eq!(hps.components.len(), 2);
    assert!(
        hps.components
            .iter()
            .all(|component| component.guard.is_empty())
    );
    assert!(hps.components.iter().any(|component| {
        component.path_support.len() == 1
            && matches!(
                &component.output.history[0],
                HistoryEntry::Write { target, value }
                    if target == &outcome && value.is_one()
            )
    }));
    assert!(hps.components.iter().any(|component| {
        component.path_support.is_empty()
            && matches!(
                &component.output.history[0],
                HistoryEntry::Write { target, value }
                    if target == &outcome && value.is_zero()
            )
    }));
}

#[test]
fn affine_branch_relations_eliminate_path_variables() {
    let q0 = qubit(0, 0);
    let q1 = qubit(0, 1);
    let c0 = bit(1, 0);
    let c1 = bit(1, 1);
    let hps = execute_all_outputs(
        &program(
            2,
            2,
            vec![
                statement(StatementKind::Apply {
                    gate: Gate::H,
                    parameters: Vec::new(),
                    qubits: vec![q0.clone()],
                }),
                statement(StatementKind::Apply {
                    gate: Gate::H,
                    parameters: Vec::new(),
                    qubits: vec![q1.clone()],
                }),
                statement(StatementKind::Measure {
                    qubit: q0.clone(),
                    target: c0.clone(),
                }),
                statement(StatementKind::Measure {
                    qubit: q1,
                    target: c1.clone(),
                }),
                statement(StatementKind::If {
                    condition: classical(ClassicalExprKind::Xor(
                        Box::new(classical(ClassicalExprKind::Bit(c0))),
                        Box::new(classical(ClassicalExprKind::Bit(c1))),
                    )),
                    then_branch: block(vec![statement(StatementKind::Apply {
                        gate: Gate::X,
                        parameters: Vec::new(),
                        qubits: vec![q0.clone()],
                    })]),
                    else_branch: block(Vec::new()),
                }),
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
fn nonlinear_branch_constraints_remain_exact() {
    let q0 = qubit(0, 0);
    let q1 = qubit(0, 1);
    let c0 = bit(1, 0);
    let c1 = bit(1, 1);
    let hps = execute_all_outputs(
        &program(
            2,
            2,
            vec![
                statement(StatementKind::Apply {
                    gate: Gate::H,
                    parameters: Vec::new(),
                    qubits: vec![q0.clone()],
                }),
                statement(StatementKind::Apply {
                    gate: Gate::H,
                    parameters: Vec::new(),
                    qubits: vec![q1.clone()],
                }),
                statement(StatementKind::Measure {
                    qubit: q0.clone(),
                    target: c0.clone(),
                }),
                statement(StatementKind::Measure {
                    qubit: q1,
                    target: c1.clone(),
                }),
                statement(StatementKind::If {
                    condition: classical(ClassicalExprKind::And(
                        Box::new(classical(ClassicalExprKind::Bit(c0))),
                        Box::new(classical(ClassicalExprKind::Bit(c1))),
                    )),
                    then_branch: block(vec![statement(StatementKind::Apply {
                        gate: Gate::X,
                        parameters: Vec::new(),
                        qubits: vec![q0.clone()],
                    })]),
                    else_branch: block(Vec::new()),
                }),
            ],
        ),
        &ExecutionConfig::zero(),
    )
    .unwrap();

    let then_component = hps
        .components
        .iter()
        .find(|component| component.guard.is_empty())
        .unwrap();
    assert!(then_component.guard.is_empty());
    assert!(then_component.path_support.is_empty());

    let else_component = hps
        .components
        .iter()
        .find(|component| !component.guard.is_empty())
        .unwrap();
    assert_eq!(else_component.path_support.len(), 2);
    assert_eq!(else_component.guard.len(), 1);
    assert!(!else_component.guard[0].is_affine());
}

#[test]
fn reading_an_uninitialized_classical_bit_is_rejected() {
    let condition = bit(1, 0);
    let error = execute_all_outputs(
        &program(
            1,
            1,
            vec![statement(StatementKind::If {
                condition: classical(ClassicalExprKind::Bit(condition.clone())),
                then_branch: block(vec![statement(StatementKind::Apply {
                    gate: Gate::X,
                    parameters: Vec::new(),
                    qubits: vec![qubit(0, 0)],
                })]),
                else_branch: block(Vec::new()),
            })],
        ),
        &ExecutionConfig::zero(),
    )
    .unwrap_err();

    assert_eq!(error, SymbolicError::UninitializedClassical(condition));
}

#[test]
fn output_slicing_does_not_hide_an_uninitialized_condition() {
    let condition = bit(1, 0);
    let observed = qubit(0, 1);
    let program = program(
        2,
        1,
        vec![statement(StatementKind::If {
            condition: classical(ClassicalExprKind::Bit(condition.clone())),
            then_branch: block(vec![statement(StatementKind::Apply {
                gate: Gate::X,
                parameters: Vec::new(),
                qubits: vec![qubit(0, 0)],
            })]),
            else_branch: block(Vec::new()),
        })],
    );

    let error = execute_observed(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new([observed], []),
    )
    .unwrap_err();

    assert_eq!(error, SymbolicError::UninitializedClassical(condition));
}

#[test]
fn a_selected_classical_bit_must_be_assigned_on_every_path() {
    let output = bit(1, 0);
    let program = program(1, 1, Vec::new());

    let error = execute_observed(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new([], [output.clone()]),
    )
    .unwrap_err();

    assert_eq!(error, SymbolicError::UninitializedClassical(output));
}

#[test]
fn a_constant_branch_preserves_definite_assignment() {
    let output = bit(1, 0);
    let program = program(
        1,
        1,
        vec![statement(StatementKind::If {
            condition: classical(ClassicalExprKind::Bool(true)),
            then_branch: block(vec![statement(StatementKind::Measure {
                qubit: qubit(0, 0),
                target: output.clone(),
            })]),
            else_branch: block(Vec::new()),
        })],
    );

    execute_observed(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new([], [output]),
    )
    .unwrap();
}

#[test]
fn reset_records_decoherence_before_reinitializing() {
    let q = qubit(0, 0);
    let hps = execute_all_outputs(
        &program(
            1,
            0,
            vec![
                statement(StatementKind::Apply {
                    gate: Gate::H,
                    parameters: Vec::new(),
                    qubits: vec![q.clone()],
                }),
                statement(StatementKind::Reset(q.clone())),
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
            value: BooleanPolynomial::variable(Variable::Input(q)),
        }]
    );
}

#[test]
fn output_slice_keeps_an_entangled_discard_as_hidden_history() {
    let environment = qubit(0, 0);
    let output = qubit(0, 1);
    let program = program(
        2,
        0,
        vec![
            statement(StatementKind::Apply {
                gate: Gate::H,
                parameters: Vec::new(),
                qubits: vec![environment.clone()],
            }),
            statement(StatementKind::Apply {
                gate: Gate::Cx,
                parameters: Vec::new(),
                qubits: vec![environment.clone(), output.clone()],
            }),
        ],
    );
    let projected = execute_observed(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new([output.clone()], []),
    )
    .unwrap();

    let component = &projected.components[0];
    assert_eq!(component.output.quantum.len(), 1);
    assert_eq!(
        component.output.quantum[&output],
        BooleanPolynomial::variable(Variable::Path(0))
    );
    assert_eq!(
        component.output.history,
        vec![HistoryEntry::Discard {
            value: BooleanPolynomial::variable(Variable::Path(0)),
        }]
    );
}

#[test]
fn output_slice_removes_a_dead_measurement_cone() {
    let dead = qubit(0, 0);
    let output = qubit(0, 1);
    let measured = bit(1, 0);
    let program = program(
        2,
        1,
        vec![
            statement(StatementKind::Apply {
                gate: Gate::H,
                parameters: Vec::new(),
                qubits: vec![dead.clone()],
            }),
            statement(StatementKind::Measure {
                qubit: dead,
                target: measured,
            }),
        ],
    );
    let projected = execute_observed(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new([output.clone()], []),
    )
    .unwrap();

    let component = &projected.components[0];
    assert!(component.path_support.is_empty());
    assert!(component.output.history.is_empty());
    assert_eq!(component.output.quantum.len(), 1);
    assert_eq!(component.output.quantum[&output], BooleanPolynomial::zero());
}

#[test]
fn output_slice_drops_an_unused_measurement_target_after_dephasing() {
    let output = qubit(0, 0);
    let unused = bit(1, 0);
    let program = program(
        1,
        1,
        vec![
            statement(StatementKind::Apply {
                gate: Gate::H,
                parameters: Vec::new(),
                qubits: vec![output.clone()],
            }),
            statement(StatementKind::Measure {
                qubit: output.clone(),
                target: unused.clone(),
            }),
        ],
    );
    let projected = execute_observed(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new([output], []),
    )
    .unwrap();

    let component = &projected.components[0];
    assert!(component.output.classical.is_empty());
    assert!(matches!(
        &component.output.history[0],
        HistoryEntry::Write { target, value }
            if target == &unused
                && value == &BooleanPolynomial::variable(Variable::Path(0))
    ));
}

#[test]
fn discarding_a_measured_qubit_reuses_the_measurement_history() {
    let measured = qubit(0, 0);
    let output = bit(1, 0);
    let program = program(
        1,
        1,
        vec![
            statement(StatementKind::Apply {
                gate: Gate::H,
                parameters: Vec::new(),
                qubits: vec![measured.clone()],
            }),
            statement(StatementKind::Measure {
                qubit: measured,
                target: output.clone(),
            }),
        ],
    );

    let projected = execute_observed(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new([], [output]),
    )
    .unwrap();

    assert_eq!(projected.components[0].output.history.len(), 1);
    assert!(matches!(
        projected.components[0].output.history[0],
        HistoryEntry::Write { .. }
    ));
}

#[test]
fn output_slice_preserves_inputs_that_feed_a_selected_output() {
    let input = qubit(0, 0);
    let output = qubit(0, 1);
    let program = program(
        2,
        0,
        vec![statement(StatementKind::Apply {
            gate: Gate::Cx,
            parameters: Vec::new(),
            qubits: vec![input.clone(), output.clone()],
        })],
    );
    let projected = execute_observed(
        &program,
        &ExecutionConfig::with_symbolic_inputs([input.clone()]),
        &OutputSelection::new([output.clone()], []),
    )
    .unwrap();

    assert!(projected.input.quantum.contains_key(&input));
    assert_eq!(
        projected.components[0].output.quantum[&output],
        BooleanPolynomial::variable(Variable::Input(input))
    );
}

#[test]
fn output_slice_records_a_reset_symbolic_input_as_traced_out() {
    let input = qubit(0, 0);
    let program = program(1, 0, vec![statement(StatementKind::Reset(input.clone()))]);
    let projected = execute_observed(
        &program,
        &ExecutionConfig::with_symbolic_inputs([input.clone()]),
        &OutputSelection::new([input.clone()], []),
    )
    .unwrap();

    assert!(projected.input.quantum.contains_key(&input));
    assert_eq!(
        projected.components[0].output.history,
        vec![HistoryEntry::Discard {
            value: BooleanPolynomial::variable(Variable::Input(input.clone())),
        }]
    );
    assert_eq!(
        projected.components[0].output.quantum[&input],
        BooleanPolynomial::zero()
    );
}

#[test]
fn phase_lifting_preserves_xor_semantics() {
    let control = qubit(0, 0);
    let target = qubit(0, 1);
    let hps = execute_all_outputs(
        &program(
            2,
            0,
            vec![
                statement(StatementKind::Apply {
                    gate: Gate::Cx,
                    parameters: Vec::new(),
                    qubits: vec![control.clone(), target.clone()],
                }),
                statement(StatementKind::Apply {
                    gate: Gate::T,
                    parameters: Vec::new(),
                    qubits: vec![target.clone()],
                }),
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
    let angle = numeric(NumericExprKind::Rational(ratio(1, 10)));
    let hps = execute_all_outputs(
        &program(
            1,
            0,
            vec![statement(StatementKind::Apply {
                gate: Gate::Rz,
                parameters: vec![angle.clone()],
                qubits: vec![q.clone()],
            })],
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
fn phase_angles_have_a_linear_canonical_form() {
    let theta = numeric(NumericExprKind::Input(SymbolId(20)));
    let half = |value: NumericExpr| {
        numeric(NumericExprKind::Div(
            Box::new(value),
            Box::new(numeric(NumericExprKind::Rational(ratio(2, 1)))),
        ))
    };
    let split_theta = numeric(NumericExprKind::Add(
        Box::new(half(theta.clone())),
        Box::new(half(theta.clone())),
    ));
    assert_eq!(
        PhaseCoefficient::angle(split_theta, ratio(1, 1)),
        PhaseCoefficient::angle(theta, ratio(1, 1))
    );

    let half_pi = half(numeric(NumericExprKind::Constant(NumericConstant::Pi)));
    assert_eq!(
        PhaseCoefficient::angle(half_pi, ratio(1, 1)),
        PhaseCoefficient::rational(ratio(1, 4))
    );
    assert_eq!(
        PhaseCoefficient::angle(
            numeric(NumericExprKind::Constant(NumericConstant::Tau)),
            ratio(1, 1),
        ),
        PhaseCoefficient::rational(ratio(0, 1))
    );
}

#[test]
fn nonlinear_angle_products_are_canonical_up_to_operand_order() {
    let theta = numeric(NumericExprKind::Input(SymbolId(20)));
    let phi = numeric(NumericExprKind::Input(SymbolId(21)));
    let left = numeric(NumericExprKind::Mul(
        Box::new(theta.clone()),
        Box::new(phi.clone()),
    ));
    let right = numeric(NumericExprKind::Mul(Box::new(phi), Box::new(theta)));

    assert_eq!(
        PhaseCoefficient::angle(left, ratio(1, 1)),
        PhaseCoefficient::angle(right, ratio(1, 1))
    );
}

#[test]
fn y_and_controlled_y_have_the_standard_phase_and_permutation() {
    let control = qubit(0, 0);
    let target = qubit(0, 1);
    let hps = execute_all_outputs(
        &program(
            2,
            0,
            vec![statement(StatementKind::Apply {
                gate: Gate::Cy,
                parameters: Vec::new(),
                qubits: vec![control.clone(), target.clone()],
            })],
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
    let angle = numeric(NumericExprKind::Constant(NumericConstant::Pi));
    let hps = execute_all_outputs(
        &program(
            2,
            0,
            vec![statement(StatementKind::Apply {
                gate: Gate::Crz,
                parameters: vec![angle.clone()],
                qubits: vec![control.clone(), target.clone()],
            })],
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
    let hps = execute_all_outputs(&program, &ExecutionConfig::default()).unwrap();

    assert_eq!(hps.input.quantum[&qubit(0, 0)], BooleanPolynomial::zero());
    assert_eq!(hps.input.quantum[&qubit(0, 1)], BooleanPolynomial::zero());
}

#[test]
fn selected_inputs_are_symbolic_and_other_qubits_are_zero() {
    let symbolic = qubit(0, 1);
    let program = program(2, 0, Vec::new());
    let config = ExecutionConfig::with_symbolic_inputs([symbolic.clone()]);
    let hps = execute_all_outputs(&program, &config).unwrap();

    assert_eq!(hps.input.quantum[&qubit(0, 0)], BooleanPolynomial::zero());
    assert_eq!(
        hps.input.quantum[&symbolic],
        BooleanPolynomial::variable(Variable::Input(symbolic.clone()))
    );
}

#[test]
fn rx_uses_sine_for_flips_and_minus_i_in_the_phase() {
    let q = qubit(0, 0);
    let angle = numeric(NumericExprKind::Constant(NumericConstant::Pi));
    let hps = execute_all_outputs(
        &program(
            1,
            0,
            vec![statement(StatementKind::Apply {
                gate: Gate::Rx,
                parameters: vec![angle],
                qubits: vec![q.clone()],
            })],
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
    let hps = execute_all_outputs(
        &program(
            1,
            0,
            vec![statement(StatementKind::Apply {
                gate: Gate::Ry,
                parameters: vec![numeric(NumericExprKind::Constant(NumericConstant::Pi))],
                qubits: vec![q.clone()],
            })],
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
        let hps = execute_all_outputs(
            &program(
                2,
                0,
                vec![statement(StatementKind::Apply {
                    gate,
                    parameters: vec![numeric(NumericExprKind::Constant(NumericConstant::Pi))],
                    qubits: vec![control.clone(), target.clone()],
                })],
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
