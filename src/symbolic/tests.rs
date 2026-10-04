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
    PhaseCoefficient, PhasePolynomial, Scalar, ScalarBindings, SymbolicError, Variable,
    execute as execute_observed,
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

#[test]
fn integer_phase_scaling_is_independent_of_modular_representative() {
    for numerator in -16..=16 {
        for denominator in 1..=12 {
            for scale in -4..=4 {
                let phase = PhaseCoefficient::rational(ratio(numerator, denominator));
                let shifted =
                    PhaseCoefficient::rational(ratio(numerator, denominator) + ratio(3, 1));
                let expected = PhaseCoefficient::rational(ratio(numerator * scale, denominator));
                assert_eq!(phase.scaled(scale.into()), expected);
                assert_eq!(shifted.scaled(scale.into()), expected);
            }
        }
    }
    let mut ids = AstIdGenerator::default();
    let angle = ids.node(NumericExprKind::Input(SymbolId(7)));
    let phase = PhaseCoefficient::angle(angle.clone(), ratio(2, 3));
    for scale in -4..=4 {
        assert_eq!(
            phase.scaled(scale.into()),
            PhaseCoefficient::angle(angle.clone(), ratio(2 * scale, 3)),
        );
    }
}

#[test]
fn sparse_boolean_and_phase_substitution_match_distributive_reference() {
    let variables = [Variable::Path(0), Variable::Path(1)];
    let x = BooleanPolynomial::variable(variables[0].clone());
    let y = BooleanPolynomial::variable(variables[1].clone());
    let atoms = [BooleanPolynomial::one(), x.clone(), y.clone(), x.and(&y)];
    let polynomial = |bits: usize| {
        atoms
            .iter()
            .enumerate()
            .fold(BooleanPolynomial::zero(), |sum, (i, m)| {
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
            for variable in &variables {
                let expand = |monomial: &Monomial| {
                    monomial
                        .variables()
                        .fold(BooleanPolynomial::one(), |product, current| {
                            product.and(&if current == variable {
                                replacement.clone()
                            } else {
                                BooleanPolynomial::variable(current.clone())
                            })
                        })
                };
                let expected = source
                    .terms()
                    .fold(BooleanPolynomial::zero(), |sum, monomial| {
                        sum.xor(&expand(&monomial))
                    });
                assert_eq!(
                    source.substitute(variable, &replacement).expanded_terms(64),
                    expected.expanded_terms(64)
                );
                let mut phase = PhasePolynomial::zero();
                for (i, monomial) in source.terms().enumerate() {
                    phase.add_boolean(
                        &BooleanPolynomial::from_monomial(monomial.clone()),
                        PhaseCoefficient::rational(ratio(1, [8, 3, 4, 7][i])),
                    );
                }
                let mut reference = PhasePolynomial::zero();
                for (monomial, coefficient) in phase.terms() {
                    reference.add_boolean(&expand(&monomial), coefficient.clone());
                }
                phase.substitute(variable, &replacement);
                assert_eq!(phase.expanded_terms(1024), reference.expanded_terms(1024));
            }
        }
    }
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
fn typed_classical_values_compare_casts_literals_and_computed_bits() {
    let program = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        qubit[6] flags;
        bit[3] negative = "110";
        bit[3] positive = "010";
        if (int[3](negative) == int[3]("110")) x flags[0];
        if (-2 == int[3](negative)) x flags[1];
        if (int[3](negative) < int[3](positive)) x flags[2];
        if (uint[3](negative) > uint[3](positive)) x flags[3];
        if (int[3](negative ^ "001") == -1) x flags[4];
        if (1 < 2) x flags[5];
        "#,
        "typed-classical-values.qasm",
    )
    .unwrap();

    let hps = execute_all_outputs(&program, &ExecutionConfig::zero()).unwrap();
    assert_eq!(hps.components.len(), 1);
    let component = &hps.components[0];
    let flags = &program.quantum_registers[0];
    for index in 0..6 {
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
fn classical_bit_expressions_preserve_scalar_and_register_semantics() {
    let program = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        qubit[5] q;
        bit[3] bits = "101";
        bit a = true;
        bit b = false;
        bit result;
        result = (a & ~b) | (b ^ false);
        a ^= true;
        if (result != a) x q[0];
        if (bits == "101") x q[1];
        bits &= "011";
        if (bits == "001") x q[2];
        bool ordered = bits < "110";
        if (ordered && bool(result)) x q[3];
        bit measured = measure q[4];
        if (!measured) x q[4];
        "#,
        "classical-bit-expressions.qasm",
    )
    .unwrap();

    let hps = execute_all_outputs(&program, &ExecutionConfig::zero()).unwrap();
    assert_eq!(hps.components.len(), 1);
    let component = &hps.components[0];
    let q = &program.quantum_registers[0];
    for index in 0..5 {
        assert!(
            component.output.quantum[&Qubit {
                register: q.id,
                index,
            }]
                .is_one()
        );
    }
}

#[test]
fn bit_register_ordering_uses_unsigned_little_endian_values() {
    let program = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        qubit[4] q;
        bit[3] value = "101";
        if (value < "110") x q[0];
        if (value <= "101") x q[1];
        if (value > "100") x q[2];
        if (value >= "101") x q[3];
        "#,
        "bit-register-ordering.qasm",
    )
    .unwrap();

    let hps = execute_all_outputs(&program, &ExecutionConfig::zero()).unwrap();
    let component = &hps.components[0];
    let q = &program.quantum_registers[0];
    for index in 0..4 {
        assert!(
            component.output.quantum[&Qubit {
                register: q.id,
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
fn affine_predicated_x_avoids_world_splitting() {
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

    let component = &hps.components[0];
    assert_eq!(hps.components.len(), 1);
    assert!(component.guard.is_empty());
    assert_eq!(component.path_support, [0, 1].into());
    assert_eq!(
        component.output.quantum[&q0],
        BooleanPolynomial::variable(Variable::Path(1))
    );
}

#[test]
fn nonlinear_predicate_remains_exact_without_world_splitting() {
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

    let component = &hps.components[0];
    let left = BooleanPolynomial::variable(Variable::Path(0));
    let right = BooleanPolynomial::variable(Variable::Path(1));
    assert_eq!(hps.components.len(), 1);
    assert!(component.guard.is_empty());
    assert_eq!(component.path_support, [0, 1].into());
    let mut expected = component.clone();
    expected.output.quantum.insert(q0, left.xor(&left.and(&right)));
    super::optimize::assert_density(
        std::slice::from_ref(component),
        std::slice::from_ref(&expected),
    );
}

#[test]
fn predicated_phase_matches_deferred_measurement() {
    let control = qubit(0, 0);
    let target = qubit(0, 1);
    let outcome = bit(1, 0);
    let angle = numeric(NumericExprKind::Div(
        Box::new(numeric(NumericExprKind::Constant(NumericConstant::Pi))),
        Box::new(numeric(NumericExprKind::Rational(ratio(4, 1)))),
    ));
    let dynamic = program(
        2,
        1,
        vec![
            statement(StatementKind::Apply {
                gate: Gate::H,
                parameters: Vec::new(),
                qubits: vec![control.clone()],
            }),
            statement(StatementKind::Measure {
                qubit: control.clone(),
                target: outcome.clone(),
            }),
            statement(StatementKind::If {
                condition: classical(ClassicalExprKind::Bit(outcome.clone())),
                then_branch: block(vec![statement(StatementKind::Apply {
                    gate: Gate::P,
                    parameters: vec![angle.clone()],
                    qubits: vec![target.clone()],
                })]),
                else_branch: block(Vec::new()),
            }),
        ],
    );
    let deferred = program(
        2,
        1,
        vec![
            statement(StatementKind::Apply {
                gate: Gate::H,
                parameters: Vec::new(),
                qubits: vec![control.clone()],
            }),
            statement(StatementKind::Apply {
                gate: Gate::Cp,
                parameters: vec![angle],
                qubits: vec![control.clone(), target.clone()],
            }),
            statement(StatementKind::Measure {
                qubit: control,
                target: outcome.clone(),
            }),
        ],
    );
    let selection = OutputSelection::new([target], [outcome]);

    let dynamic = execute_observed(&dynamic, &ExecutionConfig::all_symbolic(), &selection).unwrap();
    let deferred =
        execute_observed(&deferred, &ExecutionConfig::all_symbolic(), &selection).unwrap();

    assert_eq!(dynamic, deferred);
    assert_eq!(dynamic.components.len(), 1);
}

#[test]
fn predicated_else_uses_the_complementary_condition() {
    let control = qubit(0, 0);
    let flipped = qubit(0, 1);
    let phased = qubit(0, 2);
    let outcome = bit(1, 0);
    let hps = execute_all_outputs(
        &program(
            3,
            1,
            vec![
                statement(StatementKind::Apply {
                    gate: Gate::H,
                    parameters: Vec::new(),
                    qubits: vec![control],
                }),
                statement(StatementKind::Measure {
                    qubit: qubit(0, 0),
                    target: outcome,
                }),
                statement(StatementKind::If {
                    condition: classical(ClassicalExprKind::Bit(bit(1, 0))),
                    then_branch: block(vec![statement(StatementKind::Apply {
                        gate: Gate::X,
                        parameters: Vec::new(),
                        qubits: vec![flipped.clone()],
                    })]),
                    else_branch: block(vec![statement(StatementKind::Apply {
                        gate: Gate::Z,
                        parameters: Vec::new(),
                        qubits: vec![phased.clone()],
                    })]),
                }),
            ],
        ),
        &ExecutionConfig::all_symbolic(),
    )
    .unwrap();

    let component = &hps.components[0];
    let predicate = BooleanPolynomial::variable(Variable::Path(0));
    assert_eq!(hps.components.len(), 1);
    assert_eq!(
        component.output.quantum[&flipped],
        BooleanPolynomial::variable(Variable::Input(flipped.clone())).xor(&predicate)
    );
    let phased_input = Monomial::variable(Variable::Input(phased.clone()));
    let predicate_and_input = Monomial::variable(Variable::Path(0))
        .multiply(&Monomial::variable(Variable::Input(phased)));
    assert_eq!(
        component.phase.coefficient(&phased_input),
        PhaseCoefficient::rational(ratio(1, 2))
    );
    assert_eq!(
        component.phase.coefficient(&predicate_and_input),
        PhaseCoefficient::rational(ratio(1, 2))
    );
}

#[test]
fn branch_local_partial_trace_preserves_the_observed_distribution() {
    let measured = qubit(0, 0);
    let environment = qubit(0, 1);
    let output = qubit(0, 2);
    let outcome = bit(1, 0);
    let program = program(
        3,
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
            statement(StatementKind::Apply {
                gate: Gate::H,
                parameters: Vec::new(),
                qubits: vec![environment.clone()],
            }),
            statement(StatementKind::If {
                condition: classical(ClassicalExprKind::Bit(outcome.clone())),
                then_branch: block(vec![statement(StatementKind::Apply {
                    gate: Gate::Cx,
                    parameters: Vec::new(),
                    qubits: vec![environment, output.clone()],
                })]),
                else_branch: block(Vec::new()),
            }),
        ],
    );

    let hps = execute_observed(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new([output.clone()], [outcome.clone()]),
    )
    .unwrap();

    // c=0 leaves the output at zero with probability 1/2.
    // c=1 gives an equal classical mixture of output zero and one.
    let expected: Vec<_> = [(false, false), (true, false), (true, true)]
        .into_iter()
        .map(|(c, value)| super::Component {
            guard: Vec::new(),
            path_support: Default::default(),
            phase: super::PhasePolynomial::zero(),
            scalar: if c {
                Scalar::rational(ratio(1, 2))
            } else {
                Scalar::sqrt(Scalar::rational(ratio(1, 2)))
            },
            output: super::HybridMemory {
                quantum: [(output.clone(), BooleanPolynomial::from(value))].into(),
                classical: [(outcome.clone(), BooleanPolynomial::from(c))].into(),
                history: vec![HistoryEntry::Discard {
                    value: BooleanPolynomial::from(value),
                }],
            },
        })
        .collect();
    super::optimize::assert_density(&hps.components, &expected);
}

#[test]
fn a_dead_branch_condition_is_removed_after_predicated_execution() {
    let measured = qubit(0, 0);
    let output = qubit(0, 1);
    let outcome = bit(1, 0);
    let program = program(
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
                    gate: Gate::X,
                    parameters: Vec::new(),
                    qubits: vec![output.clone()],
                })]),
                else_branch: block(Vec::new()),
            }),
        ],
    );

    let hps = execute_observed(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new([output.clone()], []),
    )
    .unwrap();

    assert_eq!(hps.components.len(), 1);
    assert!(!hps.components[0].output.classical.contains_key(&outcome));
    assert_eq!(
        hps.components[0].output.quantum[&output],
        BooleanPolynomial::variable(Variable::Path(0))
    );
}

#[test]
fn ccz_adds_only_the_exact_cubic_phase_without_paths() {
    let qubits = vec![qubit(0, 0), qubit(0, 1), qubit(0, 2)];
    let hps = execute_all_outputs(
        &program(
            3,
            0,
            vec![statement(StatementKind::Apply {
                gate: Gate::Ccz,
                parameters: Vec::new(),
                qubits: qubits.clone(),
            })],
        ),
        &ExecutionConfig::all_symbolic(),
    )
    .unwrap();
    assert_eq!(hps.components.len(), 1);
    let component = &hps.components[0];
    assert!(component.path_support.is_empty());
    assert!(component.output.history.is_empty());
    assert!(component.guard.is_empty());
    let mut cubic = BooleanPolynomial::one();
    for q in qubits {
        let input = BooleanPolynomial::variable(Variable::Input(q.clone()));
        assert_eq!(component.output.quantum[&q], input);
        cubic = cubic.and(&input);
    }
    let mut expected = PhasePolynomial::zero();
    expected.add_boolean(&cubic, PhaseCoefficient::rational(ratio(1, 2)));
    assert_eq!(component.phase, expected);
    assert_eq!(component.scalar, Scalar::rational(ratio(1, 1)));
}

#[test]
fn predicated_monomial_gates_respect_constant_conditions() {
    let q0 = qubit(0, 0);
    let q1 = qubit(0, 1);
    let q2 = qubit(0, 2);
    let cases = [
        (Gate::X, vec![q0.clone()]),
        (Gate::Y, vec![q0.clone()]),
        (Gate::Z, vec![q0.clone()]),
        (Gate::S, vec![q0.clone()]),
        (Gate::Sdg, vec![q0.clone()]),
        (Gate::T, vec![q0.clone()]),
        (Gate::Tdg, vec![q0.clone()]),
        (Gate::Cx, vec![q0.clone(), q1.clone()]),
        (Gate::Cy, vec![q0.clone(), q1.clone()]),
        (Gate::Cz, vec![q0.clone(), q1.clone()]),
        (Gate::Swap, vec![q0.clone(), q1.clone()]),
        (Gate::P, vec![q0.clone()]),
        (Gate::Rz, vec![q0.clone()]),
        (Gate::Cp, vec![q0.clone(), q1.clone()]),
        (Gate::Crz, vec![q0.clone(), q1.clone()]),
        (Gate::Ccx, vec![q0.clone(), q1.clone(), q2.clone()]),
        (Gate::Ccz, vec![q0.clone(), q1.clone(), q2.clone()]),
    ];

    for (gate, qubits) in cases {
        let parameters = matches!(gate, Gate::P | Gate::Rz | Gate::Cp | Gate::Crz)
            .then(|| numeric(NumericExprKind::Constant(NumericConstant::Pi)))
            .into_iter()
            .collect::<Vec<_>>();
        let apply = || {
            statement(StatementKind::Apply {
                gate,
                parameters: parameters.clone(),
                qubits: qubits.clone(),
            })
        };
        let unconditional = program(3, 0, vec![apply()]);
        let when_true = program(
            3,
            0,
            vec![statement(StatementKind::If {
                condition: classical(ClassicalExprKind::Bool(true)),
                then_branch: block(vec![apply()]),
                else_branch: block(Vec::new()),
            })],
        );
        let when_false = program(
            3,
            0,
            vec![statement(StatementKind::If {
                condition: classical(ClassicalExprKind::Bool(false)),
                then_branch: block(vec![apply()]),
                else_branch: block(Vec::new()),
            })],
        );
        let identity = program(3, 0, Vec::new());

        assert_eq!(
            execute_all_outputs(&when_true, &ExecutionConfig::all_symbolic()).unwrap(),
            execute_all_outputs(&unconditional, &ExecutionConfig::all_symbolic()).unwrap(),
            "true predicate changed {gate:?}"
        );
        assert_eq!(
            execute_all_outputs(&when_false, &ExecutionConfig::all_symbolic()).unwrap(),
            execute_all_outputs(&identity, &ExecutionConfig::all_symbolic()).unwrap(),
            "false predicate did not suppress {gate:?}"
        );
    }
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
fn subroutine_returns_a_computed_classical_value() {
    let program = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        def parity(qubit[2] q) -> bit {
            bit[2] measured;
            measured = measure q;
            return measured[0] ^ measured[1];
        }
        qubit[2] q;
        qubit out;
        bit result;
        x q[0];
        result = parity(q);
        if (result) x out;
        "#,
        "computed-subroutine-return.qasm",
    )
    .unwrap();

    let hps = execute_all_outputs(&program, &ExecutionConfig::zero()).unwrap();
    assert_eq!(hps.components.len(), 1);
    let output = Qubit {
        register: program.quantum_registers[1].id,
        index: 0,
    };
    assert!(hps.components[0].output.quantum[&output].is_one());
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
fn modular_phase_lifting_discards_integer_interactions_early() {
    let variables: Vec<_> = (0..4)
        .map(|index| Variable::Input(qubit(0, index)))
        .collect();
    let parity = variables
        .iter()
        .fold(BooleanPolynomial::zero(), |sum, variable| {
            sum.xor(&BooleanPolynomial::variable(variable.clone()))
        });
    let product = |indices: &[usize]| {
        indices.iter().fold(Monomial::one(), |term, index| {
            term.multiply(&Monomial::variable(variables[*index].clone()))
        })
    };

    let mut half_turn = PhasePolynomial::zero();
    half_turn.add_boolean(&parity, PhaseCoefficient::rational(ratio(1, 2)));
    assert_eq!(
        half_turn.coefficient(&product(&[0])),
        PhaseCoefficient::rational(ratio(1, 2))
    );
    assert_eq!(
        half_turn.coefficient(&product(&[0, 1])),
        PhaseCoefficient::default()
    );

    let mut quarter_turn = PhasePolynomial::zero();
    quarter_turn.add_boolean(&parity, PhaseCoefficient::rational(ratio(1, 4)));
    assert_eq!(
        quarter_turn.coefficient(&product(&[0, 1])),
        PhaseCoefficient::rational(ratio(1, 2))
    );
    assert_eq!(
        quarter_turn.coefficient(&product(&[0, 1, 2])),
        PhaseCoefficient::default()
    );

    let mut eighth_turn = PhasePolynomial::zero();
    eighth_turn.add_boolean(&parity, PhaseCoefficient::rational(ratio(1, 8)));
    assert_eq!(
        eighth_turn.coefficient(&product(&[0, 1])),
        PhaseCoefficient::rational(ratio(3, 4))
    );
    assert_eq!(
        eighth_turn.coefficient(&product(&[0, 1, 2])),
        PhaseCoefficient::rational(ratio(1, 2))
    );
    assert_eq!(
        eighth_turn.coefficient(&product(&[0, 1, 2, 3])),
        PhaseCoefficient::default()
    );

    let theta = numeric(NumericExprKind::Input(SymbolId(9)));
    let mut symbolic = PhasePolynomial::zero();
    symbolic.add_boolean(
        &variables[..2]
            .iter()
            .fold(BooleanPolynomial::zero(), |sum, variable| {
                sum.xor(&BooleanPolynomial::variable((*variable).clone()))
            }),
        PhaseCoefficient::angle(theta.clone(), ratio(1, 1)),
    );
    assert_eq!(
        symbolic.coefficient(&product(&[0, 1])),
        PhaseCoefficient::angle(theta, ratio(-2, 1))
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
