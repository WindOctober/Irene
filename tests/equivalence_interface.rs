//! Public interface preparation and validation; no private verifier modules.
use irene::{equivalence::*, frontend::openqasm3, ir::*, symbolic::Variable};
use num_rational::BigRational;

fn parse(body: &str) -> Program {
    irene::frontend::openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
        "interface-test.qasm",
    )
    .unwrap()
}

fn q(program: &Program, index: usize) -> Qubit {
    Qubit {
        register: program.quantum_registers[0].id,
        index,
    }
}

fn terminal_value(side: &PreparedSide, position: usize, input: usize) -> bool {
    let value = &side.terminals[0].outputs[position].value;
    value
        .expanded_terms(16)
        .expect("small Boolean fixture")
        .iter()
        .fold(false, |parity, monomial| {
            parity
                ^ monomial.variables().all(|v| match v {
                    Variable::Input(q) => input & (1 << q.index) != 0,
                    Variable::Path(_) => panic!("deterministic fixture has no path variables"),
                })
        })
}

#[test]
fn paired_inputs_propagate_through_execution_then_share_coordinates() {
    let left = parse("qubit[2] a; cx a[0],a[1];");
    let right = parse("qubit[3] b; cx b[2],b[0];");
    let config = EquivalenceConfig {
        input_pairs: vec![
            InputPair::quantum(q(&left, 0), q(&right, 2)),
            InputPair::quantum(q(&left, 1), q(&right, 0)),
        ],
        output_pairs: vec![
            OutputPair {
                left: Endpoint::Quantum(q(&left, 1)),
                right: Endpoint::Quantum(q(&right, 0)),
            },
            OutputPair {
                left: Endpoint::Quantum(q(&left, 0)),
                right: Endpoint::Quantum(q(&right, 2)),
            },
        ],
        ..Default::default()
    };
    let prepared = prepare_comparison(&left, &right, &config).unwrap();
    assert_eq!(prepared.left.hps.input, prepared.right.hps.input);
    for input in 0..4 {
        let control = input & 1 != 0;
        let target = input & 2 != 0;
        for side in [&prepared.left, &prepared.right] {
            assert_eq!(terminal_value(side, 0, input), control ^ target);
            assert_eq!(terminal_value(side, 1, input), control);
        }
    }
}

#[test]
fn unpaired_qubits_start_at_zero_even_when_observed() {
    let left = parse("qubit[2] a; cx a[0],a[1];");
    let right = parse("qubit b;");
    let config = EquivalenceConfig {
        input_pairs: vec![InputPair::quantum(q(&left, 0), q(&right, 0))],
        output_pairs: vec![OutputPair {
            left: Endpoint::Quantum(q(&left, 1)),
            right: Endpoint::Quantum(q(&right, 0)),
        }],
        ..Default::default()
    };
    let prepared = prepare_comparison(&left, &right, &config).unwrap();
    for input in 0..2 {
        assert_eq!(terminal_value(&prepared.left, 0, input), input == 1);
        assert_eq!(terminal_value(&prepared.right, 0, input), input == 1);
    }
}

#[test]
fn mixed_outputs_request_measurement_but_quantum_pairs_remain_quantum() {
    let left = parse("qubit a; h a;");
    let right = parse("qubit b; bit c; h b; c=measure b;");
    let c = ClassicalBit {
        register: right.classical_registers[0].id,
        index: 0,
    };
    let config = EquivalenceConfig {
        output_pairs: vec![OutputPair {
            left: Endpoint::Quantum(q(&left, 0)),
            right: Endpoint::Classical(c),
        }],
        ..Default::default()
    };
    let mixed = prepare_comparison(&left, &right, &config).unwrap();
    assert_eq!(mixed.output_kinds, vec![PreparedOutputKind::Classical]);
    for side in [&mixed.left, &mixed.right] {
        assert!(!side.terminals.is_empty());
        for terminal in &side.terminals {
            assert_eq!(terminal.outputs[0].kind, PreparedOutputKind::Classical);
        }
    }
    let quantum_config = EquivalenceConfig {
        output_pairs: vec![OutputPair {
            left: Endpoint::Quantum(q(&left, 0)),
            right: Endpoint::Quantum(q(&right, 0)),
        }],
        ..Default::default()
    };
    let quantum = prepare_comparison(&left, &right, &quantum_config).unwrap();
    assert_eq!(quantum.output_kinds, vec![PreparedOutputKind::Quantum]);
}

#[test]
fn duplicate_and_out_of_range_endpoints_are_rejected() {
    let (left, lq) = identity_program(3);
    let (right, rq) = identity_program(4);
    let input = InputPair::quantum(lq.clone(), rq.clone());
    let output = OutputPair {
        left: Endpoint::Quantum(lq.clone()),
        right: Endpoint::Quantum(rq.clone()),
    };
    let mut config = EquivalenceConfig {
        input_pairs: vec![input.clone(), input],
        output_pairs: vec![output.clone()],
        ..Default::default()
    };
    assert!(matches!(
        prepare_comparison(&left, &right, &config),
        Err(InterfaceError::DuplicateInputEndpoint { .. })
    ));
    config.input_pairs.pop();
    config.output_pairs.push(output);
    assert!(matches!(
        prepare_comparison(&left, &right, &config),
        Err(InterfaceError::DuplicateOutputEndpoint { .. })
    ));
    config.output_pairs.pop();
    config.input_pairs[0].left = Endpoint::Quantum(Qubit {
        index: 1,
        ..lq.clone()
    });
    assert!(matches!(
        prepare_comparison(&left, &right, &config),
        Err(InterfaceError::UnknownQuantumInput { .. })
    ));
    config.input_pairs[0].left = Endpoint::Quantum(lq);
    config.output_pairs[0].right = Endpoint::Quantum(Qubit { index: 1, ..rq });
    assert!(matches!(
        prepare_comparison(&left, &right, &config),
        Err(InterfaceError::UnknownOutputEndpoint { .. })
    ));
}

#[test]
fn positional_configuration_uses_declaration_order_and_checks_counts() {
    let left = parse("qubit[2] a; bit c;");
    let right = parse("qubit b; qubit d; bit e;");
    let config = EquivalenceConfig::positional(&left, &right).unwrap();
    assert_eq!(config.input_pairs.len(), 2);
    assert_eq!(config.output_pairs.len(), 3);
    assert_eq!(
        config.input_pairs[1].right,
        Endpoint::Quantum(Qubit {
            register: right.quantum_registers[1].id,
            index: 0,
        })
    );
    assert!(EquivalenceConfig::positional(&left, &parse("qubit a; bit c;")).is_none());
    assert!(EquivalenceConfig::positional(&left, &parse("qubit[2] a;")).is_none());
}

fn identity_program(register: usize) -> (Program, Qubit) {
    let mut ids = AstIdGenerator::default();
    let quantum_register = ids.node(RegisterData {
        id: SymbolId(register),
        name: "q".into(),
        width: 1,
    });
    let body = ids.node(BlockData::default());
    let program = ids.node(ProgramData {
        annotations: Default::default(),
        spec_functions: Vec::new(),
        version: OpenQasmVersion { major: 3, minor: 0 },
        numeric_inputs: Vec::new(),
        quantum_registers: vec![quantum_register],
        classical_registers: Vec::new(),
        body,
    });
    (
        program,
        Qubit {
            register: SymbolId(register),
            index: 0,
        },
    )
}

fn identity_program_with_numeric_input(
    register: usize,
    input: usize,
    ty: NumericType,
) -> (Program, Qubit) {
    let mut ids = AstIdGenerator::default();
    let numeric_input = ids.node(NumericInputData {
        id: SymbolId(input),
        name: "theta".into(),
        ty,
    });
    let quantum_register = ids.node(RegisterData {
        id: SymbolId(register),
        name: "q".into(),
        width: 1,
    });
    let body = ids.node(BlockData::default());
    let program = ids.node(ProgramData {
        annotations: Default::default(),
        spec_functions: Vec::new(),
        version: OpenQasmVersion { major: 3, minor: 0 },
        numeric_inputs: vec![numeric_input],
        quantum_registers: vec![quantum_register],
        classical_registers: Vec::new(),
        body,
    });
    (
        program,
        Qubit {
            register: SymbolId(register),
            index: 0,
        },
    )
}

fn numeric_config(left: usize, right: usize) -> EquivalenceConfig {
    EquivalenceConfig {
        numeric_input_pairs: vec![NumericInputPair {
            left: SymbolId(left),
            right: SymbolId(right),
        }],
        ..EquivalenceConfig::default()
    }
}

#[test]
fn rejects_a_classical_input_endpoint() {
    let (left, _) = identity_program(3);
    let (right, right_q) = identity_program(4);
    let config = EquivalenceConfig {
        input_pairs: vec![InputPair {
            left: Endpoint::Classical(ClassicalBit {
                register: SymbolId(9),
                index: 0,
            }),
            right: Endpoint::Quantum(right_q),
        }],
        output_pairs: Vec::new(),
        ..EquivalenceConfig::default()
    };

    assert!(matches!(
        prepare_comparison(&left, &right, &config),
        Err(InterfaceError::KindMismatchedInput { .. })
    ));
}

#[test]
fn numeric_semantics_rejection_does_not_mask_type_mismatch() {
    let (left, _) = identity_program_with_numeric_input(3, 9, NumericType::Float(Some(64)));
    let (right, _) = identity_program_with_numeric_input(4, 10, NumericType::Angle(Some(64)));

    assert!(matches!(
        prepare_comparison(&left, &right, &numeric_config(9, 10)),
        Err(InterfaceError::NumericTypeMismatch { position: 0, .. })
    ));
}

#[test]
fn numeric_semantics_rejection_does_not_mask_unpaired_input() {
    let ty = NumericType::Float(Some(64));
    let (left, _) = identity_program_with_numeric_input(3, 9, ty);
    let (right, _) = identity_program_with_numeric_input(4, 10, ty);

    assert_eq!(
        prepare_comparison(&left, &right, &EquivalenceConfig::default()),
        Err(InterfaceError::Unsupported(
            UnsupportedInterface::UnpairedNumericInput {
                side: Side::Left,
                input: SymbolId(9),
            }
        ))
    );
}

#[test]
fn rejects_sized_and_unsized_numeric_inputs() {
    for ty in [
        NumericType::Int(None),
        NumericType::Uint(None),
        NumericType::Float(None),
        NumericType::Angle(None),
        NumericType::Int(Some(8)),
        NumericType::Uint(Some(8)),
        NumericType::Float(Some(64)),
        NumericType::Angle(Some(20)),
    ] {
        let (left, _) = identity_program_with_numeric_input(3, 9, ty);
        let (right, _) = identity_program_with_numeric_input(4, 10, ty);
        assert_eq!(
            prepare_comparison(&left, &right, &numeric_config(9, 10)),
            Err(InterfaceError::Unsupported(
                UnsupportedInterface::NumericInputSemanticsUnsupported {
                    side: Side::Left,
                    input: SymbolId(9),
                    ty,
                }
            ))
        );
    }
}

fn pair_program(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; {body}"),
        "stage1.qasm",
    )
    .unwrap()
}

fn config(left: &Program, right: &Program) -> EquivalenceConfig {
    EquivalenceConfig::positional(left, right).unwrap()
}

fn rational(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

#[test]
fn malformed_interfaces_are_errors_before_any_successful_certificate() {
    let left = pair_program("h q[0]; h q[0];");
    let right = pair_program("");
    let full = config(&left, &right);
    let mut duplicate_input = full.clone();
    duplicate_input
        .input_pairs
        .push(full.input_pairs[0].clone());
    let mut duplicate_output = full.clone();
    duplicate_output
        .output_pairs
        .push(full.output_pairs[0].clone());
    let mut unknown_input = full.clone();
    unknown_input.input_pairs[0].left = Endpoint::Quantum(Qubit {
        register: SymbolId(999),
        index: 0,
    });
    let mut unknown_output = full.clone();
    unknown_output.output_pairs[0].right = Endpoint::Quantum(Qubit {
        register: SymbolId(999),
        index: 0,
    });
    let mut classical_input = full;
    classical_input.input_pairs[0].left = Endpoint::Classical(ClassicalBit {
        register: SymbolId(999),
        index: 0,
    });
    for cfg in [
        duplicate_input,
        duplicate_output,
        unknown_input,
        unknown_output,
        classical_input,
    ] {
        let error = analyze(&left, &right, &cfg).unwrap_err();
        assert!(!matches!(error, InterfaceError::Unsupported(_)));
        // Trace refusal falls through to the existing preparation rules.
        assert_eq!(error, prepare_comparison(&left, &right, &cfg).unwrap_err());
    }
}

#[test]
fn malformed_numeric_pairing_is_not_hidden_by_unsupported_semantics() {
    let left = pair_program("input float[64] theta;");
    let right = pair_program("input float[64] theta;");
    let full = config(&left, &right);
    let mut duplicate = full.clone();
    duplicate
        .numeric_input_pairs
        .push(full.numeric_input_pairs[0]);
    assert!(matches!(
        analyze(&left, &right, &duplicate),
        Err(InterfaceError::DuplicateNumericInput { .. })
    ));
    let mut unknown = full.clone();
    unknown.numeric_input_pairs[0].left = SymbolId(999);
    assert!(matches!(
        analyze(&left, &right, &unknown),
        Err(InterfaceError::UnknownNumericInput { .. })
    ));
    let mut mismatch = right;
    mismatch.numeric_inputs[0].ty = irene::ir::NumericType::Angle(Some(64));
    assert!(matches!(
        analyze(&left, &mismatch, &full),
        Err(InterfaceError::NumericTypeMismatch { .. })
    ));
}

#[test]
fn cancelling_invalid_angles_never_produces_a_certificate() {
    use irene::ir::{AstIdGenerator, NumericExprKind, StatementKind};
    let mut left = pair_program("rx(pi/2) q[0]; rx(-pi/2) q[0];");
    let mut ids = AstIdGenerator::default();
    for statement in &mut left.body.statements {
        let StatementKind::Apply { parameters, .. } = &mut statement.kind else {
            unreachable!()
        };
        let zero = ids.node(NumericExprKind::Rational(rational(0, 1)));
        parameters[0] = ids.node(NumericExprKind::Div(
            Box::new(parameters[0].clone()),
            Box::new(zero),
        ));
    }
    let right = pair_program("");
    assert!(matches!(
        analyze(&left, &right, &config(&left, &right)),
        Err(InterfaceError::Execution { .. })
    ));
}
