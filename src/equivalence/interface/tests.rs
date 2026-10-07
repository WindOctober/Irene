use crate::ir::{
    AstIdGenerator, BlockData, NumericInputData, OpenQasmVersion, ProgramData, RegisterData,
};

use super::*;

fn parse(body: &str) -> Program {
    crate::frontend::openqasm3::parse_str(
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
        .evaluate::<std::convert::Infallible>(|v| match v {
            Variable::Input(q) => Ok(input & (1 << q.index) != 0),
            Variable::Path(_) => panic!("deterministic fixture has no path variables"),
        })
        .unwrap()
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

#[test]
fn input_renaming_reaches_every_field_without_capturing_paths() {
    use crate::symbolic::{
        Component, HistoryEntry, HybridMemory, PhaseCoefficient, PhasePolynomial, Scalar,
    };
    use num_rational::BigRational;
    let source = Qubit {
        register: SymbolId(7),
        index: 2,
    };
    let x = BooleanPolynomial::variable(Variable::Input(source.clone()));
    let y = BooleanPolynomial::variable(Variable::Path(0));
    let bit = ClassicalBit {
        register: SymbolId(8),
        index: 0,
    };
    let expr = x.xor(&y);
    let mut phase = PhasePolynomial::zero();
    phase.add_boolean(
        &expr,
        PhaseCoefficient::rational(BigRational::new(1.into(), 8.into())),
    );
    let mut hps = HybridPathSum {
        input: HybridMemory {
            quantum: [(source.clone(), x)].into(),
            ..Default::default()
        },
        components: vec![Component {
            guard: vec![expr.clone()],
            scalar: Scalar::select(
                expr.clone(),
                Scalar::one(),
                Scalar::rational(BigRational::from_integer(2.into())),
            ),
            phase,
            path_support: [0].into(),
            output: HybridMemory {
                quantum: [(source.clone(), expr.clone())].into(),
                classical: [(bit.clone(), expr.clone())].into(),
                history: vec![
                    HistoryEntry::Write {
                        target: bit,
                        value: expr.clone(),
                    },
                    HistoryEntry::Discard { value: expr },
                ],
            },
        }],
    };
    let mut expected = hps.components[0].clone();
    let old = Variable::Input(source.clone());
    let new = BooleanPolynomial::variable(Variable::Input(Qubit {
        register: SymbolId(9),
        index: 0,
    }));
    expected.guard = expected
        .guard
        .iter()
        .map(|g| g.substitute(&old, &new))
        .collect();
    expected.scalar = expected.scalar.substitute(&old, &new);
    expected.phase.substitute(&old, &new);
    for v in expected
        .output
        .quantum
        .values_mut()
        .chain(expected.output.classical.values_mut())
    {
        *v = v.substitute(&old, &new);
    }
    for entry in &mut expected.output.history {
        *entry.value_mut() = entry.value().substitute(&old, &new);
    }
    canonicalize_boolean_inputs(&mut hps, &[source], SymbolId(9));
    let actual = &hps.components[0];
    assert_eq!(actual.guard, expected.guard);
    assert_eq!(actual.scalar, expected.scalar);
    assert_eq!(actual.phase, expected.phase);
    assert_eq!(actual.output.quantum, expected.output.quantum);
    assert_eq!(actual.output.classical, expected.output.classical);
    assert_eq!(actual.path_support, expected.path_support);
    for (a, b) in actual.output.history.iter().zip(&expected.output.history) {
        assert_eq!(a.value(), b.value());
    }
}

#[test]
fn canonical_namespace_exhaustion_is_unsupported() {
    let (left, _) = identity_program(usize::MAX);
    let (right, _) = identity_program(0);
    assert!(matches!(
        prepare_comparison(&left, &right, &EquivalenceConfig::default()),
        Err(InterfaceError::Unsupported(
            UnsupportedInterface::CanonicalSymbolSpaceExhausted
        ))
    ));
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
fn rejects_sized_float_before_symbolic_normalization() {
    let ty = NumericType::Float(Some(64));
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

#[test]
fn rejects_sized_angle_before_symbolic_normalization() {
    let ty = NumericType::Angle(Some(20));
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
