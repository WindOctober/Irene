use irene::{
    equivalence::{Endpoint, EquivalenceConfig, InputPair, OutputPair, Verdict, analyze},
    frontend::openqasm3,
    ir::{ClassicalBit, Program, Qubit},
};

fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
        "analysis-api.qasm",
    )
    .unwrap()
}

#[test]
fn positional_interface_preserves_declaration_order_and_all_storage() {
    let mut left = parse("qubit[2] a; qubit b; bit[2] c;");
    let right = parse("qubit[3] target; bit first; bit second;");
    // Deliberately separate declaration order from local symbol-ID order.
    left.quantum_registers.swap(0, 1);
    let interface = EquivalenceConfig::positional(&left, &right).unwrap();
    let left_wires = [
        Qubit {
            register: left.quantum_registers[0].id,
            index: 0,
        },
        Qubit {
            register: left.quantum_registers[1].id,
            index: 0,
        },
        Qubit {
            register: left.quantum_registers[1].id,
            index: 1,
        },
    ];
    assert_eq!(interface.input_pairs.len(), 3);
    assert_eq!(interface.output_pairs.len(), 5);
    for (index, wire) in left_wires.into_iter().enumerate() {
        let expected = InputPair::quantum(
            wire,
            Qubit {
                register: right.quantum_registers[0].id,
                index,
            },
        );
        assert_eq!(interface.input_pairs[index], expected);
        assert_eq!(interface.output_pairs[index].left, expected.left);
        assert_eq!(interface.output_pairs[index].right, expected.right);
    }
    for index in 0..2 {
        assert_eq!(
            interface.output_pairs[3 + index],
            OutputPair {
                left: Endpoint::Classical(ClassicalBit {
                    register: left.classical_registers[0].id,
                    index,
                }),
                right: Endpoint::Classical(ClassicalBit {
                    register: right.classical_registers[index].id,
                    index: 0,
                }),
            }
        );
    }
}

#[test]
fn positional_interface_rejects_incompatible_shapes_and_numeric_types() {
    for (a, b) in [
        ("qubit a;", "qubit[2] b;"),
        ("qubit a; bit c;", "qubit b;"),
        ("input float theta; qubit a;", "qubit b;"),
        ("input float theta; qubit a;", "input angle phi; qubit b;"),
    ] {
        assert!(EquivalenceConfig::positional(&parse(a), &parse(b)).is_none());
    }
    let left = parse("input float theta; qubit a;");
    let right = parse("input float phi; qubit b;");
    let interface = EquivalenceConfig::positional(&left, &right).unwrap();
    assert_eq!(interface.numeric_input_pairs.len(), 1);
    assert_eq!(
        analyze(&left, &right, &interface).unwrap().verdict,
        Verdict::Unknown
    );
}

#[test]
fn explicit_interface_supports_different_shapes_and_full_analysis() {
    let left = parse("qubit[2] a;");
    let right = parse("qubit b;");
    assert!(EquivalenceConfig::positional(&left, &right).is_none());
    let pair = InputPair::quantum(
        Qubit {
            register: left.quantum_registers[0].id,
            index: 0,
        },
        Qubit {
            register: right.quantum_registers[0].id,
            index: 0,
        },
    );
    let interface = EquivalenceConfig {
        output_pairs: vec![OutputPair {
            left: pair.left.clone(),
            right: pair.right.clone(),
        }],
        input_pairs: vec![pair],
        ..EquivalenceConfig::default()
    };
    let result = analyze(&left, &right, &interface).unwrap();
    assert_eq!(result.verdict, Verdict::Equivalent);
    assert!(result.counterexample.is_none());
    assert!(result.density_counterexample.is_none());
}

#[test]
fn unitary_preprocessing_does_not_turn_a_reset_channel_into_a_unitary_miter() {
    let identity = parse("qubit q; h q; h q;");
    let reset = parse("qubit q; reset q;");
    for (left, right) in [(&identity, &reset), (&reset, &identity)] {
        let interface = EquivalenceConfig::positional(left, right).unwrap();
        let result = analyze(left, right, &interface).unwrap();
        assert_eq!(result.verdict, Verdict::NotEquivalent);
    }
    // With no symbolic input, both programs do prepare |0>. The optimizer
    // must leave input/initialization semantics to the supplied interface.
    let mut interface = EquivalenceConfig::positional(&identity, &reset).unwrap();
    interface.input_pairs.clear();
    assert_eq!(
        analyze(&identity, &reset, &interface).unwrap().verdict,
        Verdict::Equivalent
    );
}

#[test]
fn specification_metadata_neither_blocks_equivalence_nor_supplies_assumptions() {
    for (operation, comparison, expected) in [
        ("h q;", "h q;", Verdict::Equivalent),
        ("h q;", "x q;", Verdict::NotEquivalent),
        ("reset q;", "reset q;", Verdict::Equivalent),
        ("reset q;", "h q; h q;", Verdict::NotEquivalent),
    ] {
        let annotated = parse(&format!(
            "qubit q;\n\
             pragma saria.def never(n: int) -> bool = n < n\n\
             @saria.requires never(0)\n\
             @saria.ensures false\n{operation}"
        ));
        let original = annotated.clone();
        let plain = parse(&format!("qubit q; {operation}"));
        let other = parse(&format!("qubit q; {comparison}"));
        for candidate in [&plain, &annotated] {
            for (left, right) in [(candidate, &other), (&other, candidate)] {
                let interface = EquivalenceConfig::positional(left, right).unwrap();
                assert_eq!(analyze(left, right, &interface).unwrap().verdict, expected);
            }
        }
        assert_eq!(annotated, original);
        if operation == "h q;" {
            irene::equivalence::unitary_miter::validate(&annotated).unwrap();
            let (circuit, identity) =
                irene::equivalence::unitary_miter::miter(&annotated, &plain).unwrap();
            for generated in [circuit, identity] {
                assert!(generated.annotations.is_empty());
                assert!(generated.spec_functions.is_empty());
            }
        } else {
            // Metadata must not relax the existing gate-only admission rules.
            assert!(irene::equivalence::unitary_miter::validate(&annotated).is_err());
            assert!(irene::equivalence::unitary_miter::miter(&annotated, &plain).is_err());
        }
    }
}
