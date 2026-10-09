//! Whole-channel behavior, including hidden histories and coherent inputs.
use irene::{equivalence::*, frontend::openqasm3, ir::*};

fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; {body}"),
        "stage2.qasm",
    )
    .unwrap()
}
fn qubits(p: &Program) -> Vec<Qubit> {
    p.quantum_registers
        .iter()
        .flat_map(|r| {
            (0..r.width).map(|index| Qubit {
                register: r.id,
                index,
            })
        })
        .collect()
}
fn check(left: &Program, right: &Program, config: &EquivalenceConfig, equivalent: bool) {
    let before = (left.clone(), right.clone());
    let result = analyze(left, right, config).unwrap();
    if equivalent {
        assert_eq!(result.verdict, Verdict::Equivalent, "{result:?}");
    } else {
        assert_ne!(result.verdict, Verdict::Equivalent, "{result:?}");
    }
    assert_eq!((&before.0, &before.1), (left, right));
}

#[test]
fn identical_measurement_reset_and_feedback_channels_match() {
    for body in [
        "reset q[0];",
        "bit c; h q[0]; c = measure q[0];",
        "bit c; c = measure q[0]; if(c) { x q[1]; }",
    ] {
        let left = parse(body);
        let right = parse(body);
        check(
            &left,
            &right,
            &EquivalenceConfig::positional(&left, &right).unwrap(),
            true,
        );
    }
}

#[test]
fn partial_outputs_and_initialized_ancillas_can_match_without_full_trace() {
    let left = parse("h q[0]; cx q[0],q[1];");
    let right = parse("h q[0]; cx q[0],q[1];");
    let full = EquivalenceConfig::positional(&left, &right).unwrap();
    let mut partial = full.clone();
    partial.output_pairs.pop();
    let mut initialized = full;
    initialized.input_pairs.pop();
    for config in [partial, initialized] {
        check(&left, &right, &config, true);
    }
}

#[test]
fn declarations_and_explicit_pair_positions_not_local_names_determine_observables() {
    let left = parse("bit c; c = measure q[0];");
    let right = openqasm3::parse_str(
        "OPENQASM 3.0; bit flag; qubit[2] renamed; flag = measure renamed[0];",
        "renamed.qasm",
    )
    .unwrap();
    check(
        &left,
        &right,
        &EquivalenceConfig::positional(&left, &right).unwrap(),
        true,
    );
}

#[test]
fn visible_output_changes_are_not_lost_when_terminal_rows_are_extracted() {
    for (a, b) in [
        ("bit c = 0; x q[0];", "bit c = 0;"),
        ("bit c; c = measure q[0];", "bit c; c = measure q[1];"),
    ] {
        let left = parse(a);
        let right = parse(b);
        check(
            &left,
            &right,
            &EquivalenceConfig::positional(&left, &right).unwrap(),
            false,
        );
    }
}

#[test]
fn only_global_phase_is_removed_not_input_dependent_phase() {
    let identity = parse("bit c = 0;");
    let global = parse("bit c = 0; x q[0]; z q[0]; x q[0]; z q[0];");
    let relative = parse("bit c = 0; z q[0];");
    for (left, expected) in [(&global, true), (&relative, false)] {
        check(
            left,
            &identity,
            &EquivalenceConfig::positional(left, &identity).unwrap(),
            expected,
        );
    }
}

#[test]
fn hidden_measurement_dephasing_is_preserved_but_repeated_dephasing_is_idempotent() {
    let once = parse("bit c; c = measure q[0];");
    let twice = parse("bit c; c = measure q[0]; c = measure q[0];");
    let identity = parse("bit c;");
    for (right, expected) in [(&twice, true), (&identity, false)] {
        let mut config = EquivalenceConfig::positional(&once, right).unwrap();
        config
            .output_pairs
            .retain(|p| matches!(p.left, Endpoint::Quantum(_)));
        check(&once, right, &config, expected);
    }
}

#[test]
fn mixed_quantum_classical_output_is_a_z_observation() {
    let left = parse("h q[0];");
    let right = parse("bit c; h q[0]; c = measure q[0];");
    let config = EquivalenceConfig {
        input_pairs: qubits(&left)
            .into_iter()
            .zip(qubits(&right))
            .map(|(a, b)| InputPair::quantum(a, b))
            .collect(),
        output_pairs: vec![OutputPair {
            left: Endpoint::Quantum(qubits(&left)[0].clone()),
            right: Endpoint::Classical(ClassicalBit {
                register: right.classical_registers[0].id,
                index: 0,
            }),
        }],
        ..Default::default()
    };
    check(&left, &right, &config, true);
}

#[test]
fn uninitialized_observed_classical_storage_is_an_execution_error() {
    let left = parse("bit c;");
    let right = parse("bit c = 0;");
    let config = EquivalenceConfig::positional(&left, &right).unwrap();
    assert!(matches!(
        analyze(&left, &right, &config),
        Err(InterfaceError::Execution {
            side: Side::Left,
            ..
        })
    ));
}

#[test]
fn nonlinear_measurement_feedback_matches_coherent_controls() {
    // Exhaust every two-bit Boolean function in ANF. The two programs induce
    // the same quantum instrument: measure controls then use classical feedback,
    // or coherently control the target and then measure the controls.
    // This exercises nonlinear guards, weighted paths, phase and hidden history
    // without constructing private KernelTerms or prescribing a pivot order.
    for mask in 0..16 {
        let terms = ["true", "c[0]", "c[1]", "(c[0] & c[1])"];
        let gates = [
            "x q[2];",
            "cx q[0],q[2];",
            "cx q[1],q[2];",
            "ccx q[0],q[1],q[2];",
        ];
        let selected: Vec<_> = (0..4).filter(|i| mask & (1 << i) != 0).collect();
        let predicate = if selected.is_empty() {
            "false".to_owned()
        } else {
            selected
                .iter()
                .map(|&i| terms[i])
                .collect::<Vec<_>>()
                .join(" ^ ")
        };
        let controlled = selected.iter().map(|&i| gates[i]).collect::<String>();
        let source = |body: &str| {
            openqasm3::parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; bit[2] c; h q[0]; h q[1]; {body}"),
            "feedback.qasm",
        ).unwrap()
        };
        let measure = "c[0]=measure q[0]; c[1]=measure q[1];";
        let left = source(&format!("{measure} if({predicate}) x q[2]; p(pi/4) q[2];"));
        for wrong in [false, true] {
            let flip = if wrong { "x q[2];" } else { "" };
            let right = source(&format!("{controlled} {measure} p(pi/4) q[2]; {flip}"));
            let config = EquivalenceConfig::positional(&left, &right).unwrap();
            let result = analyze(&left, &right, &config).unwrap();
            assert_eq!(
                result.verdict,
                if wrong {
                    Verdict::NotEquivalent
                } else {
                    Verdict::Equivalent
                },
                "mask={mask}, wrong={wrong}: {result:?}"
            );
        }
    }
}

#[test]
fn full_input_channel_comparisons_are_symmetric_and_do_not_mutate_sources() {
    for (a, b, expected) in [
        ("h q[0]; h q[0];", "", Verdict::Equivalent),
        (
            "h q[0]; x q[0]; y q[0]; z q[0];",
            "h q[0];",
            Verdict::Equivalent,
        ),
        ("h q[0];", "", Verdict::NotEquivalent),
        ("h q[0]; cz q[0],q[1]; h q[0];", "", Verdict::NotEquivalent),
        ("h q[0]; t q[0];", "h q[0];", Verdict::NotEquivalent),
        (
            "h q[0]; cx q[0],q[1];",
            "cx q[0],q[1]; h q[0];",
            Verdict::NotEquivalent,
        ),
    ] {
        let (left, right) = (parse(a), parse(b));
        let before = (left.clone(), right.clone());
        for (a, b) in [(&left, &right), (&right, &left)] {
            let config = EquivalenceConfig::positional(a, b).unwrap();
            assert_eq!(analyze(a, b, &config).unwrap().verdict, expected);
        }
        assert_eq!(before, (left, right));
    }
}
