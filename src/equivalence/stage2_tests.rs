use super::*;
use crate::frontend::openqasm3;
use crate::symbolic::{
    BooleanPolynomial, Component, HybridMemory, PhaseCoefficient, PhasePolynomial, Scalar, Variable,
};

fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; {body}"),
        "stage2.qasm",
    )
    .unwrap()
}

fn check(left: &Program, right: &Program, config: &EquivalenceConfig, equivalent: bool) {
    assert!(
        unitary_trace::certificate(left, right, config).is_none(),
        "must exercise Stage 2"
    );
    let result = analyze(left, right, config).unwrap();
    if !equivalent {
        // This test checks refusal of the structural rule, not later rules.
        let prepared = prepare_comparison(left, right, config).unwrap();
        assert!(!exact_hps_certificate(&prepared));
        assert!(matches!(
            result.evidence,
            Evidence::KernelAggregationRequired | Evidence::OutputSupportMismatch
        ));
        assert_ne!(result.verdict, Verdict::Equivalent);
        return;
    }
    assert_eq!(
        result.verdict,
        if equivalent {
            Verdict::Equivalent
        } else {
            Verdict::Unknown
        }
    );
    assert_eq!(
        result.evidence,
        if equivalent {
            Evidence::ExactHps
        } else {
            Evidence::KernelAggregationRequired
        }
    );
}

#[test]
fn identical_measurement_and_reset_channels_get_structural_certificates() {
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

fn y(index: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(index))
}

fn synthetic_side(a: usize, b: usize) -> PreparedSide {
    let mut phase = PhasePolynomial::zero();
    phase.add_boolean(
        &y(a),
        PhaseCoefficient::rational(BigRational::new(1.into(), 8.into())),
    );
    PreparedSide {
        hps: HybridPathSum {
            input: HybridMemory::default(),
            components: vec![Component {
                guard: vec![y(b)],
                path_support: [a, b].into(),
                scalar: Scalar::Select {
                    condition: y(a),
                    when_true: Box::new(Scalar::one()),
                    when_false: Box::new(Scalar::zero()),
                },
                phase,
                output: HybridMemory {
                    history: vec![HistoryEntry::Discard { value: y(b) }],
                    ..Default::default()
                },
            }],
        },
        terminals: vec![PreparedTerminal {
            outputs: vec![PreparedOutput {
                kind: PreparedOutputKind::Quantum,
                value: y(a).xor(&y(b)),
            }],
        }],
        quantum_input_positions: Default::default(),
    }
}

#[test]
fn one_path_bijection_must_align_scalar_guard_phase_history_and_outputs() {
    let mut prepared = PreparedComparison {
        left: synthetic_side(3, 8),
        right: synthetic_side(90, 11),
        output_kinds: vec![PreparedOutputKind::Quantum],
    };
    assert!(exact_hps_certificate(&prepared));
    prepared.right.hps.components[0].phase = PhasePolynomial::zero();
    prepared.right.hps.components[0].phase.add_boolean(
        &y(11),
        PhaseCoefficient::rational(BigRational::new(1.into(), 8.into())),
    );
    assert!(
        !exact_hps_certificate(&prepared),
        "cannot rename each field independently"
    );
}

#[test]
fn multi_component_and_unbound_paths_cannot_use_this_rule() {
    let mut prepared = PreparedComparison {
        left: synthetic_side(3, 8),
        right: synthetic_side(90, 11),
        output_kinds: vec![PreparedOutputKind::Quantum],
    };
    for side in [&mut prepared.left, &mut prepared.right] {
        side.hps.components.push(side.hps.components[0].clone());
        side.terminals.push(side.terminals[0].clone());
    }
    // Even identical sums are outside this rule: per-summand phase/history
    // normalization has not been justified for their cross terms.
    assert!(!exact_hps_certificate(&prepared));
    prepared.left = synthetic_side(3, 8);
    prepared.right = synthetic_side(90, 11);
    prepared.right.hps.components[0].path_support.remove(&90);
    assert!(
        !exact_hps_certificate(&prepared),
        "unbound paths cannot be a certificate"
    );
}
