use super::*;
use crate::frontend::openqasm3;
fn proves(left: &Program, right: &Program, config: &EquivalenceConfig) -> bool {
    certificate(left, right, config).is_some_and(|n| n.is_one())
}
fn parse(gates: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; {gates}"),
        "trace-test",
    )
    .unwrap()
}
fn config(left: &Program, right: &Program) -> EquivalenceConfig {
    let l = super::super::qubits(left);
    let r = super::super::qubits(right);
    EquivalenceConfig {
        input_pairs: l
            .iter()
            .cloned()
            .zip(r.iter().cloned())
            .map(|(l, r)| InputPair::quantum(l, r))
            .collect(),
        output_pairs: l
            .into_iter()
            .zip(r)
            .map(|(l, r)| OutputPair {
                left: Endpoint::Quantum(l),
                right: Endpoint::Quantum(r),
            })
            .collect(),
        numeric_input_pairs: vec![],
    }
}
#[test]
fn exact_trace_preserves_vacuous_inputs_and_constant_global_phases() {
    for (a, b) in [
        ("h q[0];", "h q[0];"),
        ("h q[0]; x q[0]; z q[0]; x q[0]; z q[0];", "h q[0];"),
        ("h q[0]; x q[0]; y q[0]; z q[0];", "h q[0];"),
        (
            "h q[0]; cx q[0],q[1]; t q[1];",
            "h q[0]; cx q[0],q[1]; t q[1];",
        ),
    ] {
        let (a, b) = (parse(a), parse(b));
        assert!(proves(&a, &b, &config(&a, &b)));
        assert!(proves(&b, &a, &config(&b, &a)));
    }
}
#[test]
fn trace_rejects_input_dependent_phase_and_noncommuting_order() {
    for (a, b) in [
        ("h q[0]; x q[0];", "h q[0];"),
        ("h q[0]; z q[0];", "h q[0];"),
        ("h q[0]; t q[0];", "h q[0];"),
        ("h q[0]; cx q[0],q[1];", "cx q[0],q[1]; h q[0];"),
    ] {
        let (a, b) = (parse(a), parse(b));
        assert!(!proves(&a, &b, &config(&a, &b)));
    }
}
#[test]
fn trace_refuses_incomplete_duplicate_permuted_and_classical_interfaces() {
    let a = parse("h q[0]; bit c=0;");
    let full = config(&a, &a);
    assert!(proves(&a, &a, &full));
    let mut c = full.clone();
    c.input_pairs.pop();
    assert!(!proves(&a, &a, &c));
    let mut c = full.clone();
    c.output_pairs.pop();
    assert!(!proves(&a, &a, &c));
    let mut c = full.clone();
    c.output_pairs[0].right = c.output_pairs[1].right.clone();
    assert!(!proves(&a, &a, &c));
    let mut c = full.clone();
    c.output_pairs.swap(0, 1);
    assert!(!proves(&a, &a, &c));
    let c = EquivalenceConfig::positional(&a, &a).unwrap();
    assert!(!proves(&a, &a, &c));
}
#[test]
fn unsupported_or_unequal_circuits_are_not_proved_equivalent() {
    let a = parse("h q[0];");
    for body in [
        "h q[0]; reset q[0];",
        "h q[0]; bit c; c=measure q[0];",
        "h q[0]; bit c=0; if(c) x q[0];",
        "h q[0]; rx(0.1) q[0];",
        "h q[0]; rx(pi/3) q[0];",
        "h q[0]; rx(pi/2) q[0]; rz(0.1) q[0];",
    ] {
        let b = parse(body);
        assert!(!proves(&a, &b, &config(&a, &b)));
        assert!(!proves(&b, &a, &config(&b, &a)));
    }
}

#[test]
fn phase_lowering_is_local_and_preserves_unsupported_angles() {
    let source = parse(
        "rz(0.5709439576515822) q[0]; rx(pi/2) q[0]; ry(pi/4) q[1]; rx(1.5707963267948966) q[0]; ry(pi/3) q[1]; crx(pi/8192) q[0],q[1];",
    );
    let lowered = phase_only_rotations(source).unwrap();
    let expected = parse(
        "rz(0.5709439576515822) q[0]; h q[0]; rz(pi/2) q[0]; h q[0]; sdg q[1]; h q[1]; rz(pi/4) q[1]; h q[1]; s q[1]; rx(1.5707963267948966) q[0]; ry(pi/3) q[1]; crx(pi/8192) q[0],q[1];",
    );
    assert_eq!(lowered, expected);
    let mut ids = std::collections::BTreeSet::new();
    lowered.visit_ast_ids(|id| assert!(ids.insert(id)));
    // Local success does not imply that trace can handle the residual Rx.
    let identity = parse("");
    assert_eq!(
        certificate(&lowered, &identity, &config(&lowered, &identity)),
        None
    );
}

#[test]
fn mixed_angle_trace_succeeds_when_residual_phases_cancel_exactly() {
    // The decimal Rz gates are separated in the miter, so adjacent
    // preprocessing cannot remove them before local Rx lowering.
    let a = parse("rx(pi/2) q[0]; rz(0.5709439576515822) q[1];");
    let b = parse("rz(0.5709439576515822) q[1]; h q[0]; rz(pi/2) q[0]; h q[0];");
    assert!(proves(&a, &b, &config(&a, &b)));
    assert!(proves(&b, &a, &config(&b, &a)));
}

#[test]
fn mixed_angles_keep_local_reductions_on_the_general_channel_route() {
    let a =
        parse("rx(0.123) q[0]; h q[0]; rx(pi/2) q[0]; h q[0]; rz(0.5709439576515822) q[0];");
    let b = parse("rx(0.123) q[0]; rz(pi/2) q[0]; rz(0.5709439576515822) q[0];");
    let mut c = config(&a, &b);
    // Observe only one wire: force fallback instead of a unitary trace proof.
    c.input_pairs.pop();
    c.output_pairs.pop();
    assert_eq!(certificate(&a, &b, &c), None);
    assert_eq!(
        super::super::analyze(&a, &b, &c).unwrap().verdict,
        super::super::Verdict::Equivalent
    );
}

#[test]
fn trace_basis_conjugation_preserves_controlled_phase_and_ast_identity() {
    for (gate, decomposition, operands) in [
        ("rx", "h q[1]; rz(ANGLE) q[1]; h q[1];", "q[1]"),
        (
            "ry",
            "sdg q[1]; h q[1]; rz(ANGLE) q[1]; h q[1]; s q[1];",
            "q[1]",
        ),
        ("crx", "h q[1]; crz(ANGLE) q[0],q[1]; h q[1];", "q[0],q[1]"),
        (
            "cry",
            "sdg q[1]; h q[1]; crz(ANGLE) q[0],q[1]; h q[1]; s q[1];",
            "q[0],q[1]",
        ),
    ] {
        for angle in ["pi/4", "-pi/2", "2*pi"] {
            let a = parse(&format!("{gate}({angle}) {operands};"));
            let b = parse(&decomposition.replace("ANGLE", angle));
            assert!(proves(&a, &b, &config(&a, &b)), "{gate} {angle}");
            let (m, _) = unitary_miter::miter(&a, &b).unwrap();
            let lowered = phase_only_rotations(m).unwrap();
            let mut seen = std::collections::BTreeSet::new();
            lowered.visit_ast_ids(|id| assert!(seen.insert(id)));
        }
    }
    let identity = parse("");
    for gate in ["crx", "cry"] {
        let a = parse(&format!("{gate}(2*pi) q[0],q[1];"));
        assert_eq!(
            certificate(&a, &identity, &config(&a, &identity)),
            Some(TraceNorm::Rational(BigRational::from_integer(0.into())))
        );
    }
}
#[test]
fn exact_zero_trace_certifies_inequality_but_refusal_does_not() {
    let a = parse("h q[0];");
    for body in ["h q[0]; x q[0];", "h q[0]; z q[0];"] {
        let b = parse(body);
        assert_eq!(
            certificate(&a, &b, &config(&a, &b)),
            Some(TraceNorm::Rational(BigRational::from_integer(0.into())))
        );
    }
    let b = parse("h q[0]; t q[0];");
    // (2+sqrt(2))/4 is irrational but exactly unequal to one in the
    // cyclotomic power basis. It is not rounded to a rational witness.
    assert!(matches!(
        certificate(&a, &b, &config(&a, &b)),
        Some(TraceNorm::Cyclotomic(_))
    ));
}

#[test]
fn rotation_lowering_agrees_with_the_independent_general_channel_executor() {
    for gate in ["rx", "ry", "crx", "cry"] {
        for angle in ["pi/4", "-pi/2", "2*pi"] {
            let operands = if gate.starts_with('c') {
                "q[0],q[1]"
            } else {
                "q[1]"
            };
            let a = openqasm3::parse_str(
                &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {gate}({angle}) {operands};"),
                "rotation-channel-test",
            ).unwrap();
            let mut identity = a.clone();
            identity.body.statements.clear();
            let (m, _) = unitary_miter::miter(&a, &identity).unwrap();
            let b = phase_only_rotations(m).unwrap();
            let mut c = config(&a, &b);
            // Unused initialized spectator: same visible two-qubit channel,
            // but the full-unitary certificate must refuse this interface.
            c.input_pairs.pop();
            c.output_pairs.pop();
            assert_eq!(certificate(&a, &b, &c), None);
            let result = super::super::analyze(&a, &b, &c).unwrap();
            assert_eq!(
                result.verdict,
                super::super::Verdict::Equivalent,
                "{gate} {angle}: {:?}",
                result.evidence
            );
        }
    }
}
