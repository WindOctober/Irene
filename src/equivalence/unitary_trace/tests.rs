use super::super::unitary_rewrite::tests::matrix;
use super::*;

#[test]
fn rotation_lowering_preserves_full_matrices_and_unique_ids() {
    for gate in ["rx", "ry", "crx", "cry"] {
        for angle in ["0", "pi/4", "-pi/2", "2*pi"] {
            let operands = if gate.starts_with('c') {
                "q[0],q[1]"
            } else {
                "q[1]"
            };
            let original = parse(2, &format!("{gate}({angle}) {operands};"));
            let lowered = phase_only_rotations(original.clone()).unwrap();
            assert_eq!(matrix(&original), matrix(&lowered));
            let mut ids = std::collections::BTreeSet::new();
            lowered.visit_ast_ids(|id| assert!(ids.insert(id)));
            assert!(lowered.body.statements.iter().all(|s| !matches!(
                s.kind,
                StatementKind::Apply {
                    gate: Gate::Rx | Gate::Ry | Gate::Crx | Gate::Cry,
                    ..
                }
            )));
        }
    }
}

#[test]
fn rotation_decompositions_get_exact_trace_certificates() {
    for (gate, sequence, operands) in [
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
            let a = parse(2, &format!("{gate}({angle}) {operands};"));
            let b = parse(2, &sequence.replace("ANGLE", angle));
            for (l, r) in [(&a, &b), (&b, &a)] {
                assert!(
                    certificate(l, r, &config(l, r)).unwrap().is_one(),
                    "{gate} {angle}"
                );
            }
        }
    }
}

#[test]
fn controlled_two_pi_rotations_are_not_identity_channels() {
    let identity = parse(2, "");
    for gate in ["crx", "cry"] {
        let rotation = parse(2, &format!("{gate}(2*pi) q[0],q[1];"));
        assert_eq!(
            certificate(&rotation, &identity, &config(&rotation, &identity)),
            Some(TraceNorm::Rational(BigRational::from_integer(0.into())))
        );
    }
}

#[test]
fn lowering_checks_the_whole_dyadic_domain_only_when_needed() {
    for body in [
        "rx(pi/3) q[0];",
        "ry(0.1) q[0];",
        "rx(pi/4096) q[0];",
        "rx(pi/2) q[0]; rz(0.1) q[1];",
    ] {
        assert!(phase_only_rotations(parse(2, body)).is_none(), "{body}");
    }
    let untouched = parse(2, "h q[0]; rz(pi/3) q[1];");
    assert!(phase_only_rotations(parse(2, "rx(pi/2048) q[0];")).is_some());
    assert_eq!(phase_only_rotations(untouched.clone()), Some(untouched));
}
use crate::frontend::openqasm3;
use crate::ir::{AstIdGenerator, ClassicalBit, NumericExprKind, SymbolId};

fn parse(width: usize, body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[{width}] q; {body}"),
        "trace-certificate.qasm",
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
        ..Default::default()
    }
}

#[test]
fn closed_traces_certify_identity_zero_and_fractional_norms() {
    for (left, right, numerator, denominator) in [
        ("h q[0]; h q[0];", "", 1, 1),
        ("h q[0];", "", 0, 1),
        ("h q[0]; z q[0];", "h q[0];", 0, 1),
        ("h q[0]; cz q[0],q[1]; h q[0];", "", 1, 4),
        ("h q[0]; x q[0]; z q[0]; x q[0]; z q[0];", "h q[0];", 1, 1),
    ] {
        let l = parse(2, left);
        let r = parse(2, right);
        for (a, b) in [(&l, &r), (&r, &l)] {
            let result = certificate(a, b, &config(a, b)).expect(left);
            assert_eq!(
                result,
                TraceNorm::Rational(BigRational::new(numerator.into(), denominator.into())),
                "{left} / {right}"
            );
            assert_eq!(result.is_one(), numerator == denominator);
        }
    }
}

#[test]
fn full_interface_and_positional_pairing_are_required() {
    let l = parse(2, "h q[0]; h q[0];");
    let r = parse(2, "");
    let base = config(&l, &r);
    for case in 0..5 {
        let mut cfg = base.clone();
        match case {
            0 => {
                cfg.input_pairs.pop();
            }
            1 => {
                cfg.output_pairs.pop();
            }
            2 => {
                let endpoint = cfg.output_pairs[0].right.clone();
                cfg.output_pairs[0].right = cfg.output_pairs[1].right.clone();
                cfg.output_pairs[1].right = endpoint;
            }
            3 => {
                cfg.input_pairs.push(cfg.input_pairs[0].clone());
            }
            4 => {
                cfg.output_pairs[0].right = Endpoint::Classical(ClassicalBit {
                    register: SymbolId(99),
                    index: 0,
                });
            }
            _ => unreachable!(),
        }
        assert!(certificate(&l, &r, &cfg).is_none(), "case {case}");
    }
    let wider = parse(3, "");
    assert!(certificate(&l, &wider, &config(&l, &wider)).is_none());
}

#[test]
fn both_sides_must_be_unitary() {
    let good = parse(2, "h q[0]; h q[0];");
    for body in [
        "reset q[0];",
        "bit c; c=measure q[0];",
        "bit c=0; if(c) x q[0];",
    ] {
        let bad = parse(2, body);
        assert!(certificate(&good, &bad, &config(&good, &bad)).is_none());
        assert!(certificate(&bad, &good, &config(&bad, &good)).is_none());
    }
}

#[test]
fn invalid_numeric_domains_are_checked_before_gate_cancellation() {
    let mut bad = parse(2, "rx(pi) q[0]; rx(-pi) q[0];");
    let mut ids = AstIdGenerator::starting_at(bad.ast_id_bound());
    let one = ids.node(NumericExprKind::Rational(BigRational::from_integer(
        1.into(),
    )));
    let zero = ids.node(NumericExprKind::Rational(BigRational::from_integer(
        0.into(),
    )));
    let angle = ids.node(NumericExprKind::Div(Box::new(one), Box::new(zero)));
    let copy = ids.clone_numeric_expr(&angle);
    let opposite = ids.node(NumericExprKind::Neg(Box::new(copy)));
    for (s, a) in bad.body.statements.iter_mut().zip([angle, opposite]) {
        if let StatementKind::Apply { parameters, .. } = &mut s.kind {
            parameters[0] = a;
        }
    }
    let good = parse(2, "");
    assert!(certificate(&bad, &good, &config(&bad, &good)).is_none());
}

#[test]
fn unresolved_sums_and_unsupported_rotations_are_not_certificates() {
    let right = parse(2, "");
    for body in ["h q[0]; p(pi/8) q[0]; h q[0];", "rx(pi/3) q[0];"] {
        let left = parse(2, body);
        assert!(
            certificate(&left, &right, &config(&left, &right)).is_none(),
            "{body}"
        );
    }
}
