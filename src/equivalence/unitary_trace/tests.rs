use super::*;
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
