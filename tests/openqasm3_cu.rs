use irene::frontend::openqasm3;
use irene::ir::{Block, Gate, NumericExpr, Qubit, StatementKind};
use irene::symbolic::PhaseCoefficient;
use num_rational::BigRational;

fn applies<'a>(b: &'a Block, result: &mut Vec<(Gate, &'a [NumericExpr], &'a [Qubit])>) {
    for s in &b.statements {
        match &s.kind {
            StatementKind::Scope(body) => applies(body, result),
            StatementKind::Apply {
                gate,
                parameters,
                qubits,
            } => result.push((*gate, parameters, qubits)),
            _ => panic!("expected only gates"),
        }
    }
}

#[test]
fn broadcast_preserves_exact_angles_and_wire_identity() {
    for control in ["a", "a[0]"] {
        let p = openqasm3::parse_str(
            &format!(
                "OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] a; qubit[2] b;
                cu(pi/2,pi/4,pi/8,pi/16) {control},b;"
            ),
            "broadcast",
        )
        .unwrap();
        let mut gates = Vec::new();
        applies(&p.body, &mut gates);
        assert_eq!(gates.len(), 8);
        for (index, group) in gates.chunks_exact(4).enumerate() {
            let c = Qubit {
                register: p.quantum_registers[0].id,
                index: if control == "a" { index } else { 0 },
            };
            let t = Qubit {
                register: p.quantum_registers[1].id,
                index,
            };
            for ((gate, parameters, qubits), (expected_gate, denominator)) in group.iter().zip([
                (Gate::P, 8),
                (Gate::Crz, 16),
                (Gate::Cry, 4),
                (Gate::Crz, 8),
            ]) {
                assert_eq!(*gate, expected_gate);
                assert_eq!(parameters.len(), 1);
                let expected_qubits = if *gate == Gate::P {
                    vec![c.clone()]
                } else {
                    vec![c.clone(), t.clone()]
                };
                assert_eq!(*qubits, expected_qubits);
                assert_eq!(
                    PhaseCoefficient::angle(
                        parameters[0].clone(),
                        BigRational::from_integer(1.into())
                    ),
                    PhaseCoefficient::rational(BigRational::new(1.into(), denominator.into())),
                );
            }
        }
        let mut ids = Vec::new();
        p.visit_ast_ids(|id| ids.push(id.index()));
        ids.sort_unstable();
        assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
    }
}

#[test]
fn invalid_calls_and_unsupported_modifiers_are_rejected() {
    for body in [
        "cu(1,2,3) q[0],q[1];",
        "cu(1,2,3,4,5) q[0],q[1];",
        "cu(1,2,3,4) q[0];",
        "cu(1,2,3,4) q[0],q[1],q[2];",
        "cu(1,2,3,4) q[0],q[0];",
        "cu(1,2,3,4) q[0],q[3];",
        "cu(1,2,3,4) q[0],missing;",
        "cu(1,2,3,4) q[0],c;",
        "cu(1,2,3,4) q,r;",
        "inv @ cu(1,2,3,4) q[0],q[1];",
        "pow(2) @ cu(1,2,3,4) q[0],q[1];",
        "ctrl @ cu(1,2,3,4) q[0],q[1],q[2];",
    ] {
        let source = format!(
            "OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; qubit[2] r; bit c; {body}"
        );
        assert!(
            openqasm3::parse_str(&source, "invalid-cu").is_err(),
            "{body}"
        );
    }
    assert!(
        openqasm3::parse_str(
            "OPENQASM 3.0; qubit[2] q; cu(1,2,3,4) q[0],q[1];",
            "missing-include"
        )
        .is_err()
    );
}
