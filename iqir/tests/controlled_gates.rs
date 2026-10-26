use iqir::{StatementKind, frontend};

#[test]
fn general_controls_sx_and_broadcasts_lower_with_unique_ids() {
    for instruction in [
        "ctrl(3) @ x q[0],q[1],q[2],q[3];",
        "ctrl @ ctrl @ ctrl @ x q[0],q[1],q[2],q[3];",
        "ctrl(2) @ ry(pi/3) q[0],q[1],q[2];",
        "ctrl(2) @ p(pi/3) q[0],q[1],q[2];",
        "ctrl(2) @ h q[0],q[1],q[2];",
        "negctrl @ x q[0],q[1];",
        "ctrl @ negctrl @ x q[0],q[1],q[2];",
        "negctrl(2) @ x q[0],q[1],q[2];",
        "inv @ negctrl @ sx q[0],q[1];",
        "pow(2) @ sx q[0];",
        "sx q;",
        "qubit[4] targets; negctrl @ sx q,targets;",
        "gate custom a {h a; s a;} negctrl @ inv @ custom q[0],q[1];",
    ] {
        let program = frontend::parse_str(
            &format!("OPENQASM 3; include \"stdgates.inc\"; qubit[4] q; {instruction}"),
            "controls.qasm",
        )
        .unwrap();
        let mut ids = Vec::new();
        program.visit_ast_ids(|id| ids.push(id.index()));
        let count = ids.len();
        ids.sort();
        ids.dedup();
        assert_eq!(count, ids.len(), "duplicate IDs: {instruction}");
        assert!(ids.iter().all(|i| *i < program.ast_id_bound()));
    }
}

#[test]
fn multi_control_is_a_structured_unitary_not_a_classical_if() {
    let program = frontend::parse_str(
        "OPENQASM 3; include \"stdgates.inc\"; qubit[4] q; ctrl(3) @ x q[0],q[1],q[2],q[3];",
        "controls.qasm",
    )
    .unwrap();
    let StatementKind::Unitary {
        controls,
        power,
        body,
    } = &program.body.statements[0].kind
    else {
        panic!("expected a unitary");
    };
    assert_eq!(controls.len(), 3);
    assert_eq!(*power, 1);
    assert!(matches!(
        body.statements[0].kind,
        StatementKind::Apply {
            gate: iqir::Gate::X,
            ..
        }
    ));
}
