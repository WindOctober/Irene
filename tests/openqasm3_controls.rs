use irene::frontend::openqasm3::parse_str;
use irene::ir::{Gate, StatementKind};

#[test]
fn positive_control_modifiers_preserve_gate_parameters_and_operand_order() {
    for (name, params, expected) in [
        ("x", "", Gate::Cx),
        ("y", "", Gate::Cy),
        ("z", "", Gate::Cz),
        ("p", "(pi/7)", Gate::Cp),
        ("rx", "(pi/7)", Gate::Crx),
        ("ry", "(pi/7)", Gate::Cry),
        ("rz", "(pi/7)", Gate::Crz),
        ("cx", "", Gate::Ccx),
    ] {
        for modifier in ["ctrl", "ctrl(1)"] {
            let operands = if name == "cx" {
                "q[2],q[0],q[1]"
            } else {
                "q[2],q[0]"
            };
            let program = parse_str(&format!(
                "OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {modifier} @ {name}{params} {operands};"
            ), "controlled-gates.qasm").unwrap();
            let StatementKind::Apply {
                gate,
                parameters,
                qubits,
            } = &program.body.statements[0].kind
            else {
                panic!("expected a controlled IR gate");
            };
            assert_eq!(*gate, expected);
            assert_eq!(parameters.len(), usize::from(!params.is_empty()));
            assert_eq!(
                qubits.iter().map(|q| q.index).collect::<Vec<_>>(),
                if name == "cx" {
                    vec![2, 0, 1]
                } else {
                    vec![2, 0]
                }
            );
            let mut ids = Vec::new();
            program.visit_ast_ids(|id| ids.push(id.index()));
            ids.sort();
            assert_eq!(ids, (0..program.ast_id_bound()).collect::<Vec<_>>());
        }
    }
    for modifier in ["ctrl(2)", "ctrl @ ctrl", "ctrl(0x2)"] {
        let program = parse_str(
            &format!(
                "OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {modifier} @ x q[1],q[2],q[0];"
            ),
            "double-control.qasm",
        )
        .unwrap();
        assert!(matches!(
            program.body.statements[0].kind,
            StatementKind::Apply {
                gate: Gate::Ccx,
                ..
            }
        ));
    }
    let broadcast = parse_str(
        "OPENQASM 3.0; include \"stdgates.inc\"; qubit c; qubit[2] q; ctrl @ ry(pi/7) c,q;",
        "controlled-broadcast.qasm",
    )
    .unwrap();
    let StatementKind::Scope(body) = &broadcast.body.statements[0].kind else {
        panic!("expected a broadcast sequence");
    };
    assert_eq!(body.statements.len(), 2);
    for (index, statement) in body.statements.iter().enumerate() {
        let StatementKind::Apply {
            gate,
            parameters,
            qubits,
        } = &statement.kind
        else {
            panic!("expected a controlled broadcast gate");
        };
        assert_eq!(*gate, Gate::Cry);
        assert_eq!(parameters.len(), 1);
        assert_eq!(qubits[0].register, broadcast.quantum_registers[0].id);
        assert_eq!(qubits[1].index, index);
    }
    let mut ids = Vec::new();
    broadcast.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort();
    assert_eq!(ids, (0..broadcast.ast_id_bound()).collect::<Vec<_>>());
}

#[test]
fn unsupported_control_modifiers_counts_and_invalid_operands_are_not_ignored() {
    for instruction in [
        "negctrl @ x q[0],q[1]",
        "pow(0.5) @ x q[0]",
        "ctrl(0) @ x q[0]",
        "ctrl(-1) @ x q[0]",
        "ctrl(1.0) @ x q[0],q[1]",
        "ctrl(1+0) @ x q[0],q[1]",
        "ctrl(3) @ x q[0],q[1],q[2],q[3]",
        "ctrl @ ctrl @ ctrl @ x q[0],q[1],q[2],q[3]",
        "ctrl(2) @ ry(pi/3) q[0],q[1],q[2]",
        "ctrl(2) @ h q[0],q[1],q[2]",
        "ctrl @ gphase(pi/3) q[0]",
        "ctrl @ ry q[0],q[1]",
        "ctrl @ x q[0]",
        "ctrl @ x q[0],q[0]",
        "ctrl @ ry(pi/3) q,q[0]",
    ] {
        assert!(
            parse_str(
                &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[4] q; {instruction};"),
                "unsupported-control.qasm"
            )
            .is_err(),
            "{instruction}"
        );
    }
}

#[test]
fn positive_controls_match_native_gates_on_coherent_inputs() {
    use irene::ir::{Program, Qubit};
    use irene::symbolic::{ExecutionConfig, OutputSelection, execute};
    let parse = |body: &str| {
        parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; h q[0]; {body}"),
            "coherent-controls",
        )
        .unwrap()
    };
    let run = |p: &Program| {
        let qubits = (0..3).map(|index| Qubit {
            register: p.quantum_registers[0].id,
            index,
        });
        execute(
            p,
            &ExecutionConfig::all_symbolic(),
            &OutputSelection::new(qubits, []),
        )
        .unwrap()
    };
    for (modified, native) in [
        ("ctrl @ x", "cx"),
        ("ctrl @ y", "cy"),
        ("ctrl @ z", "cz"),
        ("ctrl @ p(pi/7)", "cp(pi/7)"),
        ("ctrl @ phase(pi/7)", "cp(pi/7)"),
        ("ctrl @ u1(pi/7)", "cp(pi/7)"),
        ("ctrl @ rx(pi/7)", "crx(pi/7)"),
        ("ctrl @ ry(pi/7)", "cry(pi/7)"),
        ("ctrl @ rz(pi/7)", "crz(pi/7)"),
    ] {
        let left = run(&parse(&format!("{modified} q[0],q[1];")));
        let right = run(&parse(&format!("{native} q[0],q[1];")));
        assert_eq!(left, right, "{modified}");
        assert!(left.components.iter().all(|c| c.output.history.is_empty()));
    }
    for (modified, native) in [
        ("ctrl @ cx", "ccx"),
        ("ctrl @ cz", "ccz"),
        ("ctrl(2) @ x", "ccx"),
        ("ctrl(2) @ z", "ccz"),
        ("ctrl @ ctrl @ x", "ccx"),
        ("ctrl @ ctrl @ z", "ccz"),
    ] {
        assert_eq!(
            run(&parse(&format!("{modified} q[2],q[0],q[1];"))),
            run(&parse(&format!("{native} q[2],q[0],q[1];"))),
            "{modified}",
        );
    }
}

#[test]
fn controls_do_not_accept_unimplemented_decompositions_or_modifiers() {
    for body in [
        "ctrl @ h q[0],q[1];",
        "ctrl @ swap q[0],q[1],q[2];",
        "ctrl @ s q[0],q[1];",
        "ctrl @ inv @ x q[0],q[1];",
        "inv @ ctrl @ x q[0],q[1];",
        "pow(2) @ ctrl @ x q[0],q[1];",
        "ctrl @ pow(2) @ x q[0],q[1];",
        "ctrl @ cu(1,2,3,4) q[0],q[1],q[2];",
    ] {
        let source = format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {body}");
        assert!(
            parse_str(&source, "unsupported-controls").is_err(),
            "{body}"
        );
    }
    assert!(
        parse_str(
            "OPENQASM 3.0; qubit[2] q; ctrl @ x q[0],q[1];",
            "missing-include"
        )
        .is_err()
    );
    assert!(
        parse_str(
            "OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] a; qubit[3] b; ctrl @ x a,b;",
            "width-mismatch"
        )
        .is_err()
    );
}
