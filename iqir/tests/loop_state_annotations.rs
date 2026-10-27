use iqir::{
    annotation::{AnnotationKind, AnnotationPayload, SpecExpr},
    frontend,
};

#[test]
fn absent_exit_state_is_explicit_and_only_applies_to_a_loop() {
    let p = frontend::parse_str(
        "OPENQASM 3;\n@saria.exit_state none\nwhile(false) {}",
        "none.qasm",
    )
    .unwrap();
    assert!(p.annotations.values().flatten().any(|a|
        a.kind == AnnotationKind::ExitState && a.payload == AnnotationPayload::NoState));
    for source in [
        "OPENQASM 3; qubit q;\n@saria.exit_state none\nreset q;",
        "OPENQASM 3; qubit q;\n@saria.exit_state none\n@saria.exit_state q := |0><0|\nwhile(false) {}",
        "OPENQASM 3;\n@saria.exit_state none\n@saria.exit_state none\nwhile(false) {}",
        "OPENQASM 3;\n@saria.invariant none\nwhile(false) {}",
    ] {
        assert!(frontend::parse_str(source, "bad.qasm").is_err(), "{source}");
    }
}

#[test]
fn joint_operator_declarations_resolve_targets_and_coefficients() {
    let p = frontend::parse_str(
        r"OPENQASM 3; qubit[2] q; bool b=false;
pragma saria.def weight() -> real = \real(1)/2
@saria.invariant q := \diag(weight(), 0, 0, weight())
@saria.exit_state [q[1], q[0]] := (b ? weight() : \real(0)) * |00><00|
while(!b){reset q;b=true;}
",
        "state.qasm",
    )
    .unwrap();
    let clauses = p.annotations.values().next().unwrap();
    assert_eq!(clauses[0].kind, AnnotationKind::Invariant);
    assert!(matches!(
        clauses[0].payload,
        AnnotationPayload::State { .. }
    ));
    let AnnotationPayload::State { targets, operator } = &clauses[1].payload else {
        panic!("not a state declaration")
    };
    assert_eq!(targets.len(), 2);
    assert!(matches!(targets[0].uncast(), SpecExpr::Index { .. }));
    assert!(matches!(operator.uncast(), SpecExpr::Binary { .. }));
}

#[test]
fn initial_state_is_a_checked_loop_boundary_not_an_invariant() {
    let p = frontend::parse_str(
        r"OPENQASM 3; qubit q; bool stop=false;
@saria.initial_state q := |0><0|
@saria.invariant !stop => q == |0>
@saria.exit_state q := |0><0|
while (!stop) { stop=true; }
",
        "initial.qasm",
    )
    .unwrap();
    let clauses = p.annotations.values().next().unwrap();
    assert_eq!(clauses[0].kind, AnnotationKind::InitialState);
    assert!(matches!(
        clauses[0].payload,
        AnnotationPayload::State { .. }
    ));
    for source in [
        "OPENQASM 3; qubit q;\n@saria.initial_state q := |0><0|\nreset q;",
        "OPENQASM 3; qubit q;\n@saria.initial_state q := unknown * |0><0|\nwhile (false) {}",
    ] {
        assert!(frontend::parse_str(source, "bad.qasm").is_err());
    }
}

#[test]
fn malformed_or_implicit_joint_states_are_rejected() {
    for clause in [
        "exit_state [] := |0><0|",
        "exit_state b := |0><0|",
        "exit_state [q[0],q[0]] := |00><00|",
        "exit_state [q,q[1]] := |000><000|",
        "exit_state q[2] := |0><0|",
        "exit_state q[n] := |0><0|",
        "exit_state q := |0><0|",
        "exit_state q := |00>",
        "exit_state q := w * |00><00|",
        r"exit_state q := \avg_density(q)",
        r"exit_state q := \probability(b) * |00><00|",
        "exit_state q := (q[0] == |0> ? |00><00| : |11><11|)",
        "invariant q with A: psd[2] := A",
        "invariant q := |0><0|",
        "invariant [q[0],q[0]] := |00><00|",
        "entry_state true",
        "entry_state q := |00><00|",
        "assert q := |00><00|",
    ] {
        let source = format!(
            "OPENQASM 3; qubit[2] q; bool b=false; uint n=0;\n@saria.{clause}\nwhile(!b){{b=true;}}"
        );
        assert!(
            frontend::parse_str(&source, "bad.qasm").is_err(),
            "{clause}"
        );
    }
    assert!(
        frontend::parse_str(
            "OPENQASM 3; qubit q;\n@saria.exit_state q := |0><0|\nreset q;",
            "bad.qasm"
        )
        .is_err()
    );
}

#[test]
fn state_contracts_resolve_quantum_references_and_keep_clause_order() {
    let p = frontend::parse_str(
        r"OPENQASM 3; qubit q; bool stop=false;
@saria.invariant \diagonal(q)
@saria.exit_state q == |0>
while(!stop){ reset q; stop=true; }
",
        "states.qasm",
    )
    .unwrap();
    let clauses = p.annotations.values().next().unwrap();
    assert_eq!(clauses[0].kind, AnnotationKind::Invariant);
    assert_eq!(clauses[1].kind, AnnotationKind::ExitState);
}

#[test]
fn state_contracts_are_boolean_loop_clauses() {
    for clause in ["invariant", "exit_state"] {
        for (predicate, statement) in [
            ("q", "while(false) {}"),
            ("true", "reset q;"),
            ("missing == |0>", "while(false) {}"),
            ("true", ""),
        ] {
            assert!(
                frontend::parse_str(
                    &format!("OPENQASM 3; qubit q;\n@saria.{clause} {predicate}\n{statement}"),
                    "bad.qasm"
                )
                .is_err()
            );
        }
    }
}
