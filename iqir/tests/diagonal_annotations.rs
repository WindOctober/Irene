use iqir::frontend;

#[test]
fn matrix_and_orthogonality_helpers_are_typed() {
    for expression in [
        r"\diag(1,0) == |0><0|",
        r"\orthogonal(|+>, |->)",
        r"\diag(1,0,0,0) == |00><00|",
    ] {
        frontend::parse_str(
            &format!("OPENQASM 3;\n@saria.assert {expression}\n"),
            "matrix.qasm",
        )
        .unwrap();
    }
    for expression in [
        r"\diag(q)",
        r"\diag(1,2,3)",
        r"\diag(|0>,|1>)",
        r"\orthogonal(|0>,|00>)",
        r"\orthogonal(q,q)",
    ] {
        assert!(
            frontend::parse_str(
                &format!("OPENQASM 3; qubit q;\n@saria.assert {expression}\n"),
                "matrix.qasm"
            )
            .is_err()
        );
    }
}

#[test]
fn diagonal_is_a_boolean_query_on_program_quantum_references() {
    for annotation in ["assert", "invariant"] {
        let tail = if annotation == "invariant" {
            "while (b) { b=false; }"
        } else {
            ""
        };
        frontend::parse_str(&format!("OPENQASM 3; qubit[2] q; bool b=true;\n@saria.{annotation} \\diagonal(q) && \\diagonal(q[0])\n{tail}"), "diagonal.qasm").unwrap();
    }
    for expression in [
        "\\diagonal(1)",
        "\\diagonal(|0>)",
        "\\diagonal()",
        "\\diagonal(q,q)",
    ] {
        assert!(
            frontend::parse_str(
                &format!("OPENQASM 3; qubit q;\n@saria.assert {expression}\n"),
                "bad.qasm"
            )
            .is_err()
        );
    }
}
