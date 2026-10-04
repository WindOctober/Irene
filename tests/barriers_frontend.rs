use irene::frontend::{openqasm2, openqasm3};
use irene::ir::{Block, Program, StatementKind};

fn parse(version: u8, body: &str) -> Result<Program, String> {
    let declarations = if version == 2 {
        "include \"qelib1.inc\"; qreg q[2]; creg c[1];"
    } else {
        "include \"stdgates.inc\"; qubit[2] q; bit[1] c;"
    };
    let source = format!("OPENQASM {version}.0; {declarations} {body}");
    if version == 2 {
        openqasm2::parse_str(&source, "barrier-test.qasm").map_err(|e| format!("{e:?}"))
    } else {
        openqasm3::parse_str(&source, "barrier-test.qasm").map_err(|e| format!("{e:?}"))
    }
}

// Discard only empty scopes and conditionals whose branches have no effects.
fn effects(block: &Block) -> Vec<StatementKind> {
    let mut result = Vec::new();
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::Scope(body) => result.extend(effects(body)),
            StatementKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                assert!(effects(then_branch).is_empty());
                assert!(effects(else_branch).is_empty());
            }
            other => result.push(other.clone()),
        }
    }
    result
}

#[test]
fn empty_and_operand_barriers_have_no_effects() {
    for version in [2, 3] {
        for body in ["barrier;", "barrier q;", "barrier q[0], q[1];"] {
            let program = parse(version, body).unwrap();
            let baseline = parse(version, "").unwrap();
            assert_eq!(effects(&program.body), effects(&baseline.body));
        }
    }
}

#[test]
fn barriers_preserve_gate_and_measurement_ir() {
    for version in [2, 3] {
        let conditional = if version == 2 {
            "if (c == 1) barrier q; if (c == 0) barrier;"
        } else {
            "if (c[0]) { barrier q; } else { barrier; }"
        };
        let original = parse(
            version,
            "h q[0]; measure q[0] -> c[0]; cx q[0],q[1]; h q[1];",
        )
        .unwrap();
        let fenced = parse(
            version,
            &format!(
                "barrier; h q[0]; barrier q; measure q[0] -> c[0]; {conditional}
             cx q[0],q[1]; barrier q[0],q[1]; h q[1]; barrier;"
            ),
        )
        .unwrap();
        let expected = effects(&original.body);
        assert_eq!(
            expected
                .iter()
                .filter(|s| matches!(
                    s,
                    StatementKind::Apply { .. } | StatementKind::Measure { .. }
                ))
                .count(),
            4
        );
        assert_eq!(effects(&fenced.body), expected, "OpenQASM {version}");
    }
}

#[test]
fn invalid_barrier_operands_and_conditions_are_rejected() {
    for version in [2, 3] {
        for body in ["barrier missing;", "barrier q[2];", "barrier c;"] {
            assert!(parse(version, body).is_err(), "OpenQASM {version}: {body}");
            let conditional = if version == 2 {
                format!("if (c == 1) {body}")
            } else {
                format!("if (c[0]) {{ {body} }}")
            };
            assert!(parse(version, &conditional).is_err(), "{conditional}");
        }
        let unknown_condition = if version == 2 {
            "if (missing == 1) barrier;"
        } else {
            "if (missing) { barrier; }"
        };
        assert!(parse(version, unknown_condition).is_err());
    }
}
