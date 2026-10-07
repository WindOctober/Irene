use iqir::*;
use std::collections::BTreeSet;

fn parse(body: &str) -> Program {
    let p = frontend::parse_str(
        &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
        "gate.qasm",
    )
    .unwrap();
    let mut ids = Vec::new();
    p.visit_ast_ids(|id| ids.push(id.index()));
    let unique: BTreeSet<_> = ids.iter().copied().collect();
    assert_eq!(ids.len(), unique.len(), "shared AST identity");
    assert_eq!(
        unique.into_iter().collect::<Vec<_>>(),
        (0..p.ast_id_bound()).collect::<Vec<_>>()
    );
    p
}

#[test]
fn custom_gates_expand_nested_parameters_broadcasts_and_structured_modifiers() {
    let p = parse(
        "gate a(theta) q {rx(theta) q; rz(theta/2) q;} gate b(theta) q {a(theta/2) q;} qubit[3] q; b(pi) q; ctrl @ inv @ pow(2) @ b(pi) q[0],q[1];",
    );
    assert!(
        matches!(&p.body.statements[1].kind,StatementKind::Unitary {controls,power:-2,..} if controls.len()==1)
    );
}

#[test]
fn signatures_are_checked_at_definition_and_bodies_at_call() {
    for definition in [
        "gate bad q {reset q;}",
        "gate bad q {bad q;}",
        "gate bad q {later q;} gate later q {x q;}",
        "qubit outer; gate bad q {x outer;}",
        "input angle theta; gate bad q {rx(theta) q;}",
        "gate bad q {x q[0];}",
        "gate bad q {int[8] n=0;}",
        "gate bad q {h q,q;}",
        "gate bad q {ry() q;}",
        "gate bad q {rx(theta) q;} const float theta=1.0;",
        "gate bad q {pow(n) @ x q;} const int n=1;",
    ] {
        parse(definition);
        let called =
            format!("OPENQASM 3; include \"stdgates.inc\"; {definition} qubit data; bad data;");
        assert!(
            frontend::parse_str(&called, "called.qasm").is_err(),
            "{called}"
        );
    }
    for body in [
        "gate bad(t,t) q {rx(t) q;}",
        "gate bad q,q {cx q,q;}",
        "gate a q {x q;} qubit q; ctrl @ a q,q;",
        "gate a q {x q;} qubit[2] a1; qubit[3] b1; ctrl @ a a1,b1;",
        "gate a q {x q;} qubit q; pow(0) @ a q,q;",
    ] {
        assert!(
            frontend::parse_str(
                &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
                "signature.qasm"
            )
            .is_err(),
            "{body}"
        );
    }
}

#[test]
fn calls_keep_definition_visibility_and_caller_bindings_separate() {
    parse(
        "const float theta=0.5; gate a q {rx(theta) q;} gate b(angle_arg) q {a q; rz(angle_arg) q;} qubit q; if(true) {const float theta=1.0; b(theta) q;}",
    );
    parse("gate a(theta) q {rx(theta) q;} qubit q; a(pi/2) q; a(pi/4) q;");
    let source = "OPENQASM 3; include \"stdgates.inc\"; gate a q {rx(theta) q;} gate b(theta) q {a q;} qubit q; b(pi) q;";
    assert!(frontend::parse_str(source, "capture.qasm").is_err());
}

#[test]
fn gate_calls_reuse_power_analysis_and_bound_expansion() {
    parse("gate custom a {pow(uint[1](\"1\")) @ x a;} qubit q; custom q;");
    for duplicate_body in [true, false] {
        let mut source =
            "OPENQASM 3; include \"stdgates.inc\"; gate g0(theta) a {rx(theta) a;}".to_owned();
        for i in 1..22 {
            let prev = i - 1;
            if duplicate_body {
                source += &format!("gate g{i}(theta) a {{g{prev}(theta) a; g{prev}(theta) a;}}");
            } else {
                source += &format!("gate g{i}(theta) a {{g{prev}(theta+theta) a;}}");
            }
        }
        frontend::parse_str(&source, "unused-gates.qasm").unwrap();
        source += "qubit q; g21(pi) q;";
        let error = frontend::parse_str(&source, "bounded-gates.qasm").unwrap_err();
        assert!(error.to_string().contains("budget"), "{error}");
    }
}
