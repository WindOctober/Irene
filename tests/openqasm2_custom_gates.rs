use irene::frontend::openqasm2;
use irene::ir::{Block, Gate, StatementKind};

fn source(body: &str) -> String {
    format!("OPENQASM 2.0; include \"qelib1.inc\"; {body}")
}

fn gates(block: &Block, output: &mut Vec<(Gate, Vec<usize>)>) {
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::Apply { gate, qubits, .. } => {
                output.push((*gate, qubits.iter().map(|q| q.index).collect()))
            }
            StatementKind::Scope(body) => gates(body, output),
            StatementKind::If { then_branch, .. } => gates(then_branch, output),
            _ => {}
        }
    }
}

#[test]
fn nested_broadcast_and_conditional_expansion() {
    let program = openqasm2::parse_str(&source("gate pair a,b { h a; cx a,b; } gate wrap a,b { pair b,a; barrier a,b; } qreg q[2]; qreg r[2]; creg c[1]; if(c==0) wrap q,r;"), "test").unwrap();
    let mut actual = Vec::new();
    gates(&program.body, &mut actual);
    assert_eq!(actual.len(), 4);
    assert_eq!(
        actual.iter().map(|(_, q)| q.clone()).collect::<Vec<_>>(),
        vec![vec![0], vec![0, 0], vec![1], vec![1, 1]]
    );
    assert!(
        program
            .body
            .statements
            .iter()
            .any(|s| matches!(s.kind, StatementKind::If { .. }))
    );
}

#[test]
fn lexical_parameters_and_division_validation() {
    for body in [
        "gate inner(t) a { ry(t) a; } gate outer(t) a { inner(t/2) a; } qreg q[1]; outer(pi/2) q[0];",
        "gate empty a {} qreg q[1]; empty q;",
        "gate rot(theta) a { rz(theta) a; } qreg theta[1]; rot(pi/4) theta;",
    ] {
        openqasm2::parse_str(&source(body), "test").unwrap();
    }
    assert!(
        openqasm2::parse_str(
            &source("gate g(t) a { ry(1/t) a; } qreg q[1]; g(0) q;"),
            "test"
        )
        .is_err()
    );
}

#[test]
fn invalid_definitions_and_calls_are_rejected() {
    for body in [
        "gate g a { g a; }",
        "gate g a { later a; } gate later a { x a; }",
        "gate g(t,t) a { x a; }",
        "gate g(t) t { x t; }",
        "gate g a { reset a; }",
        "gate g a { measure a; }",
        "gate g a { qreg b[1]; }",
        "qreg q[1]; gate g a { x q; }",
        "gate g a { x a[0]; }",
        "gate g a { ry(missing) a; }",
        "gate g a { cx a,a; }",
        "gate g a { x a; } qreg q[1]; g(1) q;",
        "gate g a,b { cx a,b; } qreg q[1]; g q,q;",
        "gate g a,b { cx a,b; } qreg q[2]; qreg r[3]; g q,r;",
        "gate g a {} gate g b {}",
        "gate g(t,) a { ry(t) a; }",
        "gate g a, { x a; }",
        "gate g a { x a,; }",
        "gate g a { if(c==0) x a; }",
    ] {
        assert!(
            openqasm2::parse_str(&source(body), "test").is_err(),
            "accepted: {body}"
        );
    }
}

#[test]
fn explicit_ccz_definition_overrides_only_the_extension() {
    let program = openqasm2::parse_str(
        &source("gate ccz a,b,c { x a; } qreg q[3]; ccz q[0],q[1],q[2];"),
        "test",
    )
    .unwrap();
    let mut actual = Vec::new();
    gates(&program.body, &mut actual);
    assert_eq!(actual.len(), 1);
    assert_eq!(actual[0].1, vec![0]);
    assert!(openqasm2::parse_str(&source("gate h a { x a; }"), "test").is_err());
    assert!(openqasm2::parse_str(&source("gate ccz a {} gate ccz b {}"), "test").is_err());
}

#[test]
fn legal_acyclic_chain_has_no_fixed_depth_cap() {
    let mut body = String::from("gate g0 a { x a; }");
    for i in 1..70 {
        body.push_str(&format!("gate g{i} a {{ g{} a; }}", i - 1));
    }
    body.push_str("qreg q[1]; g69 q;");
    assert_eq!(
        openqasm2::parse_str(&source(&body), "test")
            .unwrap()
            .operation_count(),
        1
    );
}
