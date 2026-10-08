use iqir::{
    StatementKind,
    annotation::{AnnotationKind, AnnotationPayload, SpecExpr},
    frontend,
};

fn parse(body: &str) -> Result<iqir::Program, String> {
    frontend::parse_str(&format!("OPENQASM 3;\n{body}"), "assertions.qasm")
        .map_err(|e| e.to_string())
}

#[test]
fn standalone_assertions_keep_their_own_boundaries_including_eof() {
    let p = parse("int n=0;\n@saria.assert n == 0\nn=1;\n@saria.assert n == 1\n@saria.assert true")
        .unwrap();
    let assertions: Vec<_> = p
        .body
        .statements
        .iter()
        .filter(|s| p.annotations.contains_key(&s.ast_id()))
        .collect();
    assert_eq!(assertions.len(), 3);
    for s in assertions {
        assert!(matches!(&s.kind, StatementKind::Scope(b) if b.statements.is_empty()));
        assert_eq!(p.annotations[&s.ast_id()][0].kind, AnnotationKind::Assert);
    }
    assert_eq!(
        p.annotations[&p.body.statements.last().unwrap().ast_id()][0].payload,
        AnnotationPayload::Expression(SpecExpr::Bool(true))
    );
}

#[test]
fn block_end_assertions_see_locals_before_scope_exit() {
    parse(
        "int n=0; while(n < 2) {
@saria.ghost local: int = n
n+=1;
@saria.assert n == local + 1
}
@saria.assert n == 2",
    )
    .unwrap();
    assert!(parse("int n=0; while(n < 2) {int local=0; n+=1;\n@saria.assert local == 0\n}\n@saria.assert local == 0").is_err());
    for body in [
        "@saria.assert 1",
        "@saria.assert missing",
        "@saria.ensures true",
        "int n=0;\n@saria.ensures true\n@saria.assert true\nn=1;",
    ] {
        assert!(parse(body).is_err(), "{body}");
    }
}

#[test]
fn density_and_distance_have_checked_quantum_dimensions() {
    parse(
        r"qubit[2] q;
@saria.assert \trace_distance(\avg_density(q[0]), (|0><0| + |1><1|)/2.0) < 1e-7
@saria.assert \trace_distance(\avg_density(q), |00><00|) <= 1.0",
    )
    .unwrap();
    for e in [
        r"\avg_density(1) == \I",
        r"\avg_density(|0>) == \I",
        r"\trace_distance(\avg_density(q), |0><0|) < 1.0",
        r"\trace_distance(|0>, |1>) < 1.0",
        r"\trace_distance(1, 2) < 1.0",
    ] {
        assert!(
            parse(&format!("qubit[2] q;\n@saria.assert {e}")).is_err(),
            "{e}"
        );
    }
}
