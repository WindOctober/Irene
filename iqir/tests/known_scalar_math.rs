use iqir::{ScalarValue, StatementKind, frontend};

fn parse(body: &str) -> iqir::Program {
    let program = frontend::parse_str(
        &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
        "known-math.qasm",
    )
    .unwrap();
    let mut ids = vec![];
    program.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort();
    assert_eq!(ids, (0..program.ast_id_bound()).collect::<Vec<_>>());
    program
}

#[test]
fn readonly_value_lookup_checks_types_overflow_and_does_not_mutate_ir() {
    let p = parse("int[8] source; int[8] result=source+1;");
    let StatementKind::ScalarDeclare {
        initializer: Some(expr),
        ..
    } = &p.body.statements[1].kind
    else {
        panic!()
    };
    let original = expr.clone();
    assert_eq!(expr.constant_value().unwrap(), None);
    assert_eq!(
        expr.constant_value_with(&|_| Some(ScalarValue::Integer(126)))
            .unwrap(),
        Some(ScalarValue::Integer(127))
    );
    assert!(
        expr.constant_value_with(&|_| Some(ScalarValue::Integer(127)))
            .is_err()
    );
    assert!(
        expr.constant_value_with(&|_| Some(ScalarValue::Integer(256)))
            .is_err()
    );
    assert!(
        expr.constant_value_with(&|_| Some(ScalarValue::Float64(0)))
            .is_err()
    );
    assert_eq!(*expr, original);
}
