use iqir::{NumericExprKind, ScalarExprKind, StatementKind, frontend};

fn parse(body: &str) -> iqir::Program {
    let source = format!("OPENQASM 3; include \"stdgates.inc\"; {body}");
    let p = frontend::parse_str(&source, "casts.qasm").unwrap();
    let scalar = frontend::parse_str_with_options(&source, "casts.qasm", true).unwrap();
    for program in [&p, &scalar] {
        let mut ids = vec![];
        program.visit_ast_ids(|id| ids.push(id.index()));
        ids.sort();
        assert_eq!(ids, (0..program.ast_id_bound()).collect::<Vec<_>>());
    }
    p
}

#[test]
fn casts_preserve_integer_subexpressions_and_explicit_intermediate_precision() {
    for body in [
        "int[32] n; float[64] f=float[64](n/2);",
        "uint[64] n; float[32] f=float[32](n);",
        "int[32] n; float[64] f=float[64](float[32](n));",
        "bit[4] b; float[64] f=float[64](uint[4](b));",
        "int[32] n; float[64] f=n/2;",
    ] {
        parse(body);
    }
    let p = parse("int[32] n; float[64] f=float[64](n/2);");
    let StatementKind::ScalarDeclare {
        initializer: Some(e),
        ..
    } = &p.body.statements[1].kind
    else {
        panic!()
    };
    let ScalarExprKind::FloatCast(inner) = &e.kind.kind else {
        panic!()
    };
    assert!(!inner.ty.is_float());
    assert!(matches!(inner.kind.kind, ScalarExprKind::Binary { .. }));
}

#[test]
fn dynamic_angles_keep_machine_arithmetic_and_copy_all_ast_ids() {
    let p = parse(
        "gate twice(a) q { p(a) q; p(a) q; } qubit q; int[32] n; twice(pi*float[64](n)/2.0) q;",
    );
    // Cloning gate parameters must also clone their scalar subtrees.
    fn visit(block: &iqir::Block, found: &mut usize) {
        for s in &block.statements {
            match &s.kind {
                StatementKind::Apply { parameters, .. } => {
                    *found += parameters
                        .iter()
                        .filter(|p| matches!(p.kind, NumericExprKind::Scalar(_)))
                        .count();
                }
                StatementKind::Scope(b) | StatementKind::Unitary { body: b, .. } => visit(b, found),
                _ => {}
            }
        }
    }
    let mut found = 0;
    visit(&p.body, &mut found);
    assert_eq!(found, 2);
}

#[test]
fn bit_to_float_is_not_an_integer_conversion() {
    assert!(
        frontend::parse_str(
            "OPENQASM 3; bit[4] b; float[64] f=float[64](b);",
            "bad.qasm"
        )
        .is_err()
    );
}
