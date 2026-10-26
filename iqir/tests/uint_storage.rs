use iqir::{ScalarExprKind, StatementKind, frontend};

fn parse(body: &str) -> iqir::Program {
    frontend::parse_str_with_options(&format!("OPENQASM 3; {body}"), "uint.qasm", true).unwrap()
}

#[test]
fn arithmetic_retains_width_and_one_assignment() {
    let p = parse("uint[8] n=255; n+=1; while(n<5) { n+=1; }");
    assert!(p.classical_registers.is_empty());
    assert!(matches!(
        p.body.statements[0].kind,
        StatementKind::ScalarDeclare {
            ty: iqir::ScalarType::Int {
                width: 8,
                signed: false
            },
            ..
        }
    ));
    let StatementKind::ScalarAssign { value, .. } = &p.body.statements[1].kind else {
        panic!()
    };
    assert!(matches!(value.kind.kind, ScalarExprKind::Binary { .. }));
    let StatementKind::While { body, .. } = &p.body.statements[2].kind else {
        panic!()
    };
    assert!(body.classical_registers.is_empty());
    assert_eq!(body.statements.len(), 1);
    assert!(matches!(
        body.statements[0].kind,
        StatementKind::ScalarAssign { .. }
    ));
}

#[test]
fn whole_source_bit_uses_keep_word_storage() {
    for source in [
        "uint[8] n=0; bit[8] c=bit[8](n);",
        "uint[8] n=0; bool b=n[0];",
    ] {
        let p = parse(source);
        assert!(
            p.classical_registers.iter().any(|r| r.name == "n"),
            "{source}"
        );
    }
}

#[test]
fn scalar_bitwise_does_not_expand_integers_into_boolean_registers() {
    for source in [
        "uint[8] n=0; uint[8] mask=3; n+=1; n^=mask;",
        "uint[8] n=0; uint[8] m=~n;",
        "uint[8] n=0; bool choice=false; if(choice){n=1;} uint[8] m=n & 3;",
    ] {
        let p = parse(source);
        assert!(!p.classical_registers.iter().any(|r| r.name == "n"), "{source}");
    }
}

#[test]
fn qubit_and_bit_register_indexing_does_not_expand_integers() {
    let p = parse("qubit[2] q; bit[2] c; uint[8] n=0; c[1]=measure q[1]; c[1]^=true; n+=1;");
    assert!(!p.classical_registers.iter().any(|r| r.name == "n"));
}

#[test]
fn scalar_scope_and_default_width_are_preserved() {
    let p = parse("uint n=0; if(true) { uint[8] n=255; n+=1; } n+=1;");
    let StatementKind::ScalarDeclare { id: outer, ty, .. } = p.body.statements[0].kind else {
        panic!()
    };
    assert_eq!(
        ty,
        iqir::ScalarType::Int {
            width: 32,
            signed: false
        }
    );
    let StatementKind::If { then_branch, .. } = &p.body.statements[1].kind else {
        panic!()
    };
    let StatementKind::ScalarDeclare { id: inner, .. } = then_branch.statements[0].kind else {
        panic!()
    };
    assert_ne!(outer, inner);
}
