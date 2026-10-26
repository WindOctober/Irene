use iqir::{Block, StatementKind as S, annotation::AnnotationKind as A, frontend};

fn parse(body: &str) -> Result<iqir::Program, String> {
    frontend::parse_str_with_options(&format!("OPENQASM 3; {body}"), "for.qasm", true)
        .map_err(|e| e.to_string())
}
fn loops<'a>(block: &'a Block, out: &mut Vec<&'a iqir::Statement>) {
    for s in &block.statements {
        match &s.kind {
            S::While { body, .. } => {
                out.push(s);
                loops(body, out);
            }
            S::Scope(b) => loops(b, out),
            S::If {
                then_branch,
                else_branch,
                ..
            } => {
                loops(then_branch, out);
                loops(else_branch, out);
            }
            _ => {}
        }
    }
}
#[test]
fn runtime_contracts_attach_to_the_generated_while_not_setup_scope() {
    let p=parse("int[8] limit;\n@saria.invariant index >= 0\nfor int[8] index in [0:limit] { limit=0; }\n").unwrap();
    let mut ls = vec![];
    loops(&p.body, &mut ls);
    assert_eq!(ls.len(), 1);
    let annotations = &p.annotations[&ls[0].ast_id()];
    assert!(annotations.iter().any(|a| a.kind == A::Invariant));
    let mut ids = vec![];
    p.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort();
    assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
}
#[test]
fn unsupported_runtime_ranges_scopes_and_backedge_constants_fail_closed() {
    for body in [
        "int[8] limit; for int[8] i in [0:limit] {int[8] i=0;}",
        "for int[8] i in [0:1] {int[8] i=0;}",
        "uint[8] limit; for uint[8] i in [0:limit] {bit i;}",
        "for uint[8] i in [0:1] {bit i;}",
        "int[8] limit; for int[8] i in [0:limit] {const int[8] i=0;}",
        "for int[8] i in [0:1] {const int[8] i=0;}",
        "int[8] limit; for int[8] i in [0:limit] {int[8] local=0;} int[8] n=local;",
        "int[8] limit; for int[8] i in [0:2:limit] {}",
        "int[8] limit; for int[8] i in [limit:-1:0] {}",
        "int[8] limit; for int[8] i in [0:limit] {} int[8] n=i;",
        "int[8] limit;\n@saria.invariant local == 0\nfor int[8] i in [0:limit] {int[8] local=0;}",
        "int[8] limit; float[64] angle=0.0; qubit q; for int[8] i in [0:limit]{rx(angle) q; angle+=1.0;}",
    ] {
        assert!(parse(body).is_err(), "{body}");
    }
}

#[test]
fn runtime_iterator_binding_is_shared_with_body_but_not_nested_blocks() {
    use iqir::annotation::{AnnotationPayload, SpecExpr};
    fn declaration(block: &Block, name: &str) -> iqir::SymbolId {
        block.statements.iter().find_map(|s| match &s.kind {
            S::ScalarDeclare { id, name: found, .. } if found == name => Some(*id),
            _ => None,
        }).unwrap()
    }
    let p = parse("int[8] i; int[8] limit;\n@saria.invariant i >= 0\nfor int[8] i in [0:limit] { i=1; if(true){int[8] i=2; i=3;} i=4; } int[8] after=i;").unwrap();
    let outer = declaration(&p.body, "i");
    let setup = p.body.statements.iter().find_map(|s| match &s.kind {
        S::Scope(b) => Some(b),
        _ => None,
    }).unwrap();
    let iterator = declaration(setup, "i");
    assert_ne!(outer, iterator);
    let mut ls = Vec::new();
    loops(&p.body, &mut ls);
    assert_eq!(ls.len(), 1);
    let S::While { body, .. } = &ls[0].kind else { panic!() };
    let S::Scope(body) = &body.statements[0].kind else { panic!() };
    assert!(matches!(body.statements[0].kind, S::ScalarAssign { target, .. } if target == iterator));
    assert!(matches!(body.statements[2].kind, S::ScalarAssign { target, .. } if target == iterator));
    let S::If { then_branch, .. } = &body.statements[1].kind else { panic!() };
    let shadow = declaration(then_branch, "i");
    assert_ne!(shadow, iterator);
    assert!(matches!(then_branch.statements[1].kind, S::ScalarAssign { target, .. } if target == shadow));
    let S::ScalarDeclare { initializer: Some(after), .. } = &p.body.statements.last().unwrap().kind else { panic!() };
    assert!(matches!(after.kind.kind, iqir::ScalarExprKind::Read(id) if id == outer));
    for a in &p.annotations[&ls[0].ast_id()] {
        let AnnotationPayload::Expression(e) = &a.payload else { panic!() };
        let mut pending = vec![e];
        let mut references = Vec::new();
        while let Some(e) = pending.pop() {
            if let SpecExpr::Symbol { id, name } = e {
                if name == "i" { references.push(*id); }
            }
            pending.extend(e.children());
        }
        assert_eq!(references, [iterator]);
    }
    // Nested source scopes and nested loops may still shadow the iterator.
    for bound in ["1", "limit"] {
        parse(&format!("int[8] limit; for int[8] i in [0:{bound}] {{ if(true){{int[8] i=0;}} for int[8] i in [0:limit] {{}} }}")).unwrap();
    }
}
