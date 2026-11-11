use iqir::{Block, Program, StatementKind as S, frontend};

fn walk<'a>(b: &'a Block, out: &mut Vec<&'a iqir::Statement>) {
    for s in &b.statements {
        out.push(s);
        match &s.kind {
            S::Scope(b) | S::While { body: b, .. } | S::Unitary { body: b, .. } => walk(b, out),
            S::If {
                then_branch,
                else_branch,
                ..
            }
            | S::LoopBody {
                body: then_branch,
                step: else_branch,
            } => {
                walk(then_branch, out);
                walk(else_branch, out);
            }
            S::UnrolledLoop { iterations } => {
                for b in iterations {
                    walk(b, out);
                }
            }
            _ => {}
        }
    }
}

fn check_ids_and_annotations(p: &Program) {
    let mut ids = vec![];
    p.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort();
    assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
    let mut statements = vec![];
    walk(&p.body, &mut statements);
    for id in p.annotations.keys() {
        assert!(statements.iter().any(|s| s.ast_id() == *id));
    }
}

#[test]
fn signed_comparison_promotion_preserves_unique_ids_and_assertion_anchors() {
    for condition in ["int[2](b) == 2", "3 == int[2](b)", "int[2](b) < 2"] {
        let source = format!(
            "OPENQASM 3; include \"stdgates.inc\"; qubit q; bit[2] b; if ({condition}) {{ x q; }}\n@saria.assert q == |0>\n"
        );
        assert!(frontend::parse_str(&source, "old.qasm").is_err());
        let p = frontend::openqasm3::parse_for_translation(&source, "translation.qasm").unwrap();
        assert_eq!(p.annotations.values().map(Vec::len).sum::<usize>(), 1);
        check_ids_and_annotations(&p);
        fn eval(e: &iqir::ClassicalExpr, raw: u8) -> bool {
            use iqir::ClassicalExprKind as E;
            match &e.kind {
                E::Bool(v) => *v,
                E::Bit(b) => raw & (1 << b.index) != 0,
                E::Not(a) => !eval(a, raw),
                E::And(a, b) => eval(a, raw) && eval(b, raw),
                E::Or(a, b) => eval(a, raw) || eval(b, raw),
                E::Eq(a, b) => eval(a, raw) == eval(b, raw),
                E::Xor(a, b) => eval(a, raw) != eval(b, raw),
                _ => panic!("expected bit-level comparison lowering"),
            }
        }
        let mut statements = vec![];
        walk(&p.body, &mut statements);
        let cond = statements
            .iter()
            .find_map(|s| match &s.kind {
                S::If { condition, .. } => Some(condition),
                _ => None,
            })
            .unwrap();
        for raw in 0..4 {
            // int[2] denotes 0, 1, -2, -1, never unsigned 2 or 3.
            assert_eq!(eval(cond, raw), condition.contains('<'));
        }
    }
}

#[test]
fn translation_keeps_large_counted_loops_without_requiring_proof_hints() {
    let source = "OPENQASM 3; include \"stdgates.inc\"; qubit q; for int i in [0:2048] { x q; }\n@saria.assert q == |1>\n";
    assert!(frontend::openqasm3::parse_structured(source, "verifier.qasm").is_err());
    let p = frontend::openqasm3::parse_for_translation(source, "translation.qasm").unwrap();
    check_ids_and_annotations(&p);
    let mut statements = vec![];
    walk(&p.body, &mut statements);
    assert!(statements.iter().any(|s| matches!(s.kind, S::While { .. })));
}

#[test]
fn translation_never_expands_small_nested_descending_or_empty_loops() {
    for (range, expected) in [("0:0",1), ("0:9",1), ("8:-1:0",1), ("2:1",1)] {
        let source = format!("OPENQASM 3; int[32] n=0; for int i in [{range}] {{ n+=1; }}");
        let p=frontend::openqasm3::parse_for_translation(&source,"retain.qasm").unwrap();
        check_ids_and_annotations(&p);
        let mut statements=vec![]; walk(&p.body,&mut statements);
        assert_eq!(statements.iter().filter(|s| matches!(s.kind,S::While{..})).count(),expected);
        assert!(!statements.iter().any(|s| matches!(s.kind,S::UnrolledLoop{..})));
    }
    let source="OPENQASM 3; int[32] n=0; for int i in [0:2] { for int j in [0:3] { n+=1; }}";
    let p=frontend::openqasm3::parse_for_translation(source,"nested.qasm").unwrap();
    check_ids_and_annotations(&p);
    let mut statements=vec![]; walk(&p.body,&mut statements);
    assert_eq!(statements.iter().filter(|s| matches!(s.kind,S::While{..})).count(),2);
}
