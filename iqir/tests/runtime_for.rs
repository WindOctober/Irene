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
        "int[8] limit; for int[8] i in [0:2:limit] {}",
        "int[8] limit; for int[8] i in [limit:-1:0] {}",
        "int[8] limit; for int[8] i in [0:limit] {} int[8] n=i;",
        "int[8] limit;\n@saria.invariant local == 0\nfor int[8] i in [0:limit] {int[8] local=0;}",
        "int[8] limit; float[64] angle=0.0; qubit q; for int[8] i in [0:limit]{rx(angle) q; angle+=1.0;}",
    ] {
        assert!(parse(body).is_err(), "{body}");
    }
}
