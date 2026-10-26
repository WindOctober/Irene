use iqir::{Block, StatementKind as S, frontend};

fn parse(body: &str) -> Result<iqir::Program, String> {
    frontend::parse_str_with_options(
        &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
        "jumps.qasm",
        true,
    )
    .map_err(|e| e.to_string())
}
fn loops<'a>(b: &'a Block, out: &mut Vec<&'a iqir::Statement>) {
    for s in &b.statements {
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
fn jumps_have_fresh_ids_and_contracts_bind_the_actual_while() {
    for body in [
        "int[8] n=0;\n@saria.invariant n>=0\nwhile(n<3){n+=1; if(n==1){continue;} break;}",
        "int[8] limit;\n@saria.invariant i>=0\nfor int[8] i in [0:limit]{if(i==1){continue;}break;}",
    ] {
        let p = parse(body).unwrap();
        assert!(!format!("{p:?}").contains("@loop."), "no synthetic jump storage");
        let mut ls = vec![];
        loops(&p.body, &mut ls);
        assert_eq!(ls.len(), 1);
        assert_eq!(p.annotations[&ls[0].ast_id()].len(), 1);
        let mut ids = Vec::new();
        p.visit_ast_ids(|id| ids.push(id.index()));
        ids.sort();
        assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
    }
    parse("qubit[3] q; for int i in [0:2]{if(i==1)continue; x q[i]; if(i==2)break;}").unwrap();
    parse("for int i in [0:1]{break;} for int j in [0:1]{continue;} while(true){break;} while(false){continue;}").unwrap();
    let p = parse("for int i in [0:1]{break;}").unwrap();
    assert!(matches!(p.body.statements[0].kind, S::UnrolledLoop { .. }));
}

#[test]
fn jumps_cannot_escape_callees_or_lexical_scopes() {
    for body in [
        "break;",
        "continue;",
        "if(true){break;}",
        "def bad(){break;} while(true){bad();}",
        "def bad(){continue;} for int i in [0:2]{bad();}",
        "while(false){break;} continue;",
        "while(false){int[8] local=1;continue;} int[8] n=local;",
    ] {
        assert!(parse(body).is_err(), "{body}");
    }
    parse("def ok(){while(true){break;}} for int i in [0:2]{ok(); continue;}").unwrap();
}

#[test]
fn skipped_static_iterations_do_not_establish_unconditional_constants() {
    for jump in ["break", "continue"] {
        let body = format!(
            "qubit q; bit b=measure q; int[8] n=0; for int i in [0:1]{{if(b){{{jump};}} n=2;}} pow(n) @ x q;"
        );
        assert!(parse(&body).is_err(), "{body}");
    }
}
