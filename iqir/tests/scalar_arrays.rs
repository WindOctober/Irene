use iqir::{ScalarValue, StatementKind, frontend};

fn parse(body: &str) -> Result<iqir::Program, String> {
    frontend::parse_str(
        &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
        "arrays.qasm",
    )
    .map_err(|e| e.to_string())
}

#[test]
fn cells_math_and_static_lookup() {
    let p = parse("array[float[64],2,2] a={{0.0,1.0},{2.0,3.0}}; a[0,0]=1.0; a[1,1]+=1.0; float[64] result=arccos(a[0,0]); qubit q; for int i in [0:1] { ry(a[i,1]) q; }").unwrap();
    assert!(p.body.statements.iter().any(|s| matches!(&s.kind, StatementKind::ScalarDeclare {name, initializer: Some(e), ..} if name=="result" && e.constant_value().unwrap()==Some(ScalarValue::Float64(0)))));
    let mut ids = vec![];
    p.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort();
    assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
}

#[test]
fn const_arrays_and_runtime_scalar_reads() {
    parse("const array[int[8],2] a={2,3}; const int[8] b=a[0]; array[int[8],2] c; c[0]=b; c[1]=c[0]+1; c[0]+=1; if(c[1]==3){c[0]=0;}").unwrap();
    parse("array[float[32],2] a={1.0,2.0}; float[64] result=sqrt(a[1]);").unwrap();
    parse("array[int[8],2,2] a={{1,2},{3,4}}; int[8] result=a[1][0];").unwrap();
    parse("const array[float[64],1] a={0.0}; def f(qubit q){ry(a[0]) q;} qubit q; f(q);").unwrap();
}

#[test]
fn rejects_unsupported_or_invalid_arrays() {
    for body in [
        "if (true) { array[int[8],1] a; }",
        "for int i in [0:1] { array[int[8],1] a; }",
        "def f() { array[int[8],1] a; } f();",
        "array[int[8],2] a={1};",
        "array[int[8],2,2] a={{1,2},{3}};",
        "array[int[8],0] a;",
        "array[int[8],4097] a;",
        "array[int[8],2] a; a[2]=0;",
        "array[int[8],2] a; a[-1]=0;",
        "array[int[8],2,2] a; a[0]=0;",
        "array[int[8],2] a; int i; a[i]=0;",
        "const array[int[8],2] a={1,2}; a[0]=0;",
        "const array[int[8],2] a={1,2}; a[0]+=1;",
        "array[int[8],2] a={1,2}; const int[8] b=a[0];",
        "array[int[8],2] a={1,a[0]};",
        "array[float[64],1] a={0.0}; bool b; while(b){ ry(a[0]) q; a[0]+=1.0;} qubit q;",
    ] {
        assert!(parse(body).is_err(), "unexpected success: {body}");
    }
}

#[test]
fn array_specifications_are_explicitly_out_of_scope() {
    let error = parse("array[int[8],2] a={1,2};\n@saria.assert a[0] == 1\n").unwrap_err();
    assert!(
        error.contains("array-valued specifications/invariants are not supported"),
        "{error}"
    );
}

#[test]
fn loop_and_branch_values_are_not_frozen() {
    fn dynamic(block: &iqir::Block) -> bool {
        block.statements.iter().any(|s| match &s.kind {
            iqir::StatementKind::Apply { parameters, .. } => parameters
                .iter()
                .any(|p| matches!(p.kind, iqir::NumericExprKind::Scalar(_))),
            iqir::StatementKind::While { body, .. } | iqir::StatementKind::Scope(body) => {
                dynamic(body)
            }
            _ => false,
        })
    }
    for source in [
        "qubit q; array[float[64],1] a={0.0}; bool b; while(b){ ry(a[0]) q; a[0]+=1.0; }",
        "qubit q; array[float[64],1] a={0.0}; bool b; if(b){a[0]=1.0;} ry(a[0]) q;",
    ] {
        assert!(dynamic(&parse(source).unwrap().body));
    }
    parse("qubit q; array[float[64],1] a={0.0}; bool b; while(b){ a[0]=1.0; ry(a[0]) q; }")
        .unwrap();
    parse("qubit q; array[float[64],1] a={0.0}; bool b; while(b){ ry(a[0]) q; }").unwrap();
}
