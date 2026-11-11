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
    // Mutable reads remain storage operations; execution folds their values.
    assert!(p.body.statements.iter().any(|s| matches!(&s.kind, StatementKind::ScalarDeclare {name, initializer: Some(e), ..} if name=="result" && e.constant_value().unwrap().is_none())));
    let mut ids = vec![];
    p.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort();
    assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
}

#[test]
fn const_arrays_and_runtime_scalar_reads() {
    parse("const array[float[32],2] phases={0.1,0.2}; int[8] i; float[32] f; f=phases[i]; f=phases[0];").unwrap();
    parse("const array[int[8],2] a={2,3}; const int[8] b=a[0]; array[int[8],2] c; c[0]=b; c[1]=c[0]+1; c[0]+=1; if(c[1]==3){c[0]=0;}").unwrap();
    parse("array[float[32],2] a={1.0,2.0}; float[64] result=sqrt(a[1]);").unwrap();
    parse("array[int[8],2,2] a={{1,2},{3,4}}; int[8] result=a[1][0];").unwrap();
    parse("const array[float[64],1] a={0.0}; def f(qubit q){ry(a[0]) q;} qubit q; f(q);").unwrap();
}

#[test]
fn immutable_tables_preserve_typed_reads_and_scope() {
    let p = parse("const array[float[32],2] a={-0.0,0.1}; int[8] i; float[32] first=a[i]; float[32] second=a[i];").unwrap();
    let reads = p.body.statements.iter().filter_map(|s| match &s.kind {
        StatementKind::ScalarDeclare { initializer: Some(e), .. } => match &e.kind.kind {
            iqir::ScalarExprKind::TableRead { table, index } => Some((table, index)),
            _ => None,
        },
        _ => None,
    }).collect::<Vec<_>>();
    assert_eq!(reads.len(), 2);
    assert!(std::sync::Arc::ptr_eq(reads[0].0, reads[1].0));
    assert_eq!(reads[0].0.values(), &[ScalarValue::Float32((-0.0f32).to_bits()), ScalarValue::Float32(0.1f32.to_bits())]);
    let mut ids = vec![];
    p.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort();
    assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
    for body in [
        "const array[int[8],2] a={1,2}; int[8] b=a[-1];",
        "const array[int[8],2] a={1,2}; int[8] b=a[2];",
        "const array[int[8],2] a={1,2}; float[64] i; int[8] b=a[i];",
        "const array[int[8],2] a={1,2}; int[8] i; a[i]=0;",
        "def f(int[8] i) -> float[64] { return a[i]; } const array[float[64],2] a={0.1,0.2}; float[64] result=f(0);",
    ] {
        assert!(parse(body).is_err(), "{body}");
    }
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
fn mutable_array_element_specifications_are_typed() {
    let program = parse("array[int[8],2] a={1,2}; a[0]=2;\n@saria.assert a[0] == 2\n").unwrap();
    assert_eq!(program.annotations.len(),1);
}

#[test]
fn readonly_arrays_share_tables_without_acquiring_const_qualification() {
    let p = parse("array[float[32],2] a={-0.0,0.1}; int[8] i; float[32] first=a[i]; float[32] second=a[i];\n@saria.assert a[0] == -0.0\n").unwrap();
    let tables = p.body.statements.iter().filter_map(|s| match &s.kind {
        StatementKind::ScalarDeclare { initializer: Some(e), .. } => match &e.kind.kind {
            iqir::ScalarExprKind::TableRead { table, .. } => Some(table),
            _ => None,
        },
        _ => None,
    }).collect::<Vec<_>>();
    assert_eq!(tables.len(), 2);
    assert!(std::sync::Arc::ptr_eq(tables[0], tables[1]));
    assert_eq!(tables[0].values(), &[ScalarValue::Float32((-0.0f32).to_bits()), ScalarValue::Float32(0.1f32.to_bits())]);
    assert!(parse("array[int[8],2] a={1,2}; const int[8] x=a[0];").is_err());
    // Array optimization must not allow mutable global captures or forward visibility.
    assert!(parse("def f(int[8] i) -> int[8] { return a[i]; } array[int[8],2] a={1,2}; int[8] x=f(0);").is_err());
}

#[test]
fn readonly_table_inference_rejects_writes_unknown_values_and_escapes() {
    for source in [
        "array[int[8],2] a={1,2}; int[8] i; int[8] x=a[i]; a[0]=3;",
        "array[int[8],2] a={1,2}; bit b; if(b){a[0]+=1;} int[8] i; int[8] x=a[i];",
        "array[int[8],2] a={1,2}; bit b; int[8] i; while(b){int[8] x=a[i]; a[1]=3;}",
        "int[8] v; array[int[8],2] a={1,v}; int[8] i; int[8] x=a[i];",
        "array[int[8],2] a; int[8] i; int[8] x=a[i];",
        "array[int[8],2] a={1,2}; let alias = a; int[8] i; int[8] x=a[i];",
        "array[int[8],2] a={1,2}; int[8] x=a[2];",
    ] { assert!(parse(source).is_err(), "{source}"); }
}

#[test]
fn multidimensional_tables_check_axes_before_flattening() {
    use iqir::{ScalarExprKind as E, SymbolId};
    for qualifier in ["const ", ""] {
        let p = parse(&format!("{qualifier}array[float[32],2,3] a={{{{0.0,0.1,0.2}},{{0.3,0.4,0.5}}}}; int[8] i; int[8] j; float[32] result=a[i,j];")).unwrap();
        let id = |name: &str| p.body.statements.iter().find_map(|s| match &s.kind {
            StatementKind::ScalarDeclare { id, name: found, .. } if found == name => Some(*id), _ => None,
        }).unwrap();
        let (i, j) = (id("i"), id("j"));
        let expression = p.body.statements.iter().find_map(|s| match &s.kind {
            StatementKind::ScalarDeclare { name, initializer: Some(e), .. } if name == "result" => Some(e), _ => None,
        }).unwrap();
        assert!(matches!(expression.kind.kind, E::TableRead { .. }));
        let evaluate = |row, column| expression.constant_value_with(&|id: SymbolId| {
            if id == i { Some(ScalarValue::Integer(row)) }
            else if id == j { Some(ScalarValue::Integer(column)) } else { None }
        });
        assert_eq!(evaluate(1, 2).unwrap(), Some(ScalarValue::Float32(0.5f32.to_bits())));
        assert!(evaluate(0, 3).is_err(), "column overflow must not alias next row");
        assert!(evaluate(-1, 2).is_err());
        assert!(evaluate(2, 0).is_err());
    }
}

#[test]
fn finite_runtime_write_checks_address_and_evaluates_rhs_once() {
    use iqir::ScalarExprKind as E;
    let p = parse("array[int[8],2,2] a; int[8] i; int[8] j; def value() -> int[8] {return 7;} a[i,j]=value(); int[8] result=a[0,0];").unwrap();
    let block = p.body.statements.iter().find_map(|s| match &s.kind {
        StatementKind::Scope(b) => Some(b), _ => None,
    }).unwrap();
    assert_eq!(block.statements.len(), 4, "address, result storage, one call, dispatch");
    let StatementKind::ScalarDeclare { initializer: Some(offset), .. } = &block.statements[0].kind else { panic!("checked address") };
    assert!(matches!(offset.kind.kind, E::Binary { .. }));
    assert!(matches!(block.statements[3].kind,StatementKind::ArrayStore {..}));
    assert!(!block.statements.iter().any(|s|matches!(s.kind,StatementKind::If {..})));
    let mut ids = vec![]; p.visit_ast_ids(|id| ids.push(id.index())); ids.sort();
    assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
    assert!(parse("const array[int[8],2] a={0,1}; int[8] i; a[i]=2;").is_err());
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
