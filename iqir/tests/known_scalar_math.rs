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

fn result(body: &str) -> ScalarValue {
    let program = parse(body);
    program
        .body
        .statements
        .iter()
        .find_map(|s| match &s.kind {
            StatementKind::ScalarDeclare {
                name,
                initializer: Some(e),
                ..
            } if name == "result" => Some(e.constant_value().unwrap().unwrap()),
            _ => None,
        })
        .unwrap()
}

#[test]
fn propagates_assignments_nested_calls_casts_and_gate_parameters() {
    assert_eq!(
        result(
            "float[64] a=0.0; a += 1.0; float[64] b=a*2.0; b=b/2.0; float[64] result=arccos(b);"
        ),
        ScalarValue::Float64(0)
    );
    assert_eq!(
        result("float[64] a=0.0; float[64] b=exp(a); float[64] result=arcsin(log(b));"),
        ScalarValue::Float64(0)
    );
    assert_eq!(
        result("int[64] k=3; k+=2; float[64] result=arccos(float[64](k)/5.0);"),
        ScalarValue::Float64(0)
    );
    assert_eq!(
        result("float[64] a=1.75; int[8] result=int[8](floor(a));"),
        ScalarValue::Integer(1)
    );
    parse("float[64] a=1.0; qubit q; ry(arccos(a)) q; a=0.0; rz(arcsin(a)) q;");
    parse("int[8] n=0; qubit q; rx(n) q;");
    parse(
        "float[64] a=0.0; for int i in [0:2] { a=a+1.0; float[64] b=sin(float[64](i)); } float[64] result=arccos(a/3.0);",
    );
}

#[test]
fn branch_meets_shadowing_and_read_only_loop_facts() {
    assert_eq!(
        result("float[64] a=0.0; if(true){a=1.0;} float[64] result=arccos(a);"),
        ScalarValue::Float64(0)
    );
    assert_eq!(
        result("bool b; float[64] a=0.0; if(b){a=1.0;}else{a=1.0;} float[64] result=arccos(a);"),
        ScalarValue::Float64(0)
    );
    assert_eq!(
        result(
            "float[64] a=1.0; if(true){float[64] a=0.0; float[64] local=arcsin(a);} float[64] result=arccos(a);"
        ),
        ScalarValue::Float64(0)
    );
    parse(
        "bool b; float[64] a=1.0; while(b){ float[64] rotation=arccos(a); } float[64] result=arccos(a);",
    );
    parse("bool b; float[64] a; while(b){ a=1.0; float[64] rotation=arccos(a); }");
}

#[test]
fn integer_masks_and_specialized_predicates_feed_constant_math() {
    for body in [
        "int[32] mask=5 & 3; float[64] a=0.0; if(mask==1){a=1.0;}else{a=-1.0;} float[64] result=arccos(a);",
        "def marked(int[32] value)->bool {return (value & 2)!=0;} float[64] a=0.0; if(marked(2)){a=1.0;} float[64] result=arccos(a);",
        "def cut(int[32] v)->bool {int[32] count=0; count += (v >> 0) % 2 ^ (v >> 1) % 2; return count==1;} float[64] a=0.0; if(cut(1)){a=1.0;} float[64] result=arccos(a);",
        // binary32 rounds a+1 back to a; evaluating the test as exact reals
        // or binary64 would select the wrong branch.
        "float[32] a=16777216.0; float[32] one=1.0; float[64] b=0.0; if(a+one==a){b=1.0;} float[64] result=arccos(b);",
    ] {
        assert_eq!(result(body), ScalarValue::Float64(0), "{body}");
    }
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

#[test]
fn folding_retains_float32_rounding_integer_division_and_signed_zero() {
    assert_eq!(
        result("float[32] a=2.0; float[64] result=sqrt(a);"),
        ScalarValue::Float64((f32::from_bits(0x3fb504f3) as f64).to_bits())
    );
    assert_eq!(
        result("int[32] a=3; int[32] b=5; float[64] result=arccos(a/b);"),
        ScalarValue::Float64(std::f64::consts::FRAC_PI_2.to_bits())
    );
    assert_eq!(
        result("float[64] a=-0.0; float[64] result=sin(a);"),
        ScalarValue::Float64((-0.0f64).to_bits())
    );
}

#[test]
fn does_not_invent_constants_at_joins_back_edges_or_in_const_contexts() {
    for body in [
        "float[64] a; float[64] result=arccos(a);",
        "bool b; float[64] a=0.0; if(b){a=1.0;} float[64] result=arccos(a);",
        "bool b; float[64] a=1.0; while(b){float[64] angle_value=arccos(a); a=0.0;}",
        "bool b; float[64] a=1.0; while(b){float[64] angle_value=arccos(a); a-=0.25;}",
        "bool b; float[64] a=1.0; while(arccos(a)>0.0){a=0.0;}",
        "bool b; float[64] a=1.0; while(b){if(b){a=0.0;}} float[64] result=arccos(a);",
    ] {
        let program = parse(body);
        // Import succeeds, but unknown values must retain an arccos operation.
        assert!(format!("{program:?}").contains("Acos"), "{body}");
    }
    for body in [
        "bool b; float[64] a=0.0; if(b){a=1.0;}else{float[64] result=arccos(2.0-a);}",
        "float[64] a=1.0; const float[64] result=arccos(a);",
        "float[64] a=2.0; float[64] result=arccos(a);",
        "float[64] a=128.0; int[8] result=int[8](a);",
        "bool b; float[64] a=0.0; if(b){a=-0.0;} float[64] result=cos(a);",
    ] {
        assert!(
            frontend::parse_str(&format!("OPENQASM 3; {body}"), "bad.qasm").is_err(),
            "{body}"
        );
    }
}
