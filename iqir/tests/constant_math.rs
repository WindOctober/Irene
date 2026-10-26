use iqir::{Gate, NumericExprKind, Program, ScalarValue, StatementKind, frontend};

fn parse(body: &str) -> Program {
    let p = frontend::parse_str(
        &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
        "math.qasm",
    )
    .unwrap();
    let mut ids = Vec::new();
    p.visit_ast_ids(|id| ids.push(id.index()));
    let count = ids.len();
    ids.sort();
    ids.dedup();
    assert_eq!(count, ids.len());
    assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
    p
}

fn value(body: &str) -> ScalarValue {
    let p = parse(body);
    let StatementKind::ScalarDeclare {
        initializer: Some(e),
        ..
    } = &p.body.statements[0].kind
    else {
        panic!("expected scalar initializer")
    };
    e.constant_value().unwrap().unwrap()
}

#[test]
fn folds_all_functions_and_nested_calls() {
    for (expression, expected) in [
        ("sin(0.0)", 0.0),
        ("cos(0.0)", 1.0),
        ("tan(0.0)", 0.0),
        ("arcsin(0.0)", 0.0),
        ("arccos(1.0)", 0.0),
        ("arctan(0.0)", 0.0),
        ("sqrt(4.0)", 2.0),
        ("exp(0.0)", 1.0),
        ("log(1.0)", 0.0),
        ("floor(-1.25)", -2.0),
        ("ceiling(-1.25)", -1.0),
        ("sqrt(exp(1.0))", f64::from_bits(0x3ffa61298e1e069c)),
    ] {
        assert_eq!(
            value(&format!("float[64] result = {expression};")),
            ScalarValue::Float64(expected.to_bits())
        );
    }
    assert_eq!(
        value("const float[64] a = sqrt(exp(1.0)); float[64] result = a;"),
        ScalarValue::Float64(0x3ffa61298e1e069c)
    );
    assert_eq!(
        value("float[64] result = sin(-0.0);"),
        ScalarValue::Float64((-0.0f64).to_bits())
    );
    assert_eq!(
        value("float[64] result = exp(-1000.0);"),
        ScalarValue::Float64(0)
    );
}

#[test]
fn rounds_each_call_at_its_argument_precision_before_assignment() {
    assert_eq!(
        value("float[64] result = sqrt(float[32](2.0));"),
        ScalarValue::Float64((f32::from_bits(0x3fb504f3) as f64).to_bits())
    );
    assert_eq!(
        value("float[64] result = exp(log(float[32](2.0)));"),
        ScalarValue::Float64(2.0f64.to_bits())
    );
    assert_eq!(
        value("float[32] result = exp(float[32](-100.0));"),
        ScalarValue::Float32(27)
    );
    assert_eq!(
        value("float[64] result = arccos(3/5);"),
        ScalarValue::Float64(std::f64::consts::FRAC_PI_2.to_bits())
    );
}

#[test]
fn explicit_closed_float_to_integer_casts_are_separate_and_checked() {
    assert_eq!(
        value("const int[64] n = int[64](floor(log(8.0)/log(2.0))) + 1; int[64] result = n;"),
        ScalarValue::Integer(4)
    );
    assert_eq!(
        value("int[8] result = int[8](ceiling(-1.25));"),
        ScalarValue::Integer(-1)
    );
    assert_eq!(
        value("int[8] result = int[8](-1.75);"),
        ScalarValue::Integer(-1)
    );
    assert_eq!(
        value("const uint[64] v = uint[64](9223372036854775808.0); float[64] result = v;"),
        ScalarValue::Float64(9223372036854775808.0f64.to_bits())
    );
}

#[test]
fn gate_parameters_receive_the_rounded_binary_value() {
    let p = parse("qubit q; ry(arccos(1.0/sqrt(3.0))) q;");
    let StatementKind::Apply {
        gate: Gate::Ry,
        parameters,
        ..
    } = &p.body.statements[0].kind
    else {
        panic!()
    };
    let NumericExprKind::Rational(angle) = &parameters[0].kind else {
        panic!()
    };
    let ScalarValue::Float64(bits) = value("float[64] result = arccos(1.0/sqrt(3.0));") else {
        panic!()
    };
    assert_eq!(
        *angle,
        num_rational::BigRational::from_float(f64::from_bits(bits)).unwrap()
    );
    parse("gate prepare q { ry(pi * arccos(1.0/3.0)) q; } qubit q; prepare q;");
    parse("bit b; if (sqrt(4.0) == 2.0) { b = true; }");
}

#[test]
fn rejects_runtime_calls_invalid_types_domains_and_nonfinite_results() {
    for body in [
        "float[64] a; float[64] result=cos(a);",
        "float[64] a; qubit q; ry(cos(a)) q;",
        "float[64] result=sin();",
        "float[64] result=sin(1.0,2.0);",
        "float[64] result=sin(true);",
        "float[64] result=sqrt(-1.0);",
        "float[64] result=arccos(2.0);",
        "float[64] result=log(0.0);",
        "float[64] result=exp(1000.0);",
        "float[64] result=unknown(1.0);",
        "float[64] sin=0.0; float[64] result=sin(1.0);",
        "int[8] result=floor(1.0);",
        "int[8] result=int[8](128.0);",
        "const uint[64] result=uint[64](18446744073709551616.0);",
        "const uint[8] result=uint[8](-1.0);",
    ] {
        assert!(
            frontend::parse_str(
                &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
                "bad.qasm"
            )
            .is_err(),
            "{body}"
        );
    }
}
