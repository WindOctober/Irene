use iqir::{
    ScalarArithmetic as A, ScalarType as T, ScalarValue as V, StatementKind as K, frontend,
};

fn parse(body: &str) -> iqir::Program {
    let p = frontend::parse_str(
        &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
        "powers.qasm",
    )
    .unwrap();
    let mut ids = Vec::new();
    p.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort();
    assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
    p
}

fn value(body: &str) -> V {
    let p = parse(body);
    let K::ScalarDeclare {
        initializer: Some(e),
        ..
    } = &p.body.statements[0].kind
    else {
        panic!("initializer")
    };
    e.constant_value().unwrap().unwrap()
}

#[test]
fn integer_and_float_powers_keep_types_and_right_associativity() {
    for (text, answer) in [
        ("2 ** (3 ** 2)", 512),
        ("2 ** 3 ** 2", 512),
        ("2 ** 3 + 1", 9),
        ("1 + 2 ** 3", 9),
        ("2 * 3 ** 2", 18),
        ("2 ** 3 * 4", 32),
        ("-2 ** 2", -4),
        ("(-2) ** 2", 4),
        ("(2 ** 3) ** 2", 64),
        ("(-2) ** 3", -8),
        ("0 ** 0", 1),
    ] {
        assert_eq!(
            value(&format!("int[32] result = {text};")),
            V::Integer(answer)
        );
    }
    for (text, answer) in [
        ("16.0 ** 0.25", 2.0f64),
        ("2.0 ** -3.0", 0.125),
        ("2.0 ** -3.0 ** 2", 0.001953125),
        ("-2.0 ** 2", -4.0),
        ("(-2.0) ** 3", -8.0),
        ("(3 / 5) ** 2.0", 0.0),
        ("(-0.0) ** 2", 0.0),
    ] {
        assert_eq!(
            value(&format!("float[64] result = {text};")),
            V::Float64(answer.to_bits())
        );
    }
    assert_eq!(
        value("const float[32] a = 2.0; float[32] result = a ** float[32](0.5);"),
        V::Float32(0x3fb504f3)
    );
    parse("qubit q; ry(0.5 ** 2) q; rz(2 ** 3) q;");
    parse("const int[32] k=3; qubit[2 ** (k-1)] q;");
    parse(
        "float[64] base_value=0.3; float[64] result=base_value ** 2; int[8] a=2; int[8] b=a ** 3;",
    );
    parse("qubit[2 ** 2 + 1] q; ry(0.5 ** 2 + 0.25) q[0];");
}

#[test]
fn integer_powers_wrap_or_check_overflow_without_unbounded_expansion() {
    let unsigned = T::Int {
        width: 8,
        signed: false,
    };
    let signed = T::Int {
        width: 8,
        signed: true,
    };
    assert_eq!(unsigned.checked_integer_arithmetic(A::Pow, 3, 6), Ok(217));
    assert_eq!(unsigned.checked_integer_arithmetic(A::Pow, 0, 0), Ok(1));
    assert_eq!(signed.checked_integer_arithmetic(A::Pow, -2, 7), Ok(-128));
    assert!(signed.checked_integer_arithmetic(A::Pow, 2, 7).is_err());
    assert!(signed.checked_integer_arithmetic(A::Pow, 2, -1).is_err());
    assert_eq!(
        T::Int {
            width: 2,
            signed: true
        }
        .checked_integer_arithmetic(A::Pow, -1, 1),
        Ok(-1)
    );
    assert_eq!(
        T::Int {
            width: 64,
            signed: false
        }
        .checked_integer_arithmetic(A::Pow, 3, u64::MAX as i128),
        Ok(12297829382473034411)
    );
    assert!(
        frontend::parse_str("OPENQASM 3; const float[64] x=(-2.0)**0.25;", "bad.qasm").is_err()
    );
}
