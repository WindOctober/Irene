use iqir::{annotation::*, frontend};

#[test]
fn specification_pi_is_real_but_decimal_math_remains_machine_typed() {
    for (source, expected) in [
        (r"\pi", SpecType::Real),
        (r"\sin(\pi)", SpecType::Real),
        (r"\sin(0.5)", SpecType::Float(None)),
    ] {
        let mut e = parse_expression(source).unwrap();
        assert_eq!(
            check_expression(&mut e, &[], |_| unreachable!()).unwrap(),
            expected
        );
    }
}

#[test]
fn absolute_value_preserves_width_and_complex_magnitude_is_real() {
    for (source, input, expected) in [
        (r"\abs(x)", SpecType::Int(Some(8)), SpecType::Uint(Some(8))),
        (
            r"\abs(x)",
            SpecType::Uint(Some(64)),
            SpecType::Uint(Some(64)),
        ),
        (
            r"\abs(x)",
            SpecType::Float(Some(32)),
            SpecType::Float(Some(32)),
        ),
        (r"\abs(3+4*\i)", SpecType::Real, SpecType::Real),
        (
            r"\sin(x)",
            SpecType::Float(Some(32)),
            SpecType::Float(Some(32)),
        ),
        (
            r"\atan(x)",
            SpecType::Float(Some(64)),
            SpecType::Float(Some(64)),
        ),
    ] {
        let mut e = parse_expression(source).unwrap();
        assert_eq!(
            check_expression(&mut e, &[], |_| Ok((SpecExpr::BoundVariable(0), input))).unwrap(),
            expected,
            "{source}"
        );
    }
}

#[test]
fn machine_math_keeps_explicit_formats_and_promotes_mixed_powers() {
    use SpecType::{Complex, Float, Int, Real, Uint};
    let infer = |source: &str, x: SpecType, y: SpecType| {
        let mut e = parse_expression(source).unwrap();
        check_expression(&mut e, &[], |name| match name {
            "x" => Ok((SpecExpr::BoundVariable(0), x)),
            "y" => Ok((SpecExpr::BoundVariable(1), y)),
            _ => Err(format!("unexpected name {name}")),
        })
    };
    for width in [32, 64] {
        let t = Float(Some(width));
        for source in [
            "x ^ 2", "x ^ y",
            r"\re(x)", r"\im(x)", r"\abs(x)", r"\binom(x, 2)",
            r"\sin(x)", r"\sqrt(x)", r"\atan(x)",
            r"\sin(\re(x))", r"\re(x) + x", r"\binom(x, 2) ^ 2",
        ] {
            assert_eq!(infer(source, t, t).unwrap(), t, "{source}: {t:?}");
        }
        // An integer exponent/count must not promote a float32 base to float64.
        for source in ["x ^ y", r"\binom(x, y)"] {
            assert_eq!(infer(source, t, Int(Some(64))).unwrap(), t);
        }
        // Decimal syntax already carries a default binary64 cast. Unlike the
        // integer literal above, it must participate in mixed-format promotion.
        assert_eq!(infer("x ^ 0.5", t, t).unwrap(), Float(Some(64)));
    }
    for (x, y, expected) in [
        (Float(Some(32)), Float(Some(64)), Float(Some(64))),
        (Float(Some(64)), Float(Some(32)), Float(Some(64))),
        (Float(Some(32)), Float(None), Float(Some(64))),
        (Int(Some(64)), Float(Some(32)), Float(Some(32))),
        (Real, Float(Some(32)), Real),
        (Float(Some(32)), Real, Real),
        (Int(Some(8)), Int(Some(32)), Int(Some(8))),
        (Uint(Some(8)), Int(Some(32)), Uint(Some(8))),
        (Complex, Int(Some(32)), Complex),
    ] {
        assert_eq!(infer("x ^ y", x, y).unwrap(), expected, "{x:?}, {y:?}");
    }
    for source in [r"\re(x)", r"\im(x)", r"\binom(x, 2)"] {
        assert_eq!(infer(source, Real, Int(None)).unwrap(), Real);
    }
    for source in [r"\re(x)", r"\im(x)", r"\abs(x)"] {
        assert_eq!(infer(source, Complex, Int(None)).unwrap(), Real);
    }
    assert_eq!(infer(r"\re(x)", Float(None), Int(None)).unwrap(), Float(None));
    assert!(infer(r"\binom(x, y)", Float(Some(32)), Float(Some(32))).is_err());
    assert!(infer(r"\binom(x, y)", Real, Real).is_err());
}

#[test]
fn mathematical_helpers_and_aggregates_have_real_results() {
    let p = frontend::parse_str(
        r"OPENQASM 3;
pragma saria.def coefficient(k: uint[8]) -> real = \real(1)/\factorial(2*k)
pragma saria.def partial(n: uint[8]) -> real = \sum(k: uint[8] in 0..n, coefficient(k))
@saria.assert \abs(\cosh(\real(1))-partial(5)) < \real(1)/1000000
",
        "real.qasm",
    )
    .unwrap();
    assert!(p.spec_functions.iter().all(|f| f.result == SpecType::Real));
}

#[test]
fn real_does_not_replace_machine_storage_or_round_implicitly() {
    for body in [
        "@saria.ghost x: real = 1\nqubit q;",
        "pragma saria.def f() -> real[64] = 1",
        r"pragma saria.def f() -> float = \cosh(\real(1))",
        r"@saria.assert \factorial(0.5) > 0",
        r"pragma saria.def f(x: angle) -> real = \min(x, \real(1))",
    ] {
        assert!(
            frontend::parse_str(&format!("OPENQASM 3;\n{body}"), "real.qasm").is_err(),
            "{body}"
        );
    }
}

#[test]
fn lifting_preserves_the_source_machine_type() {
    let mut e = parse_expression(r"\real(0.1)").unwrap();
    assert_eq!(
        check_expression(&mut e, &[], |_| unreachable!()).unwrap(),
        SpecType::Real
    );
    let SpecExpr::Cast {
        ty: SpecType::Real,
        operand,
    } = e
    else {
        panic!("missing lift")
    };
    assert!(matches!(
        *operand,
        SpecExpr::Cast {
            ty: SpecType::Float(None),
            ..
        }
    ));
}
