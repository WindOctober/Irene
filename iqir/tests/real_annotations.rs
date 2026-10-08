use iqir::{annotation::*, frontend};

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
