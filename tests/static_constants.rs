mod common;

#[test]
fn block_constants_and_cast_widths_respect_scope() {
    let p = parse(
        "const int n=2; qubit[n] q;
        if(true) { const int n=1; x q[n]; } x q[n-1];",
    );
    assert_same(&p, &parse("qubit[2] q;"));
    assert_fresh_ids(&p);
    let p = parse(
        "const int n=2; qubit q; bit[n] c;
        bit[n] d=bit[n](c); if(uint[n](c)==0) x q;",
    );
    assert_fresh_ids(&p);
    assert_eq!(
        p.classical_registers
            .iter()
            .map(|r| r.width)
            .collect::<Vec<_>>(),
        vec![2, 2]
    );
    rejects("qubit q; if(true) { const int n=1; const int n=2; }");
}
use common::unitary::{assert_fresh_ids, assert_same};
use irene::frontend::openqasm3::parse_str;
use irene::ir::Program;

fn parse(body: &str) -> Program {
    parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
        "static-constants",
    )
    .unwrap()
}
fn rejects(body: &str) {
    assert!(
        parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
            "invalid-static"
        )
        .is_err(),
        "{body}"
    );
}

#[test]
fn constants_resolve_widths_indices_and_gate_parameters() {
    let p =
        parse("const int n=4; const int[8] j=n-1; qubit[n] q; bit[n/2] c; x q[j]; rz(pi/n) q[0];");
    assert_eq!(p.quantum_registers[0].width, 4);
    assert_eq!(p.classical_registers[0].width, 2);
    assert_fresh_ids(&p);
    let p = parse("const int n=4; const int[8] j=n-1; qubit[n] q; x q[j]; rz(pi/n) q[0];");
    assert_same(&p, &parse("qubit[4] q; x q[3]; rz(pi/4) q[0];"));
    // Constants used as register precision do not become numeric runtime inputs.
    let p = parse("const int n=8; input uint[n] k; input angle[n] a; qubit q;");
    assert_eq!(
        p.numeric_inputs[0].ty,
        irene::ir::NumericType::Uint(Some(8))
    );
    assert_eq!(
        p.numeric_inputs[1].ty,
        irene::ir::NumericType::Angle(Some(8))
    );
}

#[test]
fn integer_division_is_folded_before_angle_promotion() {
    for (expr, expected) in [
        ("(1/2)*pi", "0"),
        ("pi/2", "pi/2"),
        ("7/2", "3"),
        ("(-7)/2", "-3"),
        ("1.0+(7/2)", "4.0"),
        ("7/2.0", "3.5"),
    ] {
        assert_same(
            &parse(&format!("qubit q; p({expr}) q;")),
            &parse(&format!("qubit q; p({expected}) q;")),
        );
    }
    assert_same(
        &parse(
            "const int a=-7; const int b=3; const int d=a/b; const int r=a%b; qubit q; p(d) q; rz(r) q;",
        ),
        &parse("qubit q; p(-2) q; rz(-1) q;"),
    );
    for expr in ["1/0", "1/(2-2)", "0*(1/0)", "pi/(1/2)", "1.0+(1/0)"] {
        rejects(&format!("qubit q; p({expr}) q;"));
    }
}

#[test]
fn unsigned_arithmetic_checks_range_and_result() {
    for width in 1..=4 {
        let bound = 1_i128 << width;
        for a in 0..bound {
            for b in 0..bound {
                for (op, value) in [
                    ("+", a.checked_add(b)),
                    ("-", a.checked_sub(b)),
                    ("*", a.checked_mul(b)),
                    ("/", a.checked_div(b)),
                    ("%", a.checked_rem(b)),
                ] {
                    let body = format!(
                        "const uint[{width}] a={a}; const uint[{width}] b={b}; const uint[{width}] c=a{op}b;"
                    );
                    let admitted = value.is_some_and(|v| 0 <= v && v < bound);
                    if admitted {
                        let v = value.unwrap();
                        let p = parse(&format!("{body} qubit[c-{v}+1] q;"));
                        assert_eq!(p.quantum_registers[0].width, 1, "{body}");
                    } else {
                        rejects(&body);
                    }
                }
            }
        }
    }
    rejects("const uint[3] a=7; const uint[3] b=(a+1)-1;");
}

#[test]
fn signed_arithmetic_checks_range_and_result() {
    for width in 2..=4 {
        let bound = 1_i128 << (width - 1);
        for a in -bound..bound {
            for b in -bound..bound {
                for (op, value) in [
                    ("+", a.checked_add(b)),
                    ("-", a.checked_sub(b)),
                    ("*", a.checked_mul(b)),
                    ("/", a.checked_div(b)),
                    ("%", a.checked_rem(b)),
                ] {
                    let body = format!(
                        "const int[{width}] a={a}; const int[{width}] b={b}; const int[{width}] c=a{op}b;"
                    );
                    let admitted = value.is_some_and(|v| -bound <= v && v < bound)
                        && !(a == -bound && b == -1 && matches!(op, "/" | "%"));
                    if admitted {
                        let v = value.unwrap();
                        let p = parse(&format!("{body} qubit[c-({v})+1] q;"));
                        assert_eq!(p.quantum_registers[0].width, 1, "{body}");
                    } else {
                        rejects(&body);
                    }
                }
            }
        }
    }
}

#[test]
fn default_width_and_signed_boundaries_are_checked() {
    for body in [
        "const uint n=4294967295;",
        "const int n=2147483647;",
        "const int n=-2147483648;",
        "const uint[64] n=18446744073709551615;",
        "const int[64] n=-9223372036854775808;",
        "const int width=8; const uint[width] n=255;",
    ] {
        parse(body);
    }
    for body in [
        "const uint n=4294967296;",
        "const int n=2147483648;",
        "const int n=-2147483649;",
        "const int[32] n=-2147483648; const int m=-n;",
        "const int[32] n=-2147483648; const int m=n/-1;",
        "const uint n=-1;",
        "const int[65] n=0;",
        "const int a=-1; const uint b=2; const int c=a+b;",
    ] {
        rejects(body);
    }
}

#[test]
fn subroutine_constants_use_lexical_not_caller_scope() {
    let p = parse(
        "const int n=2; qubit[n] q;
        def f(qubit[n] a) { const int j=n-1; x a[j]; }
        def caller(qubit[n] a) { const int n=1; f(a); }
        caller(q); x q[n-1];",
    );
    assert_same(&p, &parse("qubit[2] q;"));
    assert_fresh_ids(&p);
    let p = parse(
        "const int n=2; qubit[n] q;
        def f(qubit[n] a) { const int n=1; x a[n]; }
        f(q); x q[n-1];",
    );
    assert_same(&p, &parse("qubit[2] q;"));
    for body in [
        "qubit[2] q; def f(qubit[2] a) { x a[n]; } const int n=1; f(q);",
        "qubit q; def f(qubit a) { rz(pi/n) a; } def g(qubit a) { const int n=2; f(a); } g(q);",
        "const int n=2; const int n=3;",
        "const int n=2; n=3;",
        "qubit q; if(true) { const int local=1; } rz(local) q;",
    ] {
        rejects(body);
    }
}

#[test]
fn runtime_values_cannot_determine_static_declarations() {
    for body in [
        "bit c; qubit[c] q;",
        "input int n; qubit[n] q;",
        "input int n; const int k=n;",
        "qubit q; bit c=measure q; const int n=int[1](c);",
        "const int n=0; qubit[n] q;",
        "const int n=-1; qubit[2] q; x q[n];",
        "const int n=2; qubit[n] q; x q[n];",
        "const int n=2; bit[n] c; qubit q; measure q -> c[n];",
    ] {
        rejects(body);
    }
    let p = parse("const int n=2; qubit q; bit[n] c; measure q -> c[n-1];");
    assert_fresh_ids(&p);
}

#[test]
fn gate_powers_use_the_same_checked_constant_evaluator() {
    let p = parse("const int[8] k=-3; qubit q; pow(k+1) @ t q;");
    assert_same(&p, &parse("qubit q; sdg q;"));
    assert_fresh_ids(&p);
    for body in [
        "const uint[2] k=3; qubit q; pow(k+1) @ x q;",
        "qubit q; bit c=measure q; pow(c) @ x q;",
    ] {
        rejects(body);
    }
}
