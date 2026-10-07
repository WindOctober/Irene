use iqir::annotation::*;

fn span() -> SourceSpan {
    SourceSpan {
        source: "helpers.qasm".into(),
        start: 0,
        end: 0,
    }
}
fn define(table: &mut Vec<SpecFunction>, text: &str) -> Result<FunctionId, FunctionError> {
    define_function(table, parse_function(text, span()).unwrap())
}
fn check(text: &str, table: &[SpecFunction]) -> Result<SpecExpr, FunctionError> {
    let mut e = parse_expression(text).unwrap();
    check_expression(&mut e, table, |n| Err(format!("unbound {n}")))?;
    Ok(e)
}

#[test]
fn benchmark_classical_formula_families_parse_and_typecheck() {
    let mut f = Vec::new();
    // DGS: factorial sequence, finite remainder, piecewise truncation, infinite tail.
    for definition in [
        "pragma saria.def a(n: int) -> float = 1 / (2*n)!",
        "pragma saria.def remaining(n: int) -> float = cosh(1) - sum(j in 0..n, a(j))",
        "pragma saria.def stop(n: int) -> float = n >= 5 ? 1 : a(n)/remaining(n)",
        "pragma saria.def per_run(n: int) -> float = a(n)*(1+4^(-n))/(2*cosh(1))",
        "pragma saria.def tail(n: int) -> float = sum(j in n..inf, a(j)/cosh(1))",
        // QQBF and RUS: geometric tails, real specialization of abs products.
        "pragma saria.def geometric(k: uint) -> float = 2^(-k)",
        "pragma saria.def success(x: float, y: float) -> float = (1+abs(x*y)^2)/((1+abs(x)^2)*(1+abs(y)^2))",
        // Two-projector rewinding and DQE waiting time.
        "pragma saria.def rewind(n: int) -> float = n == 0 ? 1 : (1/4)*(5/8)^(n-1)",
        "pragma saria.def wait(n: uint, p: float) -> float = (1-p^n)/((1-p)*p^n)",
        // Universal rewinding: generalized binomial and Catalan forms.
        "pragma saria.def catalan(k: uint) -> float = binom(2*k,k)/(k+1)",
        "pragma saria.def hitting(m: int) -> float = (-1)^(m+1)*binom(1/2,m)",
        "pragma saria.def polynomial(n: uint) -> float = n^(-1/2)",
        // Sequential QHT: threshold, quantified event, real-valued supremum.
        "pragma saria.def rejection(lam: float, alpha: float) -> bool = lam >= 1/alpha",
        "pragma saria.def crossing(alpha: float) -> bool = exists(t in 0..inf, 0.5^t >= 1/alpha)",
        "pragma saria.def worst(alpha: float) -> float = sup(p: float in 0..=1, p*alpha)",
        // General classical terms from derivations.
        "pragma saria.def angle_of(p: float) -> angle = 2*asin(sqrt(p))",
        "pragma saria.def finite_product(n: uint) -> float = product(j in 1..=n, j/(j+1))",
        "pragma saria.def contract(n: int) -> bool = forall(j in 0..n, j >= 0 => a(j) > 0)",
        "pragma saria.def rounding(x: float) -> int = floor(x) + ceil(x)",
        "pragma saria.def parity(n: int) -> bool = n % 2 == 0",
    ] {
        define(&mut f, definition).unwrap_or_else(|e| panic!("{definition}: {e}"));
    }
    for expression in [
        "stop(0) > 0 && stop(5) == 1",
        "wait(3, 0.5) == 14",
        "geometric(2) == 1/4",
        "catalan(2) == 2",
        "hitting(2) == 1/8",
        "tail(5) < 2e-7",
        "rewind(1) == 1/4",
        "probability(true) <= 1",
        "expectation(2) == 2",
        "expectation(1) < inf",
        "sum(k in 0..inf, rewind(k)) == 5/3",
        "contract(5)",
        "rounding(0.5) == 1",
        "min(1,2,3) == 1",
        "max(1,2) == 2",
        "ln(exp(1)) == 1",
        "[1,2,3][0] == 1",
    ] {
        check(expression, &f).unwrap_or_else(|e| panic!("{expression}: {e}"));
    }
    // These tests check structure/types, not the truth of any displayed equality.
}

#[test]
fn definitions_are_pure_ordered_and_checked() {
    let mut table = Vec::new();
    define(&mut table, "pragma saria.def base(x: int) -> int = x+1").unwrap();
    for invalid in [
        "pragma saria.def base(x: int) -> int = x",
        "pragma saria.def sin(x: float) -> float = x",
        "pragma saria.def duplicate(x: int, x: int) -> int = x",
        "pragma saria.def recursive(n: int) -> int = recursive(n-1)",
        "pragma saria.def forward(n: int) -> int = later(n)",
        "pragma saria.def capture(n: int) -> int = n + global",
        "pragma saria.def wrong(n: int) -> bool = n+1",
        "pragma saria.def wrong(n: bool) -> int = n+1",
        "pragma saria.def wrong(n: float) -> float = n!",
        "pragma saria.def wrong(n: int) -> bool = sum(j in 0..n, true)",
        "pragma saria.def wrong(n: int) -> bool = forall(j in 0..n, j+1)",
        "pragma saria.def wrong(n: int) -> int = sum(j: float in 0..n, j)",
        "pragma saria.def wrong(n: int) -> int = sum(j in 0.5..n, j)",
        "pragma saria.def wrong(n: int) -> float = binom(n, 0.5)",
    ] {
        assert!(define(&mut table, invalid).is_err(), "accepted {invalid}");
        assert_eq!(table.len(), 1);
    }
    for bad in [
        "base()",
        "base(1,2)",
        "base(true)",
        "base(0.5)",
        "missing(1)",
        "true+1",
        "1 && 2",
        "probability(1)",
        "1 ? 2 : 3",
        "true ? false : 1",
        "1.5!",
        "true[0]",
    ] {
        assert!(check(bad, &table).is_err(), "accepted {bad}");
    }
    // A nonnegative domain is a later obligation, not a parser theorem.
    define(&mut table, "pragma saria.def natural(n: uint) -> uint = n").unwrap();
    assert!(check("natural(-1)", &table).is_ok());
}

#[test]
fn helper_substitution_is_symbolic_and_capture_avoiding() {
    let mut table = Vec::new();
    let id = define(
        &mut table,
        "pragma saria.def f(x: int) -> int = sum(j in 0..3, x+j)",
    )
    .unwrap();
    let body = instantiate_function(&table, id, &[SpecExpr::BoundVariable(0)]).unwrap();
    let SpecExpr::Binder {
        id: Some(local),
        body,
        ..
    } = body
    else {
        panic!()
    };
    assert_ne!(local, 0);
    let SpecExpr::Binary { left, right, .. } = *body else {
        panic!()
    };
    assert_eq!(*left, SpecExpr::BoundVariable(0));
    assert_eq!(*right, SpecExpr::BoundVariable(local));
    let shadow = define(
        &mut table,
        "pragma saria.def shadow(j: int) -> int = sum(j in 0..j, j)",
    )
    .unwrap();
    let value = parse_expression("5").unwrap();
    let body = instantiate_function(&table, shadow, std::slice::from_ref(&value)).unwrap();
    let SpecExpr::Binder { upper, body, .. } = body else {
        panic!()
    };
    assert_eq!(*upper, value);
    assert!(matches!(*body, SpecExpr::BoundVariable(_)));
}

#[test]
fn scalar_signatures_and_parameter_shadowing_are_explicit() {
    let mut table = Vec::new();
    for definition in [
        "pragma saria.def flag(x: bool) -> bool = !x",
        "pragma saria.def cell(x: bit) -> bit = x",
        "pragma saria.def turn(x: angle) -> angle = x/2",
        "pragma saria.def constant() -> float = sqrt(2)",
        "pragma saria.def shadow_pi(pi: int) -> int = pi+1",
    ] {
        define(&mut table, definition).unwrap();
    }
    for expression in [
        "flag(false)",
        "cell(true)",
        "turn(1) == 0.5",
        "constant() > 1",
        "shadow_pi(2) == 3",
    ] {
        check(expression, &table).unwrap();
    }
    assert!(
        matches!(&table[4].body, SpecExpr::Binary { left, .. } if matches!(left.as_ref(), SpecExpr::Parameter(0)))
    );
}

#[test]
fn precedence_ranges_and_errors_are_owned_by_the_grammar() {
    for good in [
        "sum(j in 0..5, j!)",
        "sum(j in 0..=5, j!)",
        "forall(n in 0..inf, n >= 0)",
        "n!=x",
        "n!>=x",
        "-2**2",
        "2^-3",
        "true?1:false?2:3",
        "infimum(x: float in -1..1, x^2)",
    ] {
        parse_expression(good).unwrap_or_else(|e| panic!("{good}: {e}"));
    }
    for bad in [
        "sum(j in 0..5 j)",
        "sum(j inx..5, j)",
        "forall(j 0..5, true)",
        "1 +",
        "f(,)",
        "1 ? 2",
        "n >>> 2",
        "1..5",
        "0 <= n <= 5",
        "@saria.invariant true",
        "1e999999",
    ] {
        assert!(parse_expression(bad).is_err(), "accepted {bad}");
    }
    let e = parse_expression("0 <= n && n <= 5").unwrap();
    assert!(matches!(
        e,
        SpecExpr::Binary {
            op: BinaryOp::And,
            ..
        }
    ));
    let error = parse_expression("n + )").unwrap_err();
    assert_eq!(error.offset, 4);
    assert!(parse_expression(&format!("{}true", "true => ".repeat(300))).is_err());
}
