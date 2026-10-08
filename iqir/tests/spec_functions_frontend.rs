use iqir::frontend;

#[test]
fn qasm_import_keeps_function_ids_and_does_not_execute_definitions() {
    let p = frontend::parse_str(
        "OPENQASM 3; uint[8] n = 0; bool stop = false;\n\
        pragma saria.def a(k: int) -> float = 1 / (2*k)!\n\
        pragma saria.def r(k: int) -> float = a(k)/(\\cosh(1)-\\sum(j in 0..k, a(j)))\n\
        @saria.invariant n <= 5 && r(n) > 0\n\
        while (!stop) { stop = true; }",
        "helpers.qasm",
    )
    .unwrap();
    assert_eq!(p.spec_functions.len(), 2);
    assert_eq!(p.annotations.len(), 1);
    assert_eq!(p.body.statements.len(), 3);
    for tail in [
        "pragma saria.def f(x: int) -> int = n+x",
        "pragma saria.def f(x: qubit) -> int = 0",
        "pragma saria.def f(x: int[8]) -> int = x",
        "@saria.requires f(1) == 1\nreset q;\npragma saria.def f(x: int) -> int = x",
        "if (true) {\npragma saria.def f(x: int) -> int = x\n}",
        "def unused(qubit q) {\npragma saria.def f(x: int) -> int = x\n}",
        "@saria.invariant 1+2\nwhile (false) {}",
    ] {
        let source = format!("OPENQASM 3; uint n = 0; qubit q;\n{tail}");
        assert!(
            frontend::parse_str(&source, "bad.qasm").is_err(),
            "accepted {tail}"
        );
    }
}

#[test]
fn qasm_payload_preserves_quantifier_backslashes_and_semicolons() {
    use iqir::annotation::{AnnotationPayload, BinderKind, SpecExpr};
    let program = frontend::parse_str(
        r"OPENQASM 3;
uint[8] n = 5;
pragma saria.def witness(k: int) -> bool = \forall i in 0..k; \exists j in i..k; j >= i
pragma saria.def triangular(k: int) -> int = \sum(j in 0..=k, j)
@saria.invariant \forall i in 0..n; \exists j in i..n; j >= i && witness(n)
@saria.requires triangular(n) >= 0
while (n > 0) { n -= 1; }
",
        "quantifiers.qasm",
    )
    .unwrap();
    assert_eq!(program.spec_functions.len(), 2);
    assert_eq!(program.annotations.len(), 1);
    let annotations = program.annotations.values().next().unwrap();
    assert_eq!(annotations.len(), 2);
    let AnnotationPayload::Expression(SpecExpr::Binder {
        kind: BinderKind::Forall,
        id: Some(_),
        body,
        ..
    }) = &annotations[0].payload
    else {
        panic!("missing checked outer quantifier")
    };
    assert!(matches!(
        body.as_ref(),
        SpecExpr::Binder {
            kind: BinderKind::Exists,
            id: Some(_),
            ..
        }
    ));
    for payload in [
        r"\forall(i in 0..n, true)",
        r"\forall i in 0..n; i + 1",
        r"(\forall i in 0..n; true) && i >= 0",
    ] {
        let source = format!(
            "OPENQASM 3; uint n = 5;\n@saria.invariant {payload}\nwhile (n > 0) {{ n -= 1; }}"
        );
        assert!(frontend::parse_str(&source, "bad-quantifier.qasm").is_err());
    }
}

#[test]
fn qasm_math_builtins_are_explicit_and_do_not_capture_user_names() {
    let source = r"OPENQASM 3;
qubit q;
pragma saria.def sqrt(x: int) -> int = x + 1
if (true) {
float pi = 0.5;
@saria.requires sqrt(2) == 3 && \sqrt(4) == 2 && pi < \pi && \tau > \euler
reset q;
}
";
    frontend::parse_str(source, "namespaces.qasm").unwrap();
    for payload in [
        "sqrt(2) > 0",
        "pi > 3",
        "tau > 6",
        "euler > 2",
        r"\missing(1) == 1",
    ] {
        let source = format!("OPENQASM 3; qubit q;\n@saria.requires {payload}\nreset q;");
        assert!(
            frontend::parse_str(&source, "missing-prefix.qasm").is_err(),
            "{payload}"
        );
    }
    // Executable OpenQASM mathematical constants retain their original syntax.
    frontend::parse_str(
        r#"OPENQASM 3; include "stdgates.inc"; qubit q; rz(pi/2) q;"#,
        "executable.qasm",
    )
    .unwrap();
}
