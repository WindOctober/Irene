use iqir::frontend;

#[test]
fn qasm_import_keeps_function_ids_and_does_not_execute_definitions() {
    let p = frontend::parse_str(
        "OPENQASM 3; uint[8] n = 0; bool stop = false;\n\
        pragma saria.def a(k: int) -> float = 1 / (2*k)!\n\
        pragma saria.def r(k: int) -> float = a(k)/(cosh(1)-sum(j in 0..k, a(j)))\n\
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
