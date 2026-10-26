use irene::symbolic::{ExecutionConfig, OutputSelection, SymbolicError, execute};

#[test]
fn equivalence_backend_refuses_machine_angles_before_algebraic_simplification() {
    for angle in ["float[64](uint[4](b))", "0.0 * float[64](uint[4](b))"] {
        let source = format!(
            "OPENQASM 3; include \"stdgates.inc\"; qubit[4] q; bit[4] b; b=measure q; ry({angle}) q[0];"
        );
        let p = iqir::frontend::parse_str(&source, "machine.qasm").unwrap();
        let error =
            execute(&p, &ExecutionConfig::zero(), &OutputSelection::new([], [])).unwrap_err();
        assert!(matches!(error, SymbolicError::NumericDomain(_)), "{error}");
    }
}
