//! Frontend syntax support must not silently widen the verifier's domain.
use irene::frontend::openqasm3;
use irene::ir::Qubit;
use irene::symbolic::{ExecutionConfig, OutputSelection, SymbolicError, execute};

#[test]
fn unsupported_statements_are_rejected_before_dead_code_slicing() {
    for source in [
        "gphase(pi/2);",
        "gate g a {x a; h a;} qubit q; inv @ g q;",
        "qubit q; if(false) { U(0,0,0) q; }",
    ] {
        let program = openqasm3::parse_str(
            &format!("OPENQASM 3; include \"stdgates.inc\"; {source}"),
            "capability.qasm",
        )
        .unwrap();
        let result = execute(
            &program,
            &ExecutionConfig::zero(),
            &OutputSelection::new([], []),
        );
        assert!(
            matches!(result, Err(SymbolicError::UnsupportedConstruct(_))),
            "{source}: {result:?}"
        );
    }
}

#[test]
fn plain_custom_gates_use_the_existing_symbolic_executor() {
    let program = openqasm3::parse_str(
        "OPENQASM 3; include \"stdgates.inc\"; gate g a {x a; h a;} qubit q; g q;",
        "gate.qasm",
    )
    .unwrap();
    let q = Qubit {
        register: program.quantum_registers[0].id,
        index: 0,
    };
    execute(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new([q], []),
    )
    .unwrap();
}
