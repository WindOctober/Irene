//! Importing a loop must not silently widen the verifier's supported domain.
use irene::frontend::openqasm3;
use irene::symbolic::{ExecutionConfig, OutputSelection, SymbolicError, execute};

#[test]
fn loops_are_rejected_even_when_dead_or_unobservable() {
    for source in [
        "while(false) {}",
        "while(true) {}",
        "if(false) {while(true) {}}",
        "qubit q; bit b; while(b) {while(b) {b=measure q;}}",
    ] {
        let program = openqasm3::parse_str(&format!("OPENQASM 3; {source}"), "while.qasm").unwrap();
        let result = execute(
            &program,
            &ExecutionConfig::zero(),
            &OutputSelection::new([], []),
        );
        assert!(
            matches!(result, Err(SymbolicError::UnsupportedConstruct(_))),
            "{source}: {result:?}"
        );
        assert!(irene::equivalence::unitary_miter::validate(&program).is_err());
    }
}
