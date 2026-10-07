//! Frontend syntax support must not silently widen the verifier's domain.
use irene::frontend::openqasm3;
use irene::ir::*;
use irene::symbolic::{ExecutionConfig, OutputSelection, SymbolicError, execute};

#[test]
fn unsupported_statements_are_rejected_before_dead_code_slicing() {
    for source in [
        "while(false) {}",
        "while(true) {}",
        "if(false) { while(true) {} }",
        "if(false) { int[8] n=0; }",
        "float[32] f=0.0;",
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
fn scalar_comparison_is_rejected_even_under_a_false_boolean_guard() {
    // Direct IR construction: do not rely on a preceding declaration to catch it.
    let mut program = openqasm3::parse_str("OPENQASM 3; if(false) {}", "guard.qasm").unwrap();
    let mut ids = AstIdGenerator::starting_at(program.ast_id_bound());
    let ty = ScalarType::Int {
        width: 8,
        signed: true,
    };
    let left = ids.node(ScalarExprData {
        ty,
        kind: ScalarExprKind::Integer(0),
    });
    let right = ids.node(ScalarExprData {
        ty,
        kind: ScalarExprKind::Integer(1),
    });
    let comparison = ids.node(ClassicalExprKind::ScalarCompare {
        op: ScalarComparison::Lt,
        left: Box::new(left),
        right: Box::new(right),
    });
    let guard = ids.node(ClassicalExprKind::Bool(false));
    let StatementKind::If { condition, .. } = &mut program.body.statements[0].kind else {
        panic!()
    };
    *condition = ids.node(ClassicalExprKind::And(
        Box::new(guard),
        Box::new(comparison),
    ));
    assert!(matches!(
        execute(
            &program,
            &ExecutionConfig::zero(),
            &OutputSelection::new([], [])
        ),
        Err(SymbolicError::UnsupportedConstruct("scalar comparison"))
    ));
}
