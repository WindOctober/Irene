use std::cell::RefCell;
use std::collections::BTreeSet;

use num_rational::BigRational;

use crate::ir::{
    AstIdGenerator, AstNode, Gate, NumericConstant, NumericExpr, NumericExprKind, NumericType,
    StatementKind,
};

use super::openqasm3::{FrontendError, parse_str};

fn rational(numerator: i64, denominator: i64) -> NumericExpr {
    node(NumericExprKind::Rational(BigRational::new(
        numerator.into(),
        denominator.into(),
    )))
}

fn node<T>(kind: T) -> AstNode<T> {
    thread_local! {
        static IDS: RefCell<AstIdGenerator> = RefCell::new(AstIdGenerator::default());
    }
    IDS.with(|ids| ids.borrow_mut().node(kind))
}

#[test]
fn ast_ids_are_unique_and_dense_within_a_program() {
    let program = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        input angle theta;
        qubit[2] q;
        bit c;
        rz(theta / 2) q;
        c = measure q[0];
        if (c) { x q[1]; }
        "#,
        "ast-ids.qasm",
    )
    .unwrap();

    let mut ids = Vec::new();
    program.visit_ast_ids(|id| ids.push(id));
    let unique = ids.iter().copied().collect::<BTreeSet<_>>();

    assert_eq!(ids.len(), unique.len());
    assert_eq!(
        unique.into_iter().map(|id| id.index()).collect::<Vec<_>>(),
        (0..program.ast_id_bound()).collect::<Vec<_>>()
    );
}

#[test]
fn lowers_single_statement_if_bodies() {
    let program = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        qubit[2] q;
        bit c;
        c = measure q[0];
        if (c) x q[1]; else z q[1];
        "#,
        "single-statement-if.qasm",
    )
    .unwrap();

    let StatementKind::If {
        then_branch,
        else_branch,
        ..
    } = &program.body.statements[1].kind
    else {
        panic!("expected an if statement");
    };
    assert!(matches!(
        then_branch.statements[0].kind,
        StatementKind::Apply { gate: Gate::X, .. }
    ));
    assert!(matches!(
        else_branch.statements[0].kind,
        StatementKind::Apply { gate: Gate::Z, .. }
    ));
}

#[test]
fn specializes_a_subroutine_call_to_its_quantum_argument() {
    let program = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        def flip(qubit target) {
            x target;
        }
        qubit[2] data;
        flip(data[0]);
        flip(data[1]);
        "#,
        "subroutine-call.qasm",
    )
    .unwrap();

    for (index, statement) in program.body.statements.iter().enumerate() {
        let StatementKind::Scope(body) = &statement.kind else {
            panic!("expected a specialized subroutine scope");
        };
        let StatementKind::Apply { gate, qubits, .. } = &body.statements[0].kind else {
            panic!("expected the specialized gate operation");
        };
        assert_eq!(*gate, Gate::X);
        assert_eq!(qubits[0].register, program.quantum_registers[0].id);
        assert_eq!(qubits[0].index, index);
    }
}

#[test]
fn broadcasts_a_scalar_qubit_over_a_register() {
    let program = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        qubit[1] control;
        qubit[3] target;
        cx control[0], target;
        "#,
        "scalar-register-broadcast.qasm",
    )
    .unwrap();

    let StatementKind::Scope(body) = &program.body.statements[0].kind else {
        panic!("expected the broadcast gate sequence");
    };
    assert_eq!(body.statements.len(), 3);
    for (index, statement) in body.statements.iter().enumerate() {
        let StatementKind::Apply { gate, qubits, .. } = &statement.kind else {
            panic!("expected a broadcast gate operation");
        };
        assert_eq!(*gate, Gate::Cx);
        assert_eq!(qubits[0].index, 0);
        assert_eq!(qubits[1].index, index);
    }
}

#[test]
fn rejects_broadcasting_registers_of_different_widths() {
    let error = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        qubit[1] control;
        qubit[3] target;
        cx control, target;
        "#,
        "register-width-mismatch.qasm",
    )
    .unwrap_err();

    assert!(matches!(
        error,
        FrontendError::Expected {
            expected: "equally sized or scalar gate operands",
            ..
        }
    ));
}

#[test]
fn rejects_duplicate_qubits_in_a_gate_application() {
    let error = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        qubit q;
        cx q, q;
        "#,
        "duplicate-gate-operands.qasm",
    )
    .unwrap_err();

    assert!(matches!(
        error,
        FrontendError::Expected {
            expected: "distinct qubit operands for each gate application",
            ..
        }
    ));
}

#[test]
fn rejects_duplicate_qubits_introduced_by_broadcasting() {
    let error = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        qubit[2] q;
        cx q[0], q;
        "#,
        "overlapping-gate-broadcast.qasm",
    )
    .unwrap_err();

    assert!(matches!(
        error,
        FrontendError::Expected {
            expected: "distinct qubit operands for each gate application",
            ..
        }
    ));
}

#[test]
fn rejects_indexing_a_scalar_classical_bit() {
    let error = parse_str(
        "OPENQASM 3.0; qubit q; bit c; c[0] = measure q;",
        "indexed-scalar-bit.qasm",
    )
    .unwrap_err();

    assert!(matches!(
        error,
        FrontendError::WrongIdentifierKind {
            expected: "classical bit register",
            actual: "classical bit",
            ..
        }
    ));
}

#[test]
fn rejects_scalar_register_measurement_mismatch() {
    let error = parse_str(
        "OPENQASM 3.0; qubit q; bit[1] c; c = measure q;",
        "measurement-type-mismatch.qasm",
    )
    .unwrap_err();

    assert!(matches!(
        error,
        FrontendError::Expected {
            expected: "matching scalar or register measurement operands",
            ..
        }
    ));
}

#[test]
fn lowers_measurement_arrow_statement() {
    let program = parse_str(
        "OPENQASM 3.0; qubit q; bit[1] c; measure q -> c[0];",
        "measurement-arrow.qasm",
    )
    .unwrap();

    let StatementKind::Measure { qubit, target } = &program.body.statements[0].kind else {
        panic!("expected a measurement");
    };
    assert_eq!(qubit.register, program.quantum_registers[0].id);
    assert_eq!(target.register, program.classical_registers[0].id);
}

#[test]
fn rejects_classical_register_assignment_width_mismatch() {
    let error = parse_str(
        "OPENQASM 3.0; bit[2] left; bit[3] right; left = right;",
        "classical-assignment-width-mismatch.qasm",
    )
    .unwrap_err();

    assert!(matches!(
        error,
        FrontendError::Expected {
            expected: "matching scalar or register assignment operands",
            ..
        }
    ));
}

#[test]
fn rejects_a_classical_register_as_a_condition() {
    let error = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        qubit q;
        bit[2] c;
        if (c) x q;
        "#,
        "register-condition.qasm",
    )
    .unwrap_err();

    assert!(matches!(
        error,
        FrontendError::Expected {
            expected: "a scalar Boolean or bit expression",
            ..
        }
    ));
}

#[test]
fn distinguishes_bool_bit_and_bit_register_types() {
    parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        qubit q;
        bool predicate = false;
        bit flag = predicate;
        predicate = flag;
        if (flag && predicate) x q;
        "#,
        "bool-bit-compatibility.qasm",
    )
    .unwrap();

    let error = parse_str(
        "OPENQASM 3.0; bool predicate; bit[1] packed; packed = predicate;",
        "scalar-register-distinction.qasm",
    )
    .unwrap_err();
    assert!(matches!(
        error,
        FrontendError::Expected {
            expected: "matching scalar or register assignment operands",
            ..
        }
    ));
}

#[test]
fn rejects_indexing_a_bool_as_a_bit_register() {
    let error = parse_str(
        "OPENQASM 3.0; bool predicate; predicate[0] = false;",
        "indexed-bool.qasm",
    )
    .unwrap_err();

    assert!(matches!(
        error,
        FrontendError::WrongIdentifierKind {
            expected: "classical bit register",
            actual: "Boolean",
            ..
        }
    ));
}

#[test]
fn distinguishes_signed_and_unsigned_integer_cast_ranges() {
    parse_str(
        r#"
        OPENQASM 3.0;
        bit[2] bits;
        if (int[2](bits) == -2) {}
        if (uint[2](bits) == 3) {}
        "#,
        "integer-cast-ranges.qasm",
    )
    .unwrap();

    for (condition, expected) in [
        (
            "int[2](bits) == 2",
            "a signed integer literal representable at the cast width",
        ),
        (
            "uint[2](bits) == -1",
            "an unsigned integer literal representable at the cast width",
        ),
    ] {
        let error = parse_str(
            &format!("OPENQASM 3.0; bit[2] bits; if ({condition}) {{}}"),
            "integer-cast-out-of-range.qasm",
        )
        .unwrap_err();
        assert!(matches!(
            error,
            FrontendError::Expected {
                expected: actual,
                ..
            } if actual == expected
        ));
    }
}

#[test]
fn rejects_unsized_integer_casts_from_bit_registers() {
    for cast in ["int", "uint"] {
        let error = parse_str(
            &format!("OPENQASM 3.0; bit[1] bits; if ({cast}(bits) == 0) {{}}"),
            "unsized-integer-cast.qasm",
        )
        .unwrap_err();
        assert!(matches!(
            error,
            FrontendError::Expected {
                expected: "an explicitly sized integer cast",
                ..
            }
        ));
    }
}

#[test]
fn block_shadowing_uses_distinct_symbol_ids() {
    let program = parse_str(
        r#"
        OPENQASM 3.0;
        qubit q;
        bit result;
        if (true) {
            bit result;
            result = measure q;
        }
        if (true) {
            result = measure q;
        }
        "#,
        "shadowing.qasm",
    )
    .unwrap();

    let global = program.classical_registers[0].id;
    let StatementKind::If { then_branch, .. } = &program.body.statements[0].kind else {
        panic!("expected the first if statement");
    };
    let local = then_branch.classical_registers[0].id;
    let StatementKind::Measure { target, .. } = &then_branch.statements[0].kind else {
        panic!("expected a local measurement");
    };
    assert_eq!(target.register, local);
    assert_ne!(local, global);

    let StatementKind::If { then_branch, .. } = &program.body.statements[1].kind else {
        panic!("expected the second if statement");
    };
    let StatementKind::Measure { target, .. } = &then_branch.statements[0].kind else {
        panic!("expected a global measurement");
    };
    assert_eq!(target.register, global);
}

#[test]
fn sibling_branch_cannot_see_a_local_binding() {
    let error = parse_str(
        r#"
        OPENQASM 3.0;
        qubit q;
        if (true) { bit local; }
        if (true) { local = measure q; }
        "#,
        "sibling-scope.qasm",
    )
    .unwrap_err();
    assert!(matches!(
        error,
        FrontendError::UnknownIdentifier(name) if name == "local"
    ));
}

#[test]
fn rejects_same_scope_redeclaration() {
    let error = parse_str("OPENQASM 3.0; bit value; bit value;", "duplicate.qasm").unwrap_err();
    assert!(matches!(
        error,
        FrontendError::DuplicateIdentifier(name) if name == "value"
    ));
}

#[test]
fn rejects_qubit_declaration_in_a_control_flow_block() {
    let error = parse_str(
        "OPENQASM 3.0; if (true) { qubit local; }",
        "local-qubit.qasm",
    )
    .unwrap_err();
    assert!(matches!(
        error,
        FrontendError::IllegalDeclaration {
            declaration: "qubit",
            scope: "block"
        }
    ));
}

#[test]
fn rejects_use_before_declaration() {
    let error = parse_str(
        r#"
        OPENQASM 3.0;
        qubit q;
        if (true) {
            local = measure q;
            bit local;
        }
        "#,
        "use-before-declaration.qasm",
    )
    .unwrap_err();
    assert!(matches!(
        error,
        FrontendError::UnknownIdentifier(name) if name == "local"
    ));
}

#[test]
fn rejects_shadowing_a_standard_gate() {
    let error = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        if (true) { bit h; }
        "#,
        "gate-shadowing.qasm",
    )
    .unwrap_err();
    assert!(matches!(
        error,
        FrontendError::CannotShadow(name) if name == "h"
    ));
}

#[test]
fn numeric_constants_respect_local_shadowing() {
    let error = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        qubit q;
        if (true) {
            bit pi;
            pi = measure q;
            rz(pi) q;
        }
        "#,
        "constant-shadowing.qasm",
    )
    .unwrap_err();

    assert!(matches!(
        error,
        FrontendError::WrongIdentifierKind {
            expected: "numeric value",
            actual: "classical bit",
            ..
        }
    ));
}

#[test]
fn preserves_numeric_gate_parameters_without_float_conversion() {
    let program = parse_str(
        r#"
        OPENQASM 3.0;
        include "stdgates.inc";
        input angle[20] theta;
        input float[64] delta;
        qubit[2] q;
        rz(0.1) q[0];
        rz(0.100) q[0];
        rz(1e-1) q[0];
        cp(pi / 7 + theta) q[0], q[1];
        crz(-1.25e-3 * delta) q[0], q[1];
        "#,
        "angle-parameters.qasm",
    )
    .unwrap();

    assert_eq!(program.numeric_inputs[0].ty, NumericType::Angle(Some(20)));
    assert_eq!(program.numeric_inputs[1].ty, NumericType::Float(Some(64)));

    let StatementKind::Apply {
        gate, parameters, ..
    } = &program.body.statements[0].kind
    else {
        panic!("expected an rz gate");
    };
    assert_eq!(*gate, Gate::Rz);
    assert_eq!(parameters, &[rational(1, 10)]);
    for statement in &program.body.statements[1..3] {
        let StatementKind::Apply { parameters, .. } = &statement.kind else {
            panic!("expected an rz gate");
        };
        assert_eq!(parameters, &[rational(1, 10)]);
    }

    let theta = node(NumericExprKind::Input(program.numeric_inputs[0].id));
    let StatementKind::Apply { parameters, .. } = &program.body.statements[3].kind else {
        panic!("expected a cp gate");
    };
    assert_eq!(
        parameters,
        &[node(NumericExprKind::Add(
            Box::new(node(NumericExprKind::Div(
                Box::new(node(NumericExprKind::Constant(NumericConstant::Pi))),
                Box::new(rational(7, 1)),
            ))),
            Box::new(theta),
        ))]
    );

    let delta = node(NumericExprKind::Input(program.numeric_inputs[1].id));
    let StatementKind::Apply { parameters, .. } = &program.body.statements[4].kind else {
        panic!("expected a crz gate");
    };
    assert_eq!(
        parameters,
        &[node(NumericExprKind::Mul(
            Box::new(node(NumericExprKind::Neg(Box::new(rational(1, 800))))),
            Box::new(delta),
        ))]
    );
}
