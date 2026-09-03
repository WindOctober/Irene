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
        rz(theta / 2) q[0];
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
            actual: "classical bit register",
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
