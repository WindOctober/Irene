use num_rational::BigRational;

use crate::ir::{Gate, NumericConstant, NumericExpr, NumericType, Statement};

use super::openqasm3::{FrontendError, parse_str};
use super::scope::{BindingKind, ScopeError, ScopeKind, ScopeStack};

fn rational(numerator: i64, denominator: i64) -> NumericExpr {
    NumericExpr::Rational(BigRational::new(numerator.into(), denominator.into()))
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
    let Statement::If { then_branch, .. } = &program.body.statements[0] else {
        panic!("expected the first if statement");
    };
    let local = then_branch.classical_registers[0].id;
    let Statement::Measure { target, .. } = &then_branch.statements[0] else {
        panic!("expected a local measurement");
    };
    assert_eq!(target.register, local);
    assert_ne!(local, global);

    let Statement::If { then_branch, .. } = &program.body.statements[1] else {
        panic!("expected the second if statement");
    };
    let Statement::Measure { target, .. } = &then_branch.statements[0] else {
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
fn registers_the_openqasm_3_standard_gate_names() {
    let mut scopes = ScopeStack::new();
    scopes.declare_standard_gates().unwrap();

    for name in ["CX", "phase", "cphase", "id", "u1", "u2", "u3"] {
        assert!(matches!(
            scopes.lookup(name).unwrap().kind,
            BindingKind::Gate
        ));
    }
}

#[test]
fn block_shadowing_restores_the_outer_binding() {
    let mut scopes = ScopeStack::new();
    let outer = scopes
        .declare("value", BindingKind::ClassicalBit { width: 1 })
        .unwrap();
    scopes.enter(ScopeKind::Block);
    let inner = scopes
        .declare("value", BindingKind::ClassicalBit { width: 2 })
        .unwrap();
    assert_eq!(scopes.lookup("value").unwrap(), inner);
    scopes.exit();
    assert_eq!(scopes.lookup("value").unwrap(), outer);
}

#[test]
fn sibling_blocks_do_not_share_bindings() {
    let mut scopes = ScopeStack::new();
    scopes.enter(ScopeKind::Block);
    scopes
        .declare("local", BindingKind::ClassicalBit { width: 1 })
        .unwrap();
    scopes.exit();
    scopes.enter(ScopeKind::Block);
    assert_eq!(
        scopes.lookup("local"),
        Err(ScopeError::Unknown("local".to_owned()))
    );
}

#[test]
fn rejects_same_scope_redeclaration_and_local_qubits() {
    let mut scopes = ScopeStack::new();
    scopes
        .declare("flag", BindingKind::ClassicalBit { width: 1 })
        .unwrap();
    assert_eq!(
        scopes.declare("flag", BindingKind::ClassicalBit { width: 1 }),
        Err(ScopeError::AlreadyDeclared("flag".to_owned()))
    );
    scopes.enter(ScopeKind::Block);
    assert!(matches!(
        scopes.declare("q", BindingKind::QuantumRegister { width: 1 }),
        Err(ScopeError::IllegalDeclaration {
            declaration: "qubit",
            scope: ScopeKind::Block
        })
    ));
}

#[test]
fn gates_cannot_be_shadowed() {
    let mut scopes = ScopeStack::new();
    scopes.declare("operation", BindingKind::Gate).unwrap();
    scopes.enter(ScopeKind::Block);
    assert_eq!(
        scopes.declare("operation", BindingKind::ClassicalBit { width: 1 }),
        Err(ScopeError::CannotShadow("operation".to_owned()))
    );
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

    let Statement::Apply {
        gate, parameters, ..
    } = &program.body.statements[0]
    else {
        panic!("expected an rz gate");
    };
    assert_eq!(*gate, Gate::Rz);
    assert_eq!(parameters, &[rational(1, 10)]);
    for statement in &program.body.statements[1..3] {
        let Statement::Apply { parameters, .. } = statement else {
            panic!("expected an rz gate");
        };
        assert_eq!(parameters, &[rational(1, 10)]);
    }

    let theta = NumericExpr::Input(program.numeric_inputs[0].id);
    let Statement::Apply { parameters, .. } = &program.body.statements[3] else {
        panic!("expected a cp gate");
    };
    assert_eq!(
        parameters,
        &[NumericExpr::Add(
            Box::new(NumericExpr::Div(
                Box::new(NumericExpr::Constant(NumericConstant::Pi)),
                Box::new(rational(7, 1)),
            )),
            Box::new(theta),
        )]
    );

    let delta = NumericExpr::Input(program.numeric_inputs[1].id);
    let Statement::Apply { parameters, .. } = &program.body.statements[4] else {
        panic!("expected a crz gate");
    };
    assert_eq!(
        parameters,
        &[NumericExpr::Mul(
            Box::new(NumericExpr::Neg(Box::new(rational(1, 800)))),
            Box::new(delta),
        )]
    );
}
