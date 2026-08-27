use crate::ir::Statement;

use super::openqasm3::{FrontendError, parse_str};
use super::scope::{BindingKind, ScopeError, ScopeKind, ScopeStack};

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
