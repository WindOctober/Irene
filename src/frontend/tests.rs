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
fn static_uint_ranges_preserve_order_slices_and_iteration_local_storage() {
    let program = parse_str(
        r#"
        OPENQASM 3.0; include "stdgates.inc";
        const uint[8] n = 3;
        qubit[2 * n] q;
        def flip(qubit[2] pair) { x pair; }
        for uint[8] i in [0:n - 1] {
            bit local;
            flip(q[2 * i:2 * i + 1]);
            local = measure q[i];
        }
        x q[0:2:4];
    "#,
        "static-range.qasm",
    )
    .unwrap();
    assert_eq!(program.quantum_registers[0].width, 6);
    fn gates(block: &crate::ir::Block, output: &mut Vec<usize>) {
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Scope(block) => gates(block, output),
                StatementKind::Apply {
                    gate: Gate::X,
                    qubits,
                    ..
                } => output.push(qubits[0].index),
                _ => {}
            }
        }
    }
    let mut actual = Vec::new();
    gates(&program.body, &mut actual);
    assert_eq!(actual, [0, 1, 2, 3, 4, 5, 0, 2, 4]);
    let StatementKind::Scope(iterations) = &program.body.statements[0].kind else {
        panic!()
    };
    let locals = iterations
        .statements
        .iter()
        .map(|statement| {
            let StatementKind::Scope(body) = &statement.kind else {
                panic!()
            };
            body.classical_registers[0].id
        })
        .collect::<BTreeSet<_>>();
    assert_eq!(locals.len(), 3);
}

#[test]
fn static_uint_specialization_rejects_missing_semantic_premises() {
    for body in [
        "const uint[2] n = 4;",
        "const uint[3] n = 7; qubit[n + 1] q;",
        "const uint[3] n = 0; qubit[n - 1] q;",
        "const uint[3] n = 2; qubit[n / 0] q;",
        "qubit q; for uint[8] i in [0:0:1] x q;",
        "qubit q; for uint[8] i in [2:1] x q;",
        "qubit q; for uint[2] i in [0:4] x q;",
        "qubit q; for uint[64] i in [0:18446744073709551615] x q;",
        "qubit[2] q; x q[0:18446744073709551615];",
        "qubit[2] q; x q[:1];",
        "qubit[2] q; x q[0:];",
        "qubit[2] q; x q[0:1:];",
        "qubit[2] q; x q[0:2];",
        "qubit[2] q; for uint[8] i in [0:1] { i = 1; x q[i]; }",
        "qubit q; for uint[8] i in [0:1] { break; }",
        "qubit q; for uint[8] i in [0:1] { continue; }",
        "qubit q; for uint[8] i in [0:1] { const uint[8] n = i; }",
        "qubit q; for uint[8] i in [0:1] { bit[i] c; }",
        "qubit q; for uint[8] i in [0:1] { const uint[8] i = 1; }",
        "qubit[2] q; for uint[8] i in [0:1] x q[i]; x q[i];",
        "const uint[8] n=2; n=1;",
        "const uint[8] n=2; const uint[8] n=3;",
        "qubit q; for uint[8] i in [0:1] { if(i==0) x q; else unknown q; }",
        "qubit[2] q; def f(qubit a) { x q[0]; } f(q[0]);",
        "qubit[2] q; def f(qubit[2] a) { x a[n]; } const uint[8] n=0; f(q);",
        "qubit[2] q; def f(qubit[2] a) { x a[i]; } for uint[8] i in [0:1] f(q);",
        "qubit q; for uint[16] i in [0:4096] x q;",
        "qubit q; for uint[8] i in [0:64] { for uint[8] j in [0:64] x q; }",
        "qubit q; for uint[8] i in [0:64] x q; for uint[16] j in [0:4090] x q;",
    ] {
        let result = parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
            "static-refusal.qasm",
        );
        assert!(result.is_err(), "unexpected admission: {body}");
    }
}

#[test]
fn static_uint_constants_obey_lexical_scope_and_definition_visibility() {
    let program = parse_str(
        r#"
        OPENQASM 3.0; include "stdgates.inc";
        const uint[8] n = 2; qubit[n] q;
        def f(qubit[n] a) { const uint[8] j = n - 1; x a[j]; }
        for uint[8] n in [0:1] { f(q); }
        x q[n - 1];
    "#,
        "static-scopes.qasm",
    )
    .unwrap();
    assert_eq!(program.quantum_registers[0].width, 2);
    let mut ids = Vec::new();
    program.visit_ast_ids(|id| ids.push(id));
    assert_eq!(ids.iter().collect::<BTreeSet<_>>().len(), ids.len());
}

#[test]
fn static_uint_arithmetic_checks_each_intermediate_not_just_final_value() {
    for width in 1..=5 {
        for a in 0..(1_u64 << width) {
            for b in 0..(1_u64 << width) {
                for (operator, expected) in [
                    ("+", a.checked_add(b)),
                    ("-", a.checked_sub(b)),
                    ("*", a.checked_mul(b)),
                    ("/", a.checked_div(b)),
                    ("%", a.checked_rem(b)),
                ] {
                    let expression = format!(
                        "const uint[{width}] a={a}; const uint[{width}] b={b}; const uint[{width}] c=a {operator} b;"
                    );
                    let result = parse_str(
                        &format!("OPENQASM 3.0; {expression}"),
                        "static-arithmetic.qasm",
                    );
                    assert_eq!(
                        result.is_ok(),
                        expected.is_some_and(|x| x < (1_u64 << width)),
                        "{expression}"
                    );
                }
            }
        }
    }
    assert!(
        parse_str(
            "OPENQASM 3.0; const uint[2] a=3; const uint[2] b=(a+1)-1;",
            "intermediate.qasm"
        )
        .is_err()
    );
}

#[test]
fn static_signed_arithmetic_checks_bounds_and_truncates_division_toward_zero() {
    for width in 1..=4 {
        let bound = 1_i128 << (width - 1);
        for a in -bound..bound {
            for b in -bound..bound {
                for (operator, expected) in [
                    ("+", a.checked_add(b)),
                    ("-", a.checked_sub(b)),
                    ("*", a.checked_mul(b)),
                    ("/", a.checked_div(b)),
                    ("%", a.checked_rem(b)),
                ] {
                    let declarations = format!(
                        "const int[{width}] a={a}; const int[{width}] b={b}; const int[{width}] c=a {operator} b;"
                    );
                    let admitted = expected.is_some_and(|x| -bound <= x && x < bound)
                        && !(a == -bound && b == -1 && matches!(operator, "/" | "%"));
                    let text = format!("OPENQASM 3.0; {declarations}");
                    assert_eq!(
                        parse_str(&text, "signed-static.qasm").is_ok(),
                        admitted,
                        "{text}"
                    );
                    if admitted {
                        // The declared result affects the register size, not
                        // merely whether the initializer is accepted.
                        let text = format!("{text} qubit[c - ({}) + 1] q;", expected.unwrap());
                        // The narrowest width cannot represent +1; keep the
                        // semantic check on signed widths with spare range.
                        if width >= 2 {
                            let result = parse_str(&text, "signed-static-value.qasm").unwrap();
                            assert_eq!(result.quantum_registers[0].width, 1, "{text}");
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn static_machine_integers_have_explicit_32_bit_bounds() {
    for body in [
        "const uint n=4294967295;",
        "const int n=2147483647; const int m=-2147483648;",
        "const int[32] n=-2147483648; const uint[64] m=18446744073709551615;",
        "const int[64] n=-9223372036854775808;",
        "qubit[2 + 2] q;",
        "const uint n=2; qubit[n] q; for uint i in [0:n-1] x q[i];",
        "const int[32] n=-2; qubit[3] q; for int[32] i in [n:0] x q[i-n];",
        "qubit[3] q; for int i in [2:-1:0] x q[i];",
        "qubit[3] q; x q[2:-1:0];",
    ] {
        parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
            "machine-static.qasm",
        )
        .unwrap();
    }
    for body in [
        "const uint n=4294967296;",
        "const uint n=-1;",
        "const int n=2147483648;",
        "const int n=-2147483649;",
        "const int[32] n=2147483647; const int[32] m=(n+1)-1;",
        "const int[32] n=-2147483648; const int[32] m=-n;",
        "const int[32] n=-2147483648; const int[32] m=n / -1;",
        "const int n=-1; qubit[n] q;",
        "const int n=-1; qubit q; x q[n];",
        "const int a=-1; const uint b=2; const int c=a+b;",
        "const uint a=1; bit c=bool(a & a);",
        "const uint a=1; bit c=bool(~a);",
        "const uint a=1; bit[32] c=bit[32](a);",
    ] {
        assert!(
            parse_str(&format!("OPENQASM 3.0; {body}"), "machine-refusal.qasm").is_err(),
            "{body}"
        );
    }
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
fn positive_control_modifiers_preserve_gate_parameters_and_operand_order() {
    for (name, params, expected) in [
        ("x", "", Gate::Cx),
        ("y", "", Gate::Cy),
        ("z", "", Gate::Cz),
        ("p", "(pi/7)", Gate::Cp),
        ("rx", "(pi/7)", Gate::Crx),
        ("ry", "(pi/7)", Gate::Cry),
        ("rz", "(pi/7)", Gate::Crz),
        ("cx", "", Gate::Ccx),
    ] {
        for modifier in ["ctrl", "ctrl(1)"] {
            let operands = if name == "cx" {
                "q[2],q[0],q[1]"
            } else {
                "q[2],q[0]"
            };
            let program = parse_str(&format!(
                "OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {modifier} @ {name}{params} {operands};"
            ), "controlled-gates.qasm").unwrap();
            let StatementKind::Apply {
                gate,
                parameters,
                qubits,
            } = &program.body.statements[0].kind
            else {
                panic!("expected a controlled IR gate");
            };
            assert_eq!(*gate, expected);
            assert_eq!(parameters.len(), usize::from(!params.is_empty()));
            assert_eq!(
                qubits.iter().map(|q| q.index).collect::<Vec<_>>(),
                if name == "cx" {
                    vec![2, 0, 1]
                } else {
                    vec![2, 0]
                }
            );
            let mut ids = Vec::new();
            program.visit_ast_ids(|id| ids.push(id.index()));
            ids.sort();
            assert_eq!(ids, (0..program.ast_id_bound()).collect::<Vec<_>>());
        }
    }
    for modifier in ["ctrl(2)", "ctrl @ ctrl", "ctrl(0x2)"] {
        let program = parse_str(
            &format!(
                "OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {modifier} @ x q[1],q[2],q[0];"
            ),
            "double-control.qasm",
        )
        .unwrap();
        assert!(matches!(
            program.body.statements[0].kind,
            StatementKind::Apply {
                gate: Gate::Ccx,
                ..
            }
        ));
    }
    let broadcast = parse_str(
        "OPENQASM 3.0; include \"stdgates.inc\"; qubit c; qubit[2] q; ctrl @ ry(pi/7) c,q;",
        "controlled-broadcast.qasm",
    )
    .unwrap();
    let StatementKind::Scope(body) = &broadcast.body.statements[0].kind else {
        panic!("expected a broadcast sequence");
    };
    assert_eq!(body.statements.len(), 2);
    for (index, statement) in body.statements.iter().enumerate() {
        let StatementKind::Apply {
            gate,
            parameters,
            qubits,
        } = &statement.kind
        else {
            panic!("expected a controlled broadcast gate");
        };
        assert_eq!(*gate, Gate::Cry);
        assert_eq!(parameters.len(), 1);
        assert_eq!(qubits[0].register, broadcast.quantum_registers[0].id);
        assert_eq!(qubits[1].index, index);
    }
    let mut ids = Vec::new();
    broadcast.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort();
    assert_eq!(ids, (0..broadcast.ast_id_bound()).collect::<Vec<_>>());
}

#[test]
fn unsupported_control_modifiers_counts_and_invalid_operands_are_not_ignored() {
    for instruction in [
        "negctrl @ x q[0],q[1]",
        "pow(0.5) @ x q[0]",
        "ctrl(0) @ x q[0]",
        "ctrl(-1) @ x q[0]",
        "ctrl(1.0) @ x q[0],q[1]",
        "ctrl(1+0) @ x q[0],q[1]",
        "ctrl(3) @ x q[0],q[1],q[2],q[3]",
        "ctrl @ ctrl @ ctrl @ x q[0],q[1],q[2],q[3]",
        "ctrl(2) @ ry(pi/3) q[0],q[1],q[2]",
        "ctrl(2) @ h q[0],q[1],q[2]",
        "ctrl @ gphase(pi/3) q[0]",
        "ctrl @ ry q[0],q[1]",
        "ctrl @ x q[0]",
        "ctrl @ x q[0],q[0]",
        "ctrl @ ry(pi/3) q,q[0]",
    ] {
        assert!(
            parse_str(
                &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[4] q; {instruction};"),
                "unsupported-control.qasm"
            )
            .is_err(),
            "{instruction}"
        );
    }
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
fn integer_parameter_subexpressions_use_truncating_division_and_dense_ids() {
    let mut source = String::from("OPENQASM 3.0; include \"stdgates.inc\"; qubit q;\n");
    let mut expected = Vec::new();
    for numerator in -7..=7 {
        for denominator in (-3..=3).filter(|value| *value != 0) {
            source.push_str(&format!("p(({numerator}) / ({denominator})) q;\n"));
            expected.push(rational(numerator / denominator, 1));
        }
    }
    source.push_str("p((7 / 2 - 1) / 2) q; p(0x7 / 0b10) q; p(1.0 + (7 / 2)) q; p(7 / 2.0) q;");
    expected.extend([
        rational(1, 1),
        rational(3, 1),
        node(NumericExprKind::Add(
            Box::new(rational(1, 1)),
            Box::new(rational(3, 1)),
        )),
        node(NumericExprKind::Div(
            Box::new(rational(7, 1)),
            Box::new(rational(2, 1)),
        )),
    ]);
    let program = parse_str(&source, "integer-parameters.qasm").unwrap();
    assert_eq!(program.body.statements.len(), expected.len());
    for (statement, expected) in program.body.statements.iter().zip(expected) {
        let StatementKind::Apply { parameters, .. } = &statement.kind else {
            panic!("gate expected")
        };
        assert_eq!(parameters, &[expected]);
    }
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
fn integer_parameter_zero_divisors_are_rejected_even_inside_mixed_expressions() {
    for expression in [
        "1 / 0",
        "1 / (2 - 2)",
        "1 / (1 / 2)",
        "0 * (1 / 0)",
        "1.0 + (1 / 0)",
        "1.0 / (1 / 2)",
        "1.0 / 0.0",
    ] {
        let source = format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit q; p({expression}) q;");
        assert!(
            parse_str(&source, "undefined-parameter.qasm").is_err(),
            "{expression}"
        );
    }
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
