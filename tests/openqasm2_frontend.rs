use std::collections::BTreeSet;
use std::panic::{AssertUnwindSafe, catch_unwind};

use irene::frontend::openqasm2;
use irene::ir::{
    Block, ClassicalBit, Gate, NumericConstant, NumericExpr, NumericExprKind, Program, Qubit,
    StatementKind,
};
use irene::symbolic::{BooleanPolynomial, ExecutionConfig, OutputSelection, execute};
use num_rational::BigRational;

fn parse(source: &str) -> Program {
    openqasm2::parse_str(source, "integration-test.qasm").expect("valid OpenQASM 2 program")
}

fn qubit(program: &Program, register_name: &str, index: usize) -> Qubit {
    let register = program
        .quantum_registers
        .iter()
        .find(|register| register.name == register_name)
        .unwrap_or_else(|| panic!("missing quantum register `{register_name}`"));
    Qubit {
        register: register.id,
        index,
    }
}

fn bit(program: &Program, register_name: &str, index: usize) -> ClassicalBit {
    let register = program
        .classical_registers
        .iter()
        .find(|register| register.name == register_name)
        .unwrap_or_else(|| panic!("missing classical register `{register_name}`"));
    ClassicalBit {
        register: register.id,
        index,
    }
}

fn collect_applies<'a>(block: &'a Block, applies: &mut Vec<(Gate, &'a [NumericExpr])>) {
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::Apply {
                gate, parameters, ..
            } => applies.push((*gate, parameters)),
            StatementKind::Scope(body) => collect_applies(body, applies),
            StatementKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_applies(then_branch, applies);
                collect_applies(else_branch, applies);
            }
            StatementKind::Reset(_)
            | StatementKind::Measure { .. }
            | StatementKind::Assign { .. } => {}
        }
    }
}

fn collect_apply_details<'a>(
    block: &'a Block,
    applies: &mut Vec<(Gate, &'a [NumericExpr], &'a [Qubit])>,
) {
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::Apply {
                gate,
                parameters,
                qubits,
            } => applies.push((*gate, parameters, qubits)),
            StatementKind::Scope(body) => collect_apply_details(body, applies),
            StatementKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                collect_apply_details(then_branch, applies);
                collect_apply_details(else_branch, applies);
            }
            StatementKind::Reset(_)
            | StatementKind::Measure { .. }
            | StatementKind::Assign { .. } => {}
        }
    }
}

fn exact_rational(expression: &NumericExpr) -> Option<BigRational> {
    match &expression.kind {
        NumericExprKind::Rational(value) => Some(value.clone()),
        NumericExprKind::Neg(inner) => exact_rational(inner).map(std::ops::Neg::neg),
        NumericExprKind::Add(left, right) => Some(exact_rational(left)? + exact_rational(right)?),
        NumericExprKind::Sub(left, right) => Some(exact_rational(left)? - exact_rational(right)?),
        NumericExprKind::Mul(left, right) => Some(exact_rational(left)? * exact_rational(right)?),
        NumericExprKind::Div(left, right) => Some(exact_rational(left)? / exact_rational(right)?),
        NumericExprKind::Constant(_) | NumericExprKind::Input(_) => None,
    }
}

fn pi_coefficient(expression: &NumericExpr) -> Option<BigRational> {
    match &expression.kind {
        NumericExprKind::Constant(NumericConstant::Pi) => Some(BigRational::from_integer(1.into())),
        NumericExprKind::Neg(inner) => pi_coefficient(inner).map(std::ops::Neg::neg),
        NumericExprKind::Add(left, right) => Some(pi_coefficient(left)? + pi_coefficient(right)?),
        NumericExprKind::Sub(left, right) => Some(pi_coefficient(left)? - pi_coefficient(right)?),
        NumericExprKind::Mul(left, right) => {
            if let Some(rational) = exact_rational(left) {
                pi_coefficient(right).map(|coefficient| rational * coefficient)
            } else {
                exact_rational(right)
                    .zip(pi_coefficient(left))
                    .map(|(rational, coefficient)| rational * coefficient)
            }
        }
        NumericExprKind::Div(left, right) => Some(pi_coefficient(left)? / exact_rational(right)?),
        NumericExprKind::Rational(value) if value == &BigRational::from_integer(0.into()) => {
            Some(BigRational::from_integer(0.into()))
        }
        NumericExprKind::Rational(_) | NumericExprKind::Constant(_) | NumericExprKind::Input(_) => {
            None
        }
    }
}

fn assert_rational(expression: &NumericExpr, numerator: i64, denominator: i64) {
    assert_eq!(
        exact_rational(expression),
        Some(BigRational::new(numerator.into(), denominator.into())),
        "expected an exact rational, got {expression:?}"
    );
}

fn assert_neg_rational(expression: &NumericExpr, numerator: i64, denominator: i64) {
    assert_rational(expression, -numerator, denominator);
}

fn assert_pi_over(expression: &NumericExpr, denominator: i64) {
    assert_eq!(
        pi_coefficient(expression),
        Some(BigRational::new(1.into(), denominator.into())),
        "expected pi / {denominator}, got {expression:?}"
    );
}

fn assert_rational_times_pi(expression: &NumericExpr, numerator: i64) {
    assert_eq!(
        pi_coefficient(expression),
        Some(BigRational::from_integer(numerator.into())),
        "expected {numerator} * pi, got {expression:?}"
    );
}

fn assert_rejected_without_panicking(label: &str, source: &str) {
    let result = catch_unwind(AssertUnwindSafe(|| {
        openqasm2::parse_str(source, &format!("{label}.qasm"))
    }));
    let result = result.unwrap_or_else(|_| panic!("{label}: frontend panicked on source input"));
    let error = match result {
        Ok(_) => panic!("{label}: invalid source was accepted"),
        Err(error) => error,
    };
    assert!(
        !error.to_string().trim().is_empty(),
        "{label}: rejection had an empty diagnostic"
    );
}

#[test]
fn lowers_old_style_declarations_primitives_and_qelib_gates() {
    let program = parse(
        r#"
        OPENQASM 2.0;
        qreg data[2];
        creg result[2];
        U(pi / 2, pi / 3, pi / 5) data[0];
        CX data[0], data[1];
        include "qelib1.inc";
        h data[0];
        cu1(pi / 8) data[0], data[1];
        rz(pi / 5) data[1];
        crz(-0.125) data[0], data[1];
        barrier data;
        "#,
    );

    assert_eq!(program.version.major, 2);
    assert_eq!(program.version.minor, 0);
    assert!(program.numeric_inputs.is_empty());
    assert_eq!(
        program
            .quantum_registers
            .iter()
            .map(|register| (register.name.as_str(), register.width))
            .collect::<Vec<_>>(),
        [("data", 2)]
    );
    assert_eq!(
        program
            .classical_registers
            .iter()
            .map(|register| (register.name.as_str(), register.width))
            .collect::<Vec<_>>(),
        [("result", 2)]
    );
    assert_eq!(program.operation_count(), 10);

    let mut applies = Vec::new();
    collect_applies(&program.body, &mut applies);
    assert_eq!(
        applies.iter().map(|(gate, _)| *gate).collect::<Vec<_>>(),
        [
            Gate::Rz,
            Gate::Ry,
            Gate::Rz,
            Gate::Cx,
            Gate::H,
            Gate::Cp,
            Gate::Rz,
            Gate::Crz,
        ]
    );
    assert_pi_over(applies[5].1.first().expect("cu1 parameter"), 8);
    assert_pi_over(applies[6].1.first().expect("rz parameter"), 5);
    assert_neg_rational(applies[7].1.first().expect("crz parameter"), 1, 8);
}

#[test]
fn primitive_u_uses_the_normative_su2_decomposition() {
    let program = parse(
        r#"
        OPENQASM 2.0;
        qreg q[1];
        U(0.1, pi / 3, -1.25e-3) q[0];
        "#,
    );

    let mut applies = Vec::new();
    collect_applies(&program.body, &mut applies);
    assert_eq!(
        applies.iter().map(|(gate, _)| *gate).collect::<Vec<_>>(),
        [Gate::Rz, Gate::Ry, Gate::Rz]
    );
    assert_neg_rational(&applies[0].1[0], 1, 800);
    assert_rational(&applies[1].1[0], 1, 10);
    assert_pi_over(&applies[2].1[0], 3);
}

#[test]
fn qelib_universal_gates_preserve_exact_parameters() {
    let program = parse(
        r#"
        OPENQASM 2.0;
        include "qelib1.inc";
        qreg q[1];
        u1(1e-1) q[0];
        u2(pi / 7, 0.100) q[0];
        u3(-0.5, 4611686018427387904 * pi, pi / 11) q[0];
        u(pi / 13, pi / 19, -pi / 17) q[0];
        "#,
    );

    let mut applies = Vec::new();
    collect_applies(&program.body, &mut applies);
    assert_eq!(
        applies.iter().map(|(gate, _)| *gate).collect::<Vec<_>>(),
        [
            Gate::P,
            Gate::P,
            Gate::Ry,
            Gate::P,
            Gate::P,
            Gate::Ry,
            Gate::P,
            Gate::P,
            Gate::Ry,
            Gate::P,
        ]
    );

    assert_rational(&applies[0].1[0], 1, 10);

    assert_rational(&applies[1].1[0], 1, 10);
    assert_pi_over(&applies[2].1[0], 2);
    assert_pi_over(&applies[3].1[0], 7);

    assert_pi_over(&applies[4].1[0], 11);
    assert_neg_rational(&applies[5].1[0], 1, 2);
    assert_rational_times_pi(&applies[6].1[0], 4_611_686_018_427_387_904);

    assert_eq!(
        pi_coefficient(&applies[7].1[0]),
        Some(BigRational::new((-1).into(), 17.into()))
    );
    assert_pi_over(&applies[8].1[0], 13);
    assert_pi_over(&applies[9].1[0], 19);
}

#[test]
fn cu3_lowering_includes_exact_control_phase_for_each_broadcast_pair() {
    let program = parse(
        r#"
        OPENQASM 2.0;
        include "qelib1.inc";
        qreg control[2];
        qreg target[2];
        cu3(pi / 3, pi / 5, pi / 7) control, target;
        "#,
    );

    let mut applies = Vec::new();
    collect_apply_details(&program.body, &mut applies);
    assert_eq!(applies.len(), 16);

    for (index, expansion) in applies.chunks_exact(8).enumerate() {
        assert_eq!(
            expansion
                .iter()
                .map(|(gate, _, _)| *gate)
                .collect::<Vec<_>>(),
            [
                Gate::P,
                Gate::P,
                Gate::Cx,
                Gate::P,
                Gate::Ry,
                Gate::Cx,
                Gate::Ry,
                Gate::P,
            ]
        );
        assert_eq!(expansion[0].2, [qubit(&program, "control", index)]);
        assert_eq!(
            pi_coefficient(&expansion[0].1[0]),
            Some(BigRational::new(6.into(), 35.into()))
        );
        assert_eq!(expansion[1].2, [qubit(&program, "target", index)]);
        assert_eq!(
            pi_coefficient(&expansion[1].1[0]),
            Some(BigRational::new((-1).into(), 35.into()))
        );
    }
}

#[test]
fn cu3_special_case_has_exact_cz_matrix_semantics() {
    let program = parse(
        r#"
        OPENQASM 2.0;
        include "qelib1.inc";
        qreg q[2];
        cu3(0, pi, 0) q[0], q[1];
        "#,
    );
    let control = qubit(&program, "q", 0);
    let target = qubit(&program, "q", 1);
    let mut applies = Vec::new();
    collect_apply_details(&program.body, &mut applies);

    // Track exact powers of i for every computational-basis column. The
    // resulting exponents [0, 0, 0, 2] are diag(1, 1, 1, -1), exactly CZ.
    let mut diagonal_quarter_turns = Vec::new();
    for control_input in [false, true] {
        for target_input in [false, true] {
            let control_value = control_input;
            let mut target_value = target_input;
            let mut quarter_turns = BigRational::from_integer(0.into());
            for (gate, parameters, qubits) in &applies {
                match gate {
                    Gate::P => {
                        let value = if *qubits == std::slice::from_ref(&control) {
                            control_value
                        } else {
                            assert_eq!(*qubits, std::slice::from_ref(&target));
                            target_value
                        };
                        if value {
                            quarter_turns += pi_coefficient(&parameters[0])
                                .expect("cu3 special-case phase is a rational multiple of pi")
                                * BigRational::from_integer(2.into());
                        }
                    }
                    Gate::Cx => {
                        assert_eq!(*qubits, [control.clone(), target.clone()]);
                        target_value ^= control_value;
                    }
                    Gate::Ry => assert_eq!(
                        exact_rational(&parameters[0]),
                        Some(BigRational::from_integer(0.into())),
                        "cu3(0, pi, 0) has only identity Y rotations"
                    ),
                    gate => panic!("unexpected gate in cu3 lowering: {gate:?}"),
                }
            }
            assert_eq!((control_value, target_value), (control_input, target_input));
            diagonal_quarter_turns.push(quarter_turns);
        }
    }
    assert_eq!(
        diagonal_quarter_turns,
        [
            BigRational::from_integer(0.into()),
            BigRational::from_integer(0.into()),
            BigRational::from_integer(0.into()),
            BigRational::from_integer(2.into()),
        ]
    );
}

#[test]
fn qelib_cswap_executes_as_a_controlled_swap() {
    let program = parse(
        r#"
        OPENQASM 2.0;
        include "qelib1.inc";
        qreg q[3];
        x q[0];
        x q[1];
        cswap q[0], q[1], q[2];
        "#,
    );
    let outputs = (0..3)
        .map(|index| qubit(&program, "q", index))
        .collect::<Vec<_>>();

    let state = execute(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new(outputs.clone(), []),
    )
    .expect("qelib cswap execution");

    assert_eq!(state.components.len(), 1);
    let output = &state.components[0].output.quantum;
    assert!(output[&outputs[0]].is_one());
    assert!(output[&outputs[1]].is_zero());
    assert!(output[&outputs[2]].is_one());
}

#[test]
fn canonical_qelib1_gate_surface_lowers() {
    let program = parse(
        r#"
        OPENQASM 2.0;
        include "qelib1.inc";
        qreg q[3];
        u3(pi/3, pi/5, pi/7) q[0];
        u2(pi/3, pi/5) q[0];
        u1(pi/3) q[0];
        cx q[0], q[1];
        id q[0];
        u0(2) q[0];
        u(pi/3, pi/5, pi/7) q[0];
        p(pi/3) q[0];
        x q[0];
        y q[0];
        z q[0];
        h q[0];
        s q[0];
        sdg q[0];
        t q[0];
        tdg q[0];
        rx(pi/3) q[0];
        ry(pi/3) q[0];
        rz(pi/3) q[0];
        sx q[0];
        sxdg q[0];
        cz q[0], q[1];
        cy q[0], q[1];
        swap q[0], q[1];
        ch q[0], q[1];
        ccx q[0], q[1], q[2];
        cswap q[0], q[1], q[2];
        crx(pi/3) q[0], q[1];
        cry(pi/3) q[0], q[1];
        crz(pi/3) q[0], q[1];
        cu1(pi/3) q[0], q[1];
        cp(pi/3) q[0], q[1];
        cu3(pi/3, pi/5, pi/7) q[0], q[1];
        "#,
    );

    assert!(program.operation_count() >= 33);
    let mut ids = Vec::new();
    program.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort_unstable();
    assert_eq!(ids, (0..program.ast_id_bound()).collect::<Vec<_>>());
}

#[test]
fn creg_cells_are_zero_initialized_for_symbolic_execution() {
    let program = parse(
        r#"
        OPENQASM 2.0;
        qreg q[1];
        creg result[3];
        "#,
    );
    let outputs = (0..3)
        .map(|index| bit(&program, "result", index))
        .collect::<Vec<_>>();

    let state = execute(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new([], outputs.clone()),
    )
    .expect("OpenQASM 2 creg declarations are initialized");

    assert_eq!(state.components.len(), 1);
    for output in outputs {
        assert_eq!(
            state.components[0].output.classical[&output],
            BooleanPolynomial::zero()
        );
    }
}

#[test]
fn whole_creg_conditions_use_little_endian_values() {
    let program = parse(
        r#"
        OPENQASM 2.0;
        include "qelib1.inc";
        qreg q[4];
        creg c[2];
        if (c == 4) x q[3];
        x q[0];
        measure q[0] -> c[1];
        if (c == 2) x q[1];
        if (c == 1) x q[2];
        "#,
    );
    let quantum_outputs = (1..4)
        .map(|index| qubit(&program, "q", index))
        .collect::<Vec<_>>();
    let classical_outputs = (0..2)
        .map(|index| bit(&program, "c", index))
        .collect::<Vec<_>>();

    let state = execute(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new(quantum_outputs.clone(), classical_outputs.clone()),
    )
    .expect("whole-creg conditional execution");

    assert_eq!(state.components.len(), 1);
    let output = &state.components[0].output;
    assert!(output.quantum[&quantum_outputs[0]].is_one());
    assert!(output.quantum[&quantum_outputs[1]].is_zero());
    assert!(output.quantum[&quantum_outputs[2]].is_zero());
    assert!(output.classical[&classical_outputs[0]].is_zero());
    assert!(output.classical[&classical_outputs[1]].is_one());
}

#[test]
fn register_broadcast_reset_and_measure_execute_through_shared_ir() {
    let program = parse(
        r#"
        OPENQASM 2.0;
        include "qelib1.inc";
        qreg control[1];
        qreg target[3];
        qreg scratch[2];
        creg observed[3];
        creg cleared[2];
        x control[0];
        cx control[0], target;
        reset target[1];
        x scratch;
        reset scratch;
        measure target -> observed;
        measure scratch -> cleared;
        "#,
    );
    let target_outputs = (0..3)
        .map(|index| qubit(&program, "target", index))
        .collect::<Vec<_>>();
    let scratch_outputs = (0..2)
        .map(|index| qubit(&program, "scratch", index))
        .collect::<Vec<_>>();
    let observed = (0..3)
        .map(|index| bit(&program, "observed", index))
        .collect::<Vec<_>>();
    let cleared = (0..2)
        .map(|index| bit(&program, "cleared", index))
        .collect::<Vec<_>>();
    let selected_qubits = target_outputs
        .iter()
        .chain(&scratch_outputs)
        .cloned()
        .collect::<Vec<_>>();
    let selected_bits = observed.iter().chain(&cleared).cloned().collect::<Vec<_>>();

    let state = execute(
        &program,
        &ExecutionConfig::zero(),
        &OutputSelection::new(selected_qubits, selected_bits),
    )
    .expect("broadcast/reset/measurement execution");

    assert_eq!(state.components.len(), 1);
    let output = &state.components[0].output;
    for (index, expected) in [true, false, true].into_iter().enumerate() {
        assert_eq!(
            output.quantum[&target_outputs[index]],
            BooleanPolynomial::from(expected)
        );
        assert_eq!(
            output.classical[&observed[index]],
            BooleanPolynomial::from(expected)
        );
    }
    for (scratch, cleared) in scratch_outputs.iter().zip(&cleared) {
        assert!(output.quantum[scratch].is_zero());
        assert!(output.classical[cleared].is_zero());
    }
}

#[test]
fn ast_ids_remain_unique_and_dense_after_expansion() {
    let program = parse(
        r#"
        OPENQASM 2.0;
        include "qelib1.inc";
        qreg control[1];
        qreg target[3];
        creg c[3];
        u3(pi / 3, 0.125, -1e-2) target;
        cu3(pi / 5, pi / 7, -pi / 11) control[0], target[0];
        u0(pi / 13) target[0];
        id target[1];
        barrier target;
        cx control[0], target;
        measure target -> c;
        if (c == 5) reset target;
        "#,
    );

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
fn ill_formed_or_unsupported_sources_are_rejected_without_panics() {
    let cases = [
        (
            "unsupported-include",
            r#"OPENQASM 2.0; include "stdgates.inc"; qreg q[1];"#,
        ),
        ("unsupported-version", "OPENQASM 3.0; qreg q[1];"),
        ("missing-version", "qreg q[1];"),
        ("qasm3-declaration", "OPENQASM 2.0; qubit[1] q; bit[1] c;"),
        (
            "unknown-gate",
            r#"OPENQASM 2.0; include "qelib1.inc"; qreg q[1]; mystery q[0];"#,
        ),
        (
            "missing-gate-operand",
            r#"OPENQASM 2.0; include "qelib1.inc"; qreg q[2]; cx q[0];"#,
        ),
        (
            "missing-gate-parameter",
            r#"OPENQASM 2.0; include "qelib1.inc"; qreg q[1]; rx q[0];"#,
        ),
        (
            "extra-gate-parameter",
            r#"OPENQASM 2.0; include "qelib1.inc"; qreg q[1]; rx(pi, 0) q[0];"#,
        ),
        (
            "gate-register-width-mismatch",
            r#"OPENQASM 2.0; include "qelib1.inc"; qreg a[2]; qreg b[3]; cx a, b;"#,
        ),
        (
            "measurement-width-mismatch",
            "OPENQASM 2.0; qreg q[2]; creg c[3]; measure q -> c;",
        ),
        (
            "measurement-shape-mismatch",
            "OPENQASM 2.0; qreg q[2]; creg c[2]; measure q -> c[0];",
        ),
        (
            "out-of-bounds-index",
            r#"OPENQASM 2.0; include "qelib1.inc"; qreg q[2]; x q[2];"#,
        ),
        (
            "out-of-bounds-barrier-index",
            "OPENQASM 2.0; qreg q[1]; barrier q[1];",
        ),
        ("missing-barrier-operand", "OPENQASM 2.0; barrier;"),
        (
            "unknown-operand",
            r#"OPENQASM 2.0; include "qelib1.inc"; qreg q[1]; x missing[0];"#,
        ),
        (
            "wrong-operand-type",
            r#"OPENQASM 2.0; include "qelib1.inc"; creg c[1]; x c[0];"#,
        ),
        (
            "wrong-measurement-target-type",
            "OPENQASM 2.0; qreg q[1]; measure q[0] -> q[0];",
        ),
        (
            "duplicate-operand",
            r#"OPENQASM 2.0; include "qelib1.inc"; qreg q[1]; cx q[0], q[0];"#,
        ),
        (
            "duplicate-identifier",
            "OPENQASM 2.0; qreg value[1]; creg value[1];",
        ),
        (
            "invalid-qasm2-identifier",
            "OPENQASM 2.0; qreg Uppercase[1];",
        ),
        ("zero-register-width", "OPENQASM 2.0; qreg q[0];"),
        (
            "malformed-condition",
            r#"OPENQASM 2.0; include "qelib1.inc"; qreg q[1]; creg c[1]; if (c ==) x q[0];"#,
        ),
        (
            "missing-measurement-target",
            "OPENQASM 2.0; qreg q[1]; measure q[0];",
        ),
    ];

    for (label, source) in cases {
        assert_rejected_without_panicking(label, source);
    }
}
