mod common;

#[test]
fn decomposed_controls_broadcast_over_distinct_registers() {
    for (name, gate) in [
        ("h", Gate::H),
        ("s", Gate::S),
        ("sdg", Gate::Sdg),
        ("t", Gate::T),
        ("tdg", Gate::Tdg),
    ] {
        let p = parse_str(
            &format!(
                "OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] a; qubit[2] b; ctrl @ {name} a,b;"
            ),
            "broadcast",
        )
        .unwrap();
        assert_action(&p, |state| {
            for i in 0..2 {
                apply(state, &[i], i + 2, single(gate, 0.0));
            }
        });
        assert_fresh_ids(&p);
    }
    let p = parse_str("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] a; qubit[2] b; qubit[2] c; ctrl @ swap a,b,c;","broadcast").unwrap();
    assert_action(&p, |state| {
        for i in 0..2 {
            let (control, a, b) = (1 << i, 1 << (i + 2), 1 << (i + 4));
            for j in 0..state.len() {
                if j & control != 0 && j & a == 0 && j & b != 0 {
                    state.swap(j, j ^ a ^ b);
                }
            }
        }
    });
    assert_fresh_ids(&p);
}
use common::unitary::{apply, assert_action, assert_fresh_ids, single};
use irene::frontend::openqasm3::parse_str;
use irene::ir::{Gate, Program};
use std::f64::consts::PI;

fn parse(body: &str) -> Program {
    parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {body}"),
        "controls",
    )
    .unwrap()
}

#[test]
fn positive_controls_preserve_parameters_and_operand_order() {
    for (name, params, gate) in [
        ("x", "", Gate::X),
        ("y", "", Gate::Y),
        ("z", "", Gate::Z),
        ("p", "(pi/7)", Gate::P),
        ("phase", "(pi/7)", Gate::P),
        ("u1", "(pi/7)", Gate::P),
        ("rx", "(pi/7)", Gate::Rx),
        ("ry", "(pi/7)", Gate::Ry),
        ("rz", "(pi/7)", Gate::Rz),
    ] {
        for modifier in ["ctrl", "ctrl(1)"] {
            let p = parse(&format!("{modifier} @ {name}{params} q[2],q[0];"));
            assert_action(&p, |state| apply(state, &[2], 0, single(gate, PI / 7.0)));
            assert_fresh_ids(&p);
        }
    }
    for (call, base) in [
        ("ctrl @ cx", Gate::X),
        ("ctrl @ cz", Gate::Z),
        ("ctrl(2) @ x", Gate::X),
        ("ctrl(2) @ z", Gate::Z),
        ("ctrl @ ctrl @ x", Gate::X),
        ("ctrl @ ctrl @ z", Gate::Z),
        ("ctrl(0x2) @ x", Gate::X),
    ] {
        let p = parse(&format!("{call} q[1],q[2],q[0];"));
        assert_action(&p, |state| apply(state, &[1, 2], 0, single(base, 0.0)));
        assert_fresh_ids(&p);
    }
}

#[test]
fn controlled_broadcast_preserves_distinct_register_cells() {
    let p = parse_str(
        "OPENQASM 3.0; include \"stdgates.inc\"; qubit c; qubit[2] q; ctrl @ ry(pi/7) c,q;",
        "broadcast",
    )
    .unwrap();
    assert_action(&p, |state| {
        apply(state, &[0], 1, single(Gate::Ry, PI / 7.0));
        apply(state, &[0], 2, single(Gate::Ry, PI / 7.0));
    });
    assert_fresh_ids(&p);
}

#[test]
fn controlled_decompositions_preserve_unitaries() {
    for (body, gate) in [
        ("ctrl @ h q[0],q[1];", Gate::H),
        ("ch q[0],q[1];", Gate::H),
        ("ctrl @ s q[0],q[1];", Gate::S),
        ("ctrl @ sdg q[0],q[1];", Gate::Sdg),
        ("ctrl @ t q[0],q[1];", Gate::T),
        ("ctrl @ tdg q[0],q[1];", Gate::Tdg),
    ] {
        let p = parse(body);
        assert_action(&p, |state| apply(state, &[0], 1, single(gate, 0.0)));
        assert_fresh_ids(&p);
    }
    for body in ["ctrl @ swap q[0],q[1],q[2];", "cswap q[0],q[1],q[2];"] {
        let p = parse(body);
        assert_action(&p, |state| state.swap(3, 5));
        assert_fresh_ids(&p);
    }
}

#[test]
fn invalid_control_counts_and_operands_are_rejected() {
    for instruction in [
        "ctrl(0) @ x q[0]",
        "ctrl(-1) @ x q[0]",
        "ctrl(1.0) @ x q[0],q[1]",
        "ctrl @ ry q[0],q[1]",
        "ctrl @ x q[0]",
        "ctrl @ x q[0],q[0]",
        "ctrl @ ry(pi/3) q,q[0]",
    ] {
        assert!(
            parse_str(
                &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[4] q; {instruction};"),
                "invalid-controls"
            )
            .is_err(),
            "{instruction}"
        );
    }
    assert!(
        parse_str(
            "OPENQASM 3.0; qubit[2] q; ctrl @ x q[0],q[1];",
            "missing-include"
        )
        .is_err()
    );
    assert!(
        parse_str(
            "OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] a; qubit[3] b; ctrl @ x a,b;",
            "width-mismatch"
        )
        .is_err()
    );
}

#[test]
fn extended_controls_are_rejected_or_have_the_specified_action() {
    // Unsupported legal syntax may be implemented later, but never silently ignored.
    for (body, controls, target, gate) in [
        ("ctrl(1+0) @ x q[0],q[1];", vec![0], 1, Gate::X),
        (
            "ctrl(3) @ x q[0],q[1],q[2],q[3];",
            vec![0, 1, 2],
            3,
            Gate::X,
        ),
        (
            "ctrl @ ctrl @ ctrl @ x q[0],q[1],q[2],q[3];",
            vec![0, 1, 2],
            3,
            Gate::X,
        ),
        (
            "ctrl(2) @ ry(pi/3) q[0],q[1],q[2];",
            vec![0, 1],
            2,
            Gate::Ry,
        ),
        ("ctrl(2) @ h q[0],q[1],q[2];", vec![0, 1], 2, Gate::H),
        ("ctrl @ gphase(pi/3) q[0];", vec![], 0, Gate::P),
    ] {
        if let Ok(p) = parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[4] q; {body}"),
            "extended-controls",
        ) {
            assert_action(&p, |state| {
                apply(state, &controls, target, single(gate, PI / 3.0))
            });
        }
    }
    if let Ok(p) = parse_str(
        "OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; negctrl @ x q[0],q[1];",
        "negative-control",
    ) {
        assert_action(&p, |state| state.swap(0, 2));
    }
    if let Ok(p) = parse_str(
        "OPENQASM 3.0; include \"stdgates.inc\"; qubit q; pow(0.5) @ x q;",
        "fractional-power",
    ) {
        assert_action(&p, |state| {
            apply(
                state,
                &[],
                0,
                [[(0.5, 0.5), (0.5, -0.5)], [(0.5, -0.5), (0.5, 0.5)]],
            )
        });
    }
}
