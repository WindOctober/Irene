mod common;
use common::unitary::{apply, assert_action, assert_fresh_ids, u};
use irene::frontend::openqasm3;
use std::f64::consts::PI;

#[test]
fn broadcast_preserves_angles_and_wire_identity() {
    for control in ["a", "a[0]"] {
        let p = openqasm3::parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] a; qubit[2] b; cu(pi/2,pi/4,pi/8,pi/16) {control},b;"),
            "broadcast",
        ).unwrap();
        assert_action(&p, |state| {
            for index in 0..2 {
                apply(
                    state,
                    &[if control == "a" { index } else { 0 }],
                    2 + index,
                    u(PI / 2.0, PI / 4.0, PI / 8.0, PI / 16.0),
                );
            }
        });
        assert_fresh_ids(&p);
    }
}

#[test]
fn invalid_calls_are_rejected() {
    for body in [
        "cu(1,2,3) q[0],q[1];",
        "cu(1,2,3,4,5) q[0],q[1];",
        "cu(1,2,3,4) q[0];",
        "cu(1,2,3,4) q[0],q[1],q[2];",
        "cu(1,2,3,4) q[0],q[0];",
        "cu(1,2,3,4) q[0],q[3];",
        "cu(1,2,3,4) q[0],missing;",
        "cu(1,2,3,4) q[0],c;",
        "cu(1,2,3,4) q,r;",
    ] {
        let source = format!(
            "OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; qubit[2] r; bit c; {body}"
        );
        assert!(
            openqasm3::parse_str(&source, "invalid-cu").is_err(),
            "{body}"
        );
    }
    assert!(
        openqasm3::parse_str(
            "OPENQASM 3.0; qubit[2] q; cu(1,2,3,4) q[0],q[1];",
            "missing-include"
        )
        .is_err()
    );
}

#[test]
fn cu_modifiers_are_rejected_or_preserve_the_full_operator() {
    // Inversion reverses the whole product; powers do not scale each Euler angle.
    let matrix = u(PI / 2.0, PI / 4.0, PI / 8.0, PI / 16.0);
    for modifier in ["inv", "pow(2)", "ctrl"] {
        let operands = if modifier == "ctrl" {
            "q[0],q[1],q[2]"
        } else {
            "q[0],q[1]"
        };
        let source = format!(
            "OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {modifier} @ cu(pi/2,pi/4,pi/8,pi/16) {operands};"
        );
        if let Ok(p) = openqasm3::parse_str(&source, "modified-cu") {
            assert_action(&p, |state| match modifier {
                "ctrl" => apply(state, &[0, 1], 2, matrix),
                "pow(2)" => {
                    apply(state, &[0], 1, matrix);
                    apply(state, &[0], 1, matrix);
                }
                _ => apply(
                    state,
                    &[0],
                    1,
                    std::array::from_fn(|i| {
                        std::array::from_fn(|j| (matrix[j][i].0, -matrix[j][i].1))
                    }),
                ),
            });
        }
    }
}
