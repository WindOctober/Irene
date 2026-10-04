mod common;
use common::unitary::{apply, assert_action, assert_fresh_ids, assert_same, single};
use irene::frontend::openqasm2;
use irene::ir::{Gate, Program};

fn parse(body: &str) -> Program {
    openqasm2::parse_str(
        &format!("OPENQASM 2.0; include \"qelib1.inc\"; {body}"),
        "custom-gate-scope.qasm",
    )
    .unwrap()
}

const DEFINITIONS: &str = "gate inner(theta) a,b { p(theta) a; cx a,b; }
     gate outer(theta) a,b { inner(theta/2) b,a; p(theta) a; }
     qreg q[2]; qreg r[2]; qreg theta[1];";

#[test]
fn empty_barriers_in_gate_bodies_remain_noops() {
    let program = parse("gate g a { barrier; x a; barrier a; } qreg q[1]; g q;");
    assert_action(&program, |state| apply(state, &[], 0, single(Gate::X, 0.0)));
}

#[test]
fn nested_frames_preserve_unitary_semantics_and_fresh_ids() {
    let left = parse(&format!(
        "{DEFINITIONS} outer(pi/2) q,r; outer(pi/4) r[0],q[1];"
    ));
    let right = parse(
        "qreg q[2]; qreg r[2]; qreg theta[1];
         p(pi/4) r[0]; cx r[0],q[0]; p(pi/2) q[0];
         p(pi/4) r[1]; cx r[1],q[1]; p(pi/2) q[1];
         p(pi/8) q[1]; cx q[1],r[0]; p(pi/4) r[0];",
    );
    assert_same(&left, &right);
    assert_fresh_ids(&left);
}

#[test]
fn scalar_operands_broadcast_without_capturing_registers() {
    let program = parse("gate g a,b { cx a,b; } qreg a[1]; qreg b[2]; g a[0],b;");
    // Check the declared interface, not the number or placement of IR gates.
    assert_eq!(
        program
            .quantum_registers
            .iter()
            .map(|r| (r.name.as_str(), r.width))
            .collect::<Vec<_>>(),
        vec![("a", 1), ("b", 2)]
    );
    assert_action(&program, |state| {
        apply(state, &[0], 1, single(Gate::X, 0.0));
        apply(state, &[0], 2, single(Gate::X, 0.0));
    });
    assert_fresh_ids(&program);
}
