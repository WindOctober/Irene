mod common;

use common::unitary::{assert_fresh_ids, assert_same};
use irene::frontend::openqasm3::parse_str;
use irene::ir::{Block, Gate, Program, StatementKind};

fn parse(body: &str) -> Program {
    let p = parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; {body}"),
        "known-powers.qasm",
    )
    .unwrap();
    assert_fresh_ids(&p);
    p
}

// Only for the measurement-free fixtures below: classical assignments have
// already served to determine powers. Compare the resulting quantum action
// with the independent matrix oracle, including global phase.
fn remove_assignments(block: &mut Block) {
    block
        .statements
        .retain(|s| !matches!(s.kind, StatementKind::Assign { .. }));
    for s in &mut block.statements {
        match &mut s.kind {
            StatementKind::Scope(b) => remove_assignments(b),
            StatementKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                remove_assignments(then_branch);
                remove_assignments(else_branch);
            }
            _ => {}
        }
    }
}

fn compare_quantum_action(body: &str, reference: &str) {
    let mut p = parse(body);
    remove_assignments(&mut p.body);
    assert_same(&p, &parse(reference));
}

fn count_x(block: &Block) -> usize {
    block
        .statements
        .iter()
        .map(|s| match &s.kind {
            StatementKind::Apply { gate: Gate::X, .. } => 1,
            StatementKind::Scope(b) => count_x(b),
            StatementKind::If {
                then_branch,
                else_branch,
                ..
            } => count_x(then_branch) + count_x(else_branch),
            _ => 0,
        })
        .sum()
}

#[test]
fn assignments_and_loop_updates_determine_powers() {
    compare_quantum_action(
        "uint[3] k=1; for uint i in [0:3] { pow(k) @ p(pi/8) q[0]; k <<= 1; }",
        "p(7*pi/8) q[0];",
    );
    compare_quantum_action(
        "uint[3] k=1; pow(k<<1) @ x q[0]; pow(k) @ x q[1];",
        "x q[1];",
    );
    compare_quantum_action(
        "uint[3] k=3; uint[3] mask=1; k ^= mask; pow(k) @ t q[0];",
        "s q[0];",
    );
}

#[test]
fn known_conditions_and_local_shadowing_preserve_values() {
    compare_quantum_action(
        "uint[3] k=1; if(true) { uint[3] k=2; pow(k) @ x q[0]; } pow(k) @ x q[1];",
        "x q[1];",
    );
    compare_quantum_action("uint[3] k=1; if(true) { k=2; } pow(k) @ x q[0];", "");
    compare_quantum_action(
        "uint[3] k=1; if(false) { k=2; } pow(k) @ x q[0];",
        "x q[0];",
    );
}

#[test]
fn unknown_condition_keeps_only_agreeing_branch_values() {
    let p = parse(
        "h q[0]; bit b=measure q[0]; uint[3] k=1; if(b) { k=2; } else { k=2; } pow(k) @ x q[1];",
    );
    assert_eq!(count_x(&p.body), 0);
}

#[test]
fn else_branch_starts_from_the_branch_entry_state() {
    let p =
        parse("h q[0]; bit b=measure q[0]; uint[3] k=1; if(b) { k=2; } else { pow(k) @ x q[1]; }");
    let branch = p
        .body
        .statements
        .iter()
        .find_map(|s| match &s.kind {
            StatementKind::If {
                then_branch,
                else_branch,
                ..
            } => Some((then_branch, else_branch)),
            _ => None,
        })
        .unwrap();
    assert_eq!(count_x(branch.0), 0);
    assert_eq!(count_x(branch.1), 1);
}

#[test]
fn unknown_and_invalid_powers_are_rejected() {
    for body in [
        "uint[3] k; pow(k) @ x q[0];",
        "bit b=measure q[0]; uint[3] k=1; if(b) { k=2; } pow(k) @ x q[0];",
        "uint[3] k=1; measure q[0] -> k[0]; pow(k) @ x q[0];",
        "uint[3] k=1; bit b=measure q[0]; if(b) { k=2; } else { pow(k-1) @ x q[0]; }",
        "pow(0.5) @ x q[0];",
        "pow(2.0) @ x q[0];",
        "pow(0) @ bogus q[0];",
        "pow(0) @ x q[0],q[1];",
        "uint[3] k=2; bit[k] b; pow(k) @ x q[0];",
    ] {
        assert!(
            parse_str(
                &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; {body}"),
                "invalid-power.qasm",
            )
            .is_err(),
            "{body}"
        );
    }
}
