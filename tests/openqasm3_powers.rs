mod common;
use common::unitary::{assert_fresh_ids, assert_same};
use irene::frontend::openqasm3::parse_str;
use irene::ir::Program;

fn parse(body: &str) -> Program {
    parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {body}"),
        "powers",
    )
    .unwrap()
}

#[test]
fn integer_powers_and_inverses_match_explicit_repetition() {
    for (gate, inverse) in [
        ("h q[0];", "h q[0];"),
        ("x q[0];", "x q[0];"),
        ("y q[0];", "y q[0];"),
        ("z q[0];", "z q[0];"),
        ("s q[0];", "sdg q[0];"),
        ("sdg q[0];", "s q[0];"),
        ("t q[0];", "tdg q[0];"),
        ("tdg q[0];", "t q[0];"),
        ("p(pi/7) q[0];", "p(-pi/7) q[0];"),
        ("rx(pi/7) q[0];", "rx(-pi/7) q[0];"),
        ("ry(pi/7) q[0];", "ry(-pi/7) q[0];"),
        ("rz(pi/7) q[0];", "rz(-pi/7) q[0];"),
        ("cx q[1],q[0];", "cx q[1],q[0];"),
        ("cy q[1],q[0];", "cy q[1],q[0];"),
        ("cz q[1],q[0];", "cz q[1],q[0];"),
        ("swap q[1],q[0];", "swap q[1],q[0];"),
        ("cp(pi/7) q[1],q[0];", "cp(-pi/7) q[1],q[0];"),
        ("crx(pi/7) q[1],q[0];", "crx(-pi/7) q[1],q[0];"),
        ("cry(pi/7) q[1],q[0];", "cry(-pi/7) q[1],q[0];"),
        ("crz(pi/7) q[1],q[0];", "crz(-pi/7) q[1],q[0];"),
        ("ccx q[2],q[0],q[1];", "ccx q[2],q[0],q[1];"),
        ("ccz q[2],q[0],q[1];", "ccz q[2],q[0],q[1];"),
        ("ch q[1],q[0];", "ch q[1],q[0];"),
        ("cswap q[2],q[0],q[1];", "cswap q[2],q[0],q[1];"),
    ] {
        for k in -3_i32..=3 {
            let p = parse(&format!("pow({k}) @ {gate}"));
            let reference =
                parse(&(if k < 0 { inverse } else { gate }).repeat(k.unsigned_abs() as usize));
            assert_same(&p, &reference);
            assert_fresh_ids(&p);
        }
        assert_same(&parse(&format!("inv @ {gate}")), &parse(inverse));
        assert_same(&parse(&format!("inv @ inv @ {gate}")), &parse(gate));
    }
}

#[test]
fn controls_and_modifiers_preserve_relative_phase_and_noncommuting_decompositions() {
    for (gate, inverse, operands) in [
        ("h", "h", "q[0],q[1]"),
        ("swap", "swap", "q[0],q[1],q[2]"),
        ("s", "sdg", "q[0],q[1]"),
        ("t", "tdg", "q[0],q[1]"),
        ("rx(pi/3)", "rx(-pi/3)", "q[0],q[1]"),
        ("rz(pi/3)", "rz(-pi/3)", "q[0],q[1]"),
    ] {
        for k in -3_i32..=3 {
            let reference = parse(
                &format!("ctrl @ {} {operands};", if k < 0 { inverse } else { gate })
                    .repeat(k.unsigned_abs() as usize),
            );
            for prefix in [format!("ctrl @ pow({k})"), format!("pow({k}) @ ctrl")] {
                let p = parse(&format!("{prefix} @ {gate} {operands};"));
                assert_same(&p, &reference);
                assert_fresh_ids(&p);
            }
        }
        assert_same(
            &parse(&format!("ctrl @ inv @ {gate} {operands};")),
            &parse(&format!("ctrl @ {inverse} {operands};")),
        );
    }
    assert_same(&parse("inv @ pow(-2) @ t q[0];"), &parse("s q[0];"));
    assert_same(
        &parse("pow(0x2) @ pow(0b11) @ t q[0];"),
        &parse("sdg q[0];"),
    );
    assert_same(&parse("pow((-2)) @ x q[0];"), &parse(""));
}

#[test]
fn powered_broadcast_preserves_all_wires_and_fresh_ids() {
    let p = parse("inv @ ry(pi/7) q;");
    assert_same(
        &p,
        &parse("ry(-pi/7) q[0]; ry(-pi/7) q[1]; ry(-pi/7) q[2];"),
    );
    assert_fresh_ids(&p);
}

#[test]
fn cu_identity_powers_preserve_the_control_phase() {
    let gate = "cu(pi/2,pi/4,pi/8,pi/16) q[0],q[1];";
    for modifier in ["pow(1)", "inv @ pow(-1)", "inv @ inv"] {
        let p = parse(&format!("{modifier} @ {gate}"));
        assert_same(&p, &parse(gate));
        assert_fresh_ids(&p);
    }
    let p = parse(&format!("pow(0) @ {gate}"));
    assert_same(&p, &parse(""));
    assert_fresh_ids(&p);
}

#[test]
fn zero_power_still_validates_the_gate_interface() {
    for body in [
        "pow(0) @ unknown q[0];",
        "pow(0) @ h(1) q[0];",
        "pow(0) @ rx q[0];",
        "pow(0) @ x q[3];",
        "pow(0) @ ctrl @ x q[0],q[0];",
        "pow(0) @ cu(1,2,3) q[0],q[1];",
    ] {
        let source = format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {body}");
        assert!(parse_str(&source, "bad-power").is_err(), "{body}");
    }
}
