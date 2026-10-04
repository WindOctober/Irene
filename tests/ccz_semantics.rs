mod common;
use common::unitary::assert_action;
use irene::equivalence::{Endpoint, EquivalenceConfig, InputPair, OutputPair, Verdict, analyze};
use irene::frontend::{openqasm2, openqasm3};
use irene::ir::{ClassicalBit, Program, Qubit};

fn parse(version: u8, body: &str, classical: bool) -> Result<Program, String> {
    let declarations = if version == 2 {
        "include \"qelib1.inc\"; qreg q[4];"
    } else {
        "include \"stdgates.inc\"; qubit[4] q;"
    };
    let storage = if !classical {
        ""
    } else if version == 2 {
        "creg c[1];"
    } else {
        "bit[1] c;"
    };
    let source = format!("OPENQASM {version}.0; {declarations} {storage} {body}");
    if version == 2 {
        openqasm2::parse_str(&source, "ccz-test.qasm").map_err(|e| format!("{e:?}"))
    } else {
        openqasm3::parse_str(&source, "ccz-test.qasm").map_err(|e| format!("{e:?}"))
    }
}

#[test]
fn ccz_has_diagonal_phase_for_all_operand_orders() {
    for version in [2, 3] {
        for [a, b, c] in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            let program = parse(version, &format!("ccz q[{a}],q[{b}],q[{c}];"), false).unwrap();
            assert_action(&program, |state| {
                for (i, value) in state.iter_mut().enumerate() {
                    if i & 7 == 7 {
                        *value = (-value.0, -value.1);
                    }
                }
            });
        }
    }
}

#[test]
fn two_ccz_gates_cancel() {
    for version in [2, 3] {
        let p = parse(version, "ccz q[0],q[1],q[2]; ccz q[0],q[1],q[2];", false).unwrap();
        assert_action(&p, |_| {});
    }
}

#[test]
fn feedback_ccz_preserves_observed_classical_output_and_relative_phase() {
    for version in [2, 3] {
        let condition = if version == 2 { "c == 1" } else { "c[0]" };
        let prefix = "h q[3]; measure q[3] -> c[0];";
        let left = parse(
            version,
            &format!("{prefix} if ({condition}) ccz q[0],q[1],q[2];"),
            true,
        )
        .unwrap();
        for wrong in [false, true] {
            let suffix = if wrong {
                String::new()
            } else {
                format!(
                    "if ({condition}) h q[2]; if ({condition}) ccx q[0],q[1],q[2]; if ({condition}) h q[2];"
                )
            };
            let right = parse(version, &format!("{prefix} {suffix}"), true).unwrap();
            let quantum = |p: &Program, index| {
                Endpoint::Quantum(Qubit {
                    register: p.quantum_registers[0].id,
                    index,
                })
            };
            let classical = |p: &Program| {
                Endpoint::Classical(ClassicalBit {
                    register: p.classical_registers[0].id,
                    index: 0,
                })
            };
            let config = EquivalenceConfig {
                input_pairs: (0..4)
                    .map(|i| InputPair {
                        left: quantum(&left, i),
                        right: quantum(&right, i),
                    })
                    .collect(),
                output_pairs: (0..4)
                    .map(|i| OutputPair {
                        left: quantum(&left, i),
                        right: quantum(&right, i),
                    })
                    .chain([OutputPair {
                        left: classical(&left),
                        right: classical(&right),
                    }])
                    .collect(),
                ..Default::default()
            };
            assert_eq!(
                analyze(&left, &right, &config).unwrap().verdict,
                if wrong {
                    Verdict::NotEquivalent
                } else {
                    Verdict::Equivalent
                }
            );
        }
    }
}

#[test]
fn ccz_rejects_invalid_parameters_arity_and_operands() {
    for version in [2, 3] {
        for body in [
            "ccz q[0],q[1];",
            "ccz q[0],q[1],q[2],q[3];",
            "ccz(pi) q[0],q[1],q[2];",
            "ccz q[0],q[0],q[2];",
            "ccz q[0],q[1],q[4];",
            "ccz q[0],q[1],c[0];",
            "ccz q[0],q[1],missing;",
        ] {
            assert!(
                parse(version, body, true).is_err(),
                "OpenQASM {version}: {body}"
            );
        }
    }
}
