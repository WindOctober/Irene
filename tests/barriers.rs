use irene::equivalence::{Endpoint, EquivalenceConfig, InputPair, OutputPair, Verdict, analyze};
use irene::frontend::{openqasm2, openqasm3};
use irene::ir::{Program, Qubit};

fn source(version: u8, body: &str) -> String {
    let declarations = if version == 2 {
        "include \"qelib1.inc\"; qreg q[2]; creg c[1];"
    } else {
        "include \"stdgates.inc\"; qubit[2] q; bit[1] c; c[0] = false;"
    };
    format!("OPENQASM {version}.0; {declarations} {body}")
}

fn parse(version: u8, body: &str) -> Program {
    let text = source(version, body);
    if version == 2 {
        openqasm2::parse_str(&text, "barriers.qasm").unwrap()
    } else {
        openqasm3::parse_str(&text, "barriers.qasm").unwrap()
    }
}

#[test]
fn barriers_preserve_coherence_and_feedback_channels() {
    for version in [2, 3] {
        for measured in [false, true] {
            let prefix = if measured {
                "measure q[0] -> c[0];"
            } else {
                ""
            };
            let conditional = if version == 2 {
                "if (c == 1) barrier q; if (c == 0) barrier;"
            } else {
                "if (c[0]) { barrier q; } else { barrier; }"
            };
            let left = parse(version, &format!("h q[0]; {prefix} cx q[0],q[1]; h q[0];"));
            for wrong in [false, true] {
                let suffix = if wrong { "x q[1];" } else { "" };
                let right = parse(
                    version,
                    &format!(
                        "barrier; h q[0]; barrier q; {prefix} {conditional}
                     cx q[0],q[1]; barrier q[0],q[1]; h q[0]; barrier; {suffix}"
                    ),
                );
                let endpoint = |p: &Program, index| {
                    Endpoint::Quantum(Qubit {
                        register: p.quantum_registers[0].id,
                        index,
                    })
                };
                let config = EquivalenceConfig {
                    input_pairs: (0..2)
                        .map(|i| InputPair {
                            left: endpoint(&left, i),
                            right: endpoint(&right, i),
                        })
                        .collect(),
                    output_pairs: (0..2)
                        .map(|i| OutputPair {
                            left: endpoint(&left, i),
                            right: endpoint(&right, i),
                        })
                        .collect(),
                    ..EquivalenceConfig::default()
                };
                let result = analyze(&left, &right, &config).unwrap();
                assert_eq!(
                    result.verdict,
                    if wrong {
                        Verdict::NotEquivalent
                    } else {
                        Verdict::Equivalent
                    },
                    "version={version}, measured={measured}, wrong={wrong}: {result:?}"
                );
            }
        }
    }
}

#[test]
fn barrier_operands_still_require_valid_quantum_references() {
    for version in [2, 3] {
        for body in ["barrier missing;", "barrier q[2];", "barrier c;"] {
            let text = source(version, body);
            let rejected = if version == 2 {
                openqasm2::parse_str(&text, "invalid-barrier.qasm").is_err()
            } else {
                openqasm3::parse_str(&text, "invalid-barrier.qasm").is_err()
            };
            assert!(rejected, "version={version}: {body}");
        }
    }
}
