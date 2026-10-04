use irene::equivalence::{
    Endpoint, EquivalenceConfig, Evidence, InputPair, OutputPair, Verdict, analyze,
    prepare_comparison,
};
use irene::frontend::openqasm3;
use irene::ir::{ClassicalBit, Program, Qubit};

fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0;\ninclude \"stdgates.inc\";\n{body}"),
        "equivalence-test.qasm",
    )
    .expect("valid test program")
}

#[test]
fn compact_xag_proofs_do_not_require_polynomial_kernel_lowering() {
    // A conjunction of 20 complemented inputs has 2^20 ANF terms.
    const N: usize = 20;
    let circuit = |gate: &str, reverse: bool| {
        let controls = if reverse {
            (0..N).rev().collect::<Vec<_>>()
        } else {
            (0..N).collect()
        };
        let flips = (0..N).map(|i| format!("x q[{i}];")).collect::<String>();
        let mut chain = vec![format!(
            "ccx q[{}],q[{}],q[{}];",
            controls[0],
            controls[1],
            N + 1
        )];
        for (i, control) in controls.iter().enumerate().skip(2) {
            chain.push(format!("ccx q[{}],q[{control}],q[{}];", N + i - 1, N + i));
        }
        parse(&format!(
            "qubit[{}] q; {flips} {} {gate} q[{}],q[{N}]; {} {flips}",
            2 * N,
            chain.join(" "),
            2 * N - 1,
            chain.into_iter().rev().collect::<String>()
        ))
    };
    for gate in ["cx", "cp(pi/4)"] {
        let left = circuit(gate, false);
        let right = circuit(gate, true);
        let config = EquivalenceConfig {
            input_pairs: (0..=N)
                .map(|i| InputPair {
                    left: Endpoint::Quantum(qubit_at(&left, "q", i)),
                    right: Endpoint::Quantum(qubit_at(&right, "q", i)),
                })
                .collect(),
            output_pairs: (0..=N)
                .map(|i| OutputPair {
                    left: Endpoint::Quantum(qubit_at(&left, "q", i)),
                    right: Endpoint::Quantum(qubit_at(&right, "q", i)),
                })
                .collect(),
            ..EquivalenceConfig::default()
        };
        let result = analyze(&left, &right, &config).unwrap();
        assert_eq!(result.verdict, Verdict::Equivalent, "{gate}: {result:?}");
        assert!(matches!(
            result.evidence,
            Evidence::ExactHps | Evidence::DeterministicExact
        ));
        assert_eq!(result.kernel_terms, (0, 0));
    }
}

#[test]
fn certified_xag_output_equality_is_reused_for_classical_snapshots() {
    let left = parse(
        "qubit[4] q; bit[4] c; ccx q[0],q[1],q[3]; x q[0]; ccx q[0],q[2],q[3]; x q[0]; c=measure q;",
    );
    for wrong in [false, true] {
        let initial = if wrong { "" } else { "cx q[2],q[3];" };
        let right = parse(&format!(
            "qubit[4] q; bit[4] c; {initial} cx q[2],q[1]; ccx q[0],q[1],q[3]; cx q[2],q[1]; c=measure q;"
        ));
        let config = EquivalenceConfig {
            input_pairs: (0..4)
                .map(|i| InputPair {
                    left: Endpoint::Quantum(qubit_at(&left, "q", i)),
                    right: Endpoint::Quantum(qubit_at(&right, "q", i)),
                })
                .collect(),
            output_pairs: (0..4)
                .map(|i| OutputPair {
                    left: Endpoint::Classical(ClassicalBit {
                        register: left.classical_registers[0].id,
                        index: i,
                    }),
                    right: Endpoint::Classical(ClassicalBit {
                        register: right.classical_registers[0].id,
                        index: i,
                    }),
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
            }
        );
        if !wrong {
            assert_eq!(result.evidence, Evidence::DeterministicExact);
        }
    }
}

#[test]
fn sized_static_teleportation_matches_explicit_channel_and_detects_missing_correction() {
    for hops in [1, 3, 10] {
        let source = format!(
            r#"
            const uint[32] n={hops}; qubit input_qubit; qubit[2*n] q;
            def teleport(qubit source, qubit[2] bell) {{
                bit pm; bit bm; reset bell; h bell[0]; cx bell[0],bell[1];
                cx source,bell[0]; h source;
                pm=measure source; bm=measure bell[0];
                if(pm) z bell[1]; if(bm) x bell[1];
            }}
            teleport(input_qubit,q[0:1]);
        "#
        );
        let source = if hops == 1 {
            source
        } else {
            format!("{source} for uint[32] i in [1:n-1] teleport(q[2*i-1],q[2*i:2*i+1]);")
        };
        let right = parse(&format!("qubit input_qubit; qubit[{}] bell;", 2 * hops));
        for missing in [false, true] {
            let left = parse(&if missing {
                source.replace("if(pm) z bell[1];", "")
            } else {
                source.clone()
            });
            let mut config = EquivalenceConfig {
                // Bell registers are deliberately ALSO free inputs. The reset
                // must remove them; no implicit zero-ancilla shortcut is tested.
                input_pairs: vec![InputPair {
                    left: Endpoint::Quantum(qubit(&left, "input_qubit")),
                    right: Endpoint::Quantum(qubit(&right, "input_qubit")),
                }],
                output_pairs: vec![OutputPair {
                    left: Endpoint::Quantum(qubit_at(&left, "q", 2 * hops - 1)),
                    right: Endpoint::Quantum(qubit(&right, "input_qubit")),
                }],
                ..EquivalenceConfig::default()
            };
            config.input_pairs.extend((0..2 * hops).map(|i| InputPair {
                left: Endpoint::Quantum(qubit_at(&left, "q", i)),
                right: Endpoint::Quantum(qubit_at(&right, "bell", i)),
            }));
            let result = analyze(&left, &right, &config).unwrap();
            assert_eq!(
                result.verdict,
                if missing {
                    Verdict::NotEquivalent
                } else {
                    Verdict::Equivalent
                },
                "hops={hops}, missing={missing}"
            );
        }
    }
}

#[test]
fn adaptive_phase_products_export_complete_exact_smt_product_certificates() {
    const N: usize = 12;
    let program = |flipped: bool| {
        let mut source = format!(
            "qubit[{}] q; bit[{N}] c; h q[0]; cp(2*pi) q[0],q[{N}]; h q[0]; c[0]=measure q[0];",
            N + 1
        );
        for i in 1..N {
            let sign = if flipped && i == N - 1 { "" } else { "-" };
            source.push_str(&format!("h q[{i}]; cp(pi/{}) q[{i}],q[{N}]; if(c[0]) {{ p({sign}pi/{}) q[{i}]; }} h q[{i}]; c[{i}]=measure q[{i}];", 1 << i, 1 << (i + 1)));
        }
        parse(&source)
    };
    let left = program(false);
    let right = program(true);
    let mut config = EquivalenceConfig::default();
    for i in 0..=N {
        config.input_pairs.push(InputPair {
            left: Endpoint::Quantum(qubit_at(&left, "q", i)),
            right: Endpoint::Quantum(qubit_at(&right, "q", i)),
        });
    }
    for i in 0..N {
        config.output_pairs.push(OutputPair {
            left: Endpoint::Classical(bit_at(&left, "c", i)),
            right: Endpoint::Classical(bit_at(&right, "c", i)),
        });
    }
    config.output_pairs.push(OutputPair {
        left: Endpoint::Quantum(qubit_at(&left, "q", N)),
        right: Endpoint::Quantum(qubit_at(&right, "q", N)),
    });
    let result = analyze(&left, &right, &config).unwrap();
    assert_eq!(result.verdict, Verdict::NotEquivalent);
    let witness = result.density_counterexample.unwrap();
    assert!(!witness.exact_factors.is_empty());
    assert!(result.solver_queries.iter().any(|q| {
        q.results.iter().any(|r| {
            r.solver == irene::equivalence::Solver::Bitwuzla
                && r.status == irene::equivalence::SolverStatus::Sat
        })
    }));
    let order = witness.root_of_unity_order;
    let expected = |flipped: bool| {
        if witness.classical_outputs[0] != witness.ket_inputs[0]
            || witness.classical_outputs[0] != witness.bra_inputs[0]
            || witness.ket_outputs != [witness.ket_inputs[N]]
            || witness.bra_outputs != [witness.bra_inputs[N]]
        {
            return std::collections::BTreeMap::new();
        }
        let mut product = std::collections::BTreeMap::from([(
            0,
            num_rational::BigRational::from_integer(1.into()),
        )]);
        // Independent gate formula for ALL ket/bra inputs, not just diagonals:
        // <out|H P(t) H|in> = (1 + (-1)^(in xor out) zeta^t)/2.
        for i in 1..N {
            for (input, conjugate) in [(&witness.ket_inputs, false), (&witness.bra_inputs, true)] {
                let controlled = if input[N] { order >> (i + 1) } else { 0 };
                let feedback = if witness.classical_outputs[0] {
                    order >> (i + 2)
                } else {
                    0
                };
                let t = (controlled
                    + if flipped && i == N - 1 {
                        feedback
                    } else {
                        order - feedback
                    })
                    % order;
                let t = if conjugate { (order - t) % order } else { t };
                let coefficient = num_rational::BigRational::new(
                    (if input[i] == witness.classical_outputs[i] {
                        1
                    } else {
                        -1
                    })
                    .into(),
                    2.into(),
                );
                let mut factor = std::collections::BTreeMap::new();
                literal_add_root(
                    &mut factor,
                    0,
                    num_rational::BigRational::new(1.into(), 2.into()),
                    order,
                );
                literal_add_root(&mut factor, t, coefficient, order);
                product = literal_product(&product, &factor, order);
            }
        }
        product
    };
    let mut difference = expected(false);
    for (p, c) in expected(true) {
        literal_add_root(&mut difference, p, -c, order);
    }
    assert!(!difference.is_empty());
    assert_eq!(literal_witness_value(&witness), difference);
}

#[test]
fn wide_unitary_hadamard_tail_has_an_exact_zero_trace_certificate() {
    let left = parse("qubit[40] q; ccx q[0],q[1],q[39]; h q[39];");
    let right = parse("qubit[40] q; ccx q[0],q[1],q[39];");
    let config = EquivalenceConfig {
        input_pairs: (0..40)
            .map(|i| InputPair::quantum(qubit_at(&left, "q", i), qubit_at(&right, "q", i)))
            .collect(),
        output_pairs: (0..40)
            .map(|i| OutputPair {
                left: Endpoint::Quantum(qubit_at(&left, "q", i)),
                right: Endpoint::Quantum(qubit_at(&right, "q", i)),
            })
            .collect(),
        ..EquivalenceConfig::default()
    };
    let result = analyze(&left, &right, &config).unwrap();
    assert_eq!(result.verdict, Verdict::NotEquivalent);
    assert_eq!(
        result.evidence,
        Evidence::UnitaryTraceMismatch {
            normalized_trace_norm_squared: num_rational::BigRational::from_integer(0.into()),
        }
    );
    assert!(result.solver_queries.is_empty());
    assert_eq!(result.kernel_terms, (0, 0));
}

#[test]
fn wide_channel_hadamard_tail_has_a_complete_smt_entry_witness() {
    // An untouched, unpaired, unobserved |0> spectator preserves the exact
    // same 40-input/40-output channel, but deliberately makes the whole
    // declared interface non-unitary-route-admissible. Continue exercising
    // the general SMT entry witness and its independent exact evaluation;
    // the full-unitary fast certificate has a separate test above.
    let left = parse("qubit[40] q; qubit spectator; ccx q[0],q[1],q[39]; h q[39];");
    let right = parse("qubit[40] q; qubit spectator; ccx q[0],q[1],q[39];");
    let mut config = EquivalenceConfig::default();
    for i in 0..40 {
        let a = Endpoint::Quantum(qubit_at(&left, "q", i));
        let b = Endpoint::Quantum(qubit_at(&right, "q", i));
        config.input_pairs.push(InputPair {
            left: a.clone(),
            right: b.clone(),
        });
        config.output_pairs.push(OutputPair { left: a, right: b });
    }
    let result = analyze(&left, &right, &config).unwrap();
    assert_eq!(result.verdict, Verdict::NotEquivalent);
    let witness = result.density_counterexample.unwrap();
    // Independently evaluate the returned matrix entry; SMT need not choose
    // the lexicographically first (all-zero) witness.
    let channel = |hadamard: bool| {
        let transformed = |input: &[bool]| {
            let mut x = input.to_vec();
            x[39] ^= x[0] && x[1];
            x
        };
        let ket = transformed(&witness.ket_inputs);
        let bra = transformed(&witness.bra_inputs);
        if ket[..39] != witness.ket_outputs[..39] || bra[..39] != witness.bra_outputs[..39] {
            return num_rational::BigRational::from_integer(0.into());
        }
        if hadamard {
            let negative =
                (ket[39] && witness.ket_outputs[39]) ^ (bra[39] && witness.bra_outputs[39]);
            num_rational::BigRational::new((if negative { -1 } else { 1 }).into(), 2.into())
        } else {
            num_rational::BigRational::from_integer(
                (if ket == witness.ket_outputs && bra == witness.bra_outputs {
                    1
                } else {
                    0
                })
                .into(),
            )
        }
    };
    let difference = channel(true) - channel(false);
    assert_ne!(
        difference,
        num_rational::BigRational::from_integer(0.into())
    );
    assert_eq!(
        literal_witness_value(&witness),
        std::collections::BTreeMap::from([(0, difference)])
    );
}

#[test]
fn controlled_rotation_modifiers_preserve_relative_phase_on_free_controls() {
    for angle in ["pi/4", "pi", "2*pi"] {
        let left = parse(&format!("qubit[2] q; ctrl @ ry({angle}) q[0],q[1];"));
        let right = parse(&format!(
            "qubit[2] q; ry(({angle})/2) q[1]; cx q[0],q[1]; ry(-({angle})/2) q[1]; cx q[0],q[1];"
        ));
        let mut config = EquivalenceConfig::default();
        for index in 0..2 {
            let a = Endpoint::Quantum(qubit_at(&left, "q", index));
            let b = Endpoint::Quantum(qubit_at(&right, "q", index));
            config.input_pairs.push(InputPair {
                left: a.clone(),
                right: b.clone(),
            });
            config.output_pairs.push(OutputPair { left: a, right: b });
        }
        assert_eq!(
            analyze(&left, &right, &config).unwrap().verdict,
            Verdict::Equivalent
        );
    }
    let left = parse("qubit[2] q; ctrl @ ry(2*pi) q[0],q[1];");
    let right = parse("qubit[2] q;");
    let mut config = EquivalenceConfig::default();
    for index in 0..2 {
        let a = Endpoint::Quantum(qubit_at(&left, "q", index));
        let b = Endpoint::Quantum(qubit_at(&right, "q", index));
        config.input_pairs.push(InputPair {
            left: a.clone(),
            right: b.clone(),
        });
        config.output_pairs.push(OutputPair { left: a, right: b });
    }
    // Ry(2*pi)=-I on the target, so its positive control is Z on the
    // control, not a removable global phase. Both inputs remain free.
    assert_eq!(
        analyze(&left, &right, &config).unwrap().verdict,
        Verdict::NotEquivalent
    );
}

#[test]
fn exact_sixth_turn_rotations_distinguish_environment_reset_without_sampling() {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    let left = openqasm3::parse_str(
        include_str!("../benchmarks/openqasm3-programs/programs/amplitude-damping-reuse/left.qasm"),
        "fresh-environments.qasm",
    )
    .unwrap();
    for (source, equivalent) in [
        (
            include_str!(
                "../benchmarks/openqasm3-programs/programs/amplitude-damping-reuse/right.qasm"
            ),
            true,
        ),
        (
            include_str!(
                "../benchmarks/openqasm3-programs/programs/amplitude-damping-reuse/missing-reset.qasm"
            ),
            false,
        ),
    ] {
        let right = openqasm3::parse_str(source, "reused-environment.qasm").unwrap();
        let a = Endpoint::Quantum(qubit(&left, "system"));
        let b = Endpoint::Quantum(qubit(&right, "system"));
        let config = EquivalenceConfig {
            input_pairs: vec![InputPair {
                left: a.clone(),
                right: b.clone(),
            }],
            output_pairs: vec![OutputPair { left: a, right: b }],
            ..EquivalenceConfig::default()
        };
        let result = analyze(&left, &right, &config).unwrap();
        assert_eq!(
            result.verdict,
            if equivalent {
                Verdict::Equivalent
            } else {
                Verdict::NotEquivalent
            }
        );
        if !equivalent {
            let witness = result.density_counterexample.unwrap();
            assert_eq!(witness.ket_inputs, [true]);
            assert_eq!(witness.bra_inputs, [true]);
            assert_eq!(witness.ket_outputs, witness.bra_outputs);
            assert!(witness.classical_outputs.is_empty());
            // Independent channel calculation: each damping step has jump
            // probability sin(pi/6)^2=1/4. From |1>, fresh environments give
            // final P(1)=9/16. Without reset a first jump re-excites |0> on
            // the second CX, giving P(1)=9/16+1/4=13/16. Thus left-right is
            // -1/4 at output 1 and +1/4 at output 0.
            let difference = BigRational::new(
                BigInt::from(if witness.ket_outputs[0] { -1 } else { 1 }),
                BigInt::from(4),
            );
            assert_eq!(witness.difference_coefficients, vec![(0, difference)]);
        }
    }
}

fn qubit(program: &Program, name: &str) -> Qubit {
    qubit_at(program, name, 0)
}

fn qubit_at(program: &Program, name: &str, index: usize) -> Qubit {
    let register = program
        .quantum_registers
        .iter()
        .find(|register| register.name == name)
        .expect("quantum register");
    Qubit {
        register: register.id,
        index,
    }
}

fn output_config(left: Endpoint, right: Endpoint) -> EquivalenceConfig {
    EquivalenceConfig {
        output_pairs: vec![OutputPair { left, right }],
        ..EquivalenceConfig::default()
    }
}

fn bit(program: &Program, name: &str) -> ClassicalBit {
    bit_at(program, name, 0)
}

fn bit_at(program: &Program, name: &str, index: usize) -> ClassicalBit {
    let register = program
        .classical_registers
        .iter()
        .find(|register| register.name == name)
        .expect("classical register");
    ClassicalBit {
        register: register.id,
        index,
    }
}

fn feedback_config(
    left: &Program,
    right: &Program,
    inputs: &[usize],
    outputs: &[usize],
    generated: bool,
    quantum_outputs: usize,
) -> EquivalenceConfig {
    EquivalenceConfig {
        input_pairs: inputs
            .iter()
            .copied()
            .enumerate()
            .map(|(index, physical)| InputPair {
                left: Endpoint::Quantum(qubit_at(left, "q", physical)),
                right: Endpoint::Quantum(qubit_at(right, "q", index)),
            })
            .collect(),
        output_pairs: outputs
            .iter()
            .copied()
            .enumerate()
            .map(|(index, physical)| OutputPair {
                left: if generated || index < quantum_outputs {
                    Endpoint::Quantum(qubit_at(left, "q", physical))
                } else {
                    Endpoint::Classical(bit_at(left, "c", index - quantum_outputs))
                },
                right: if index < quantum_outputs {
                    Endpoint::Quantum(qubit_at(right, "q", index))
                } else {
                    Endpoint::Classical(bit_at(right, "c", index - quantum_outputs))
                },
            })
            .collect(),
        ..EquivalenceConfig::default()
    }
}

#[test]
fn generated_owm_positive_bit_controls_differ_from_full_register_equality() {
    // Read frozen sources as programs, never their truth labels. SQbricks'
    // source parser retains only the set bits of the compared integer.
    let left = irene::frontend::openqasm2::parse_str(
        include_str!("../benchmarks/sqbricks/generated/programs/owm-vs-qiskit/0051/left.qasm"),
        "generated-positive-controls.qasm",
    )
    .unwrap();
    let original = irene::frontend::openqasm2::parse_str(
        include_str!("../benchmarks/sqbricks/generated/programs/owm-vs-qiskit/0051/right.qasm"),
        "full-register-equality.qasm",
    )
    .unwrap();
    let prefix = "qubit[5] q; bit[3] c; c[2] = false; cx q[0],q[1]; cx q[1],q[2];
        cz q[0],q[3]; cz q[1],q[3]; cz q[0],q[4]; cz q[2],q[4];
        c[0] = measure q[3]; c[1] = measure q[4];";
    let positive_only = parse(&format!(
        "{prefix}
        if (c[0]) z q[2]; if (c[1]) z q[1];
        if (c[0] && c[1]) z q[0];"
    ));
    let exact_equality = parse(&format!(
        "{prefix}
        if (c[0] && !c[1] && !c[2]) z q[2];
        if (!c[0] && c[1] && !c[2]) z q[1];
        if (c[0] && c[1] && !c[2]) z q[0];"
    ));
    let config = |left: &Program, right: &Program, generated: bool| {
        let inputs = if generated {
            [0, 53, 60, 67, 86]
        } else {
            [0, 1, 2, 3, 4]
        };
        let outputs = if generated {
            [52, 59, 66, 85, 118]
        } else {
            [0, 1, 2, 3, 4]
        };
        feedback_config(left, right, &inputs, &outputs, generated, 3)
    };
    assert_eq!(
        analyze(
            &original,
            &exact_equality,
            &config(&original, &exact_equality, false)
        )
        .unwrap()
        .verdict,
        Verdict::Equivalent
    );
    assert_eq!(
        analyze(&left, &positive_only, &config(&left, &positive_only, true))
            .unwrap()
            .verdict,
        Verdict::Equivalent
    );
    assert_eq!(
        analyze(
            &positive_only,
            &original,
            &config(&positive_only, &original, false)
        )
        .unwrap()
        .verdict,
        Verdict::NotEquivalent
    );
}

#[test]
fn generated_owm_bitflip_controls_differ_on_register_value_seven() {
    let left = irene::frontend::openqasm2::parse_str(
        include_str!("../benchmarks/sqbricks/generated/programs/owm-vs-qiskit/0050/left.qasm"),
        "generated-bitflip-controls.qasm",
    )
    .unwrap();
    let original = irene::frontend::openqasm2::parse_str(
        include_str!("../benchmarks/sqbricks/generated/programs/owm-vs-qiskit/0050/right.qasm"),
        "register-equality-bitflip.qasm",
    )
    .unwrap();
    let prefix = "qubit[6] q; bit[3] c;
        cx q[0],q[3]; cx q[1],q[3]; cx q[1],q[4];
        cx q[2],q[4]; cx q[0],q[5]; cx q[2],q[5];
        c[0] = measure q[3]; c[1] = measure q[4]; c[2] = measure q[5];";
    let positive_only = parse(&format!(
        "{prefix}
        if (c[0] && c[2]) x q[0]; if (c[1] && c[2]) x q[1];
        if (c[0] && c[1]) x q[2];"
    ));
    let full_equality = parse(&format!(
        "{prefix}
        if (c[0] && !c[1] && c[2]) x q[0];
        if (!c[0] && c[1] && c[2]) x q[1];
        if (c[0] && c[1] && !c[2]) x q[2];"
    ));
    let identity = [0, 1, 2, 3, 4, 5];
    assert_eq!(
        analyze(
            &original,
            &full_equality,
            &feedback_config(&original, &full_equality, &identity, &identity, false, 3)
        )
        .unwrap()
        .verdict,
        Verdict::Equivalent
    );
    assert_eq!(
        analyze(
            &left,
            &positive_only,
            &feedback_config(
                &left,
                &positive_only,
                &[0, 19, 38, 57, 66, 81],
                &[18, 37, 56, 65, 80, 101],
                true,
                3
            )
        )
        .unwrap()
        .verdict,
        Verdict::Equivalent
    );
    assert_eq!(
        analyze(
            &positive_only,
            &original,
            &feedback_config(&positive_only, &original, &identity, &identity, false, 3)
        )
        .unwrap()
        .verdict,
        Verdict::NotEquivalent
    );
}

#[test]
fn generated_owm_shor_feedback_drops_zero_bit_requirements() {
    let left = irene::frontend::openqasm2::parse_str(
        include_str!("../benchmarks/sqbricks/generated/programs/owm-vs-qiskit/0055/left.qasm"),
        "generated-shor-feedback.qasm",
    )
    .unwrap();
    let source =
        include_str!("../benchmarks/sqbricks/generated/programs/owm-vs-qiskit/0055/right.qasm");
    let original =
        irene::frontend::openqasm2::parse_str(source, "shor-register-equality.qasm").unwrap();
    let mut syntax = source
        .replace("OPENQASM 2.0;", "OPENQASM 3.0;")
        .replace("qelib1.inc", "stdgates.inc")
        .replace("qreg q[7];", "qubit[7] q;")
        // Barriers constrain compilation scheduling, not channel semantics.
        .replace("barrier q[0],q[1],q[2],q[3],q[4],q[5],q[6];", "")
        .replace(
            "creg c[3];",
            "bit[3] c; c[0]=false; c[1]=false; c[2]=false;",
        )
        .replace("u1(", "p(");
    for (q, b) in [(4, 0), (5, 1), (6, 2)] {
        syntax = syntax.replace(
            &format!("measure q[{q}] -> c[{b}];"),
            &format!("c[{b}] = measure q[{q}];"),
        );
    }
    let positive = syntax
        .replace("if(c==1)", "if(c[0])")
        .replace("if(c==2)", "if(c[1])")
        .replace("if(c==3)", "if(c[0] && c[1])");
    let equality = syntax
        .replace("if(c==1)", "if(c[0] && !c[1] && !c[2])")
        .replace("if(c==2)", "if(!c[0] && c[1] && !c[2])")
        .replace("if(c==3)", "if(c[0] && c[1] && !c[2])");
    let positive = openqasm3::parse_str(&positive, "shor-positive.qasm").unwrap();
    let equality = openqasm3::parse_str(&equality, "shor-equality.qasm").unwrap();
    let identity = [0, 1, 2, 3, 4, 5, 6];
    for (a, b, inputs, outputs, generated, expected) in [
        (
            &original,
            &equality,
            identity,
            identity,
            false,
            Verdict::Equivalent,
        ),
        (
            &left,
            &positive,
            [0, 49, 130, 213, 250, 267, 304],
            [48, 129, 212, 249, 266, 303, 392],
            true,
            Verdict::Equivalent,
        ),
        (
            &positive,
            &original,
            identity,
            identity,
            false,
            Verdict::NotEquivalent,
        ),
    ] {
        assert_eq!(
            analyze(
                a,
                b,
                &feedback_config(a, b, &inputs, &outputs, generated, 4)
            )
            .unwrap()
            .verdict,
            expected
        );
    }
}

#[test]
fn frozen_phase_unit_product_matches_semiclassical_outputs() {
    let left = irene::frontend::openqasm2::parse_str(
        include_str!("../benchmarks/sqbricks/generated/programs/owm-vs-qiskit/0005/left.qasm"),
        "owm-phase-unit.qasm",
    )
    .unwrap();
    let right = irene::frontend::openqasm2::parse_str(
        include_str!("../benchmarks/sqbricks/generated/programs/owm-vs-qiskit/0005/right.qasm"),
        "semiclassical-phase-unit.qasm",
    )
    .unwrap();
    // Actual frozen interface, including ALL seven free inputs. No label or
    // assumed zero auxiliary input is read into the verifier.
    let config = EquivalenceConfig {
        input_pairs: [0, 15, 36, 63, 96, 135, 180]
            .into_iter()
            .enumerate()
            .map(|(index, physical)| {
                InputPair::quantum(qubit_at(&left, "q", physical), qubit_at(&right, "q", index))
            })
            .collect(),
        output_pairs: [14, 35, 62, 95, 134, 179, 228]
            .into_iter()
            .enumerate()
            .map(|(index, physical)| OutputPair {
                left: Endpoint::Quantum(qubit_at(&left, "q", physical)),
                right: if index == 6 {
                    Endpoint::Quantum(qubit_at(&right, "q", index))
                } else {
                    Endpoint::Classical(bit(&right, &format!("c{index}")))
                },
            })
            .collect(),
        ..EquivalenceConfig::default()
    };
    let result = analyze(&left, &right, &config).unwrap();
    assert_eq!(result.verdict, Verdict::Equivalent);
    // XAG storage need not have the same syntax after two different rewrite
    // histories; either complete exact certificate proves the same verdict.
    assert!(matches!(
        result.evidence,
        Evidence::ExactHps | Evidence::DensityKernelExact
    ));
}

#[test]
fn frozen_teleportation_phase_product_has_an_exact_density_certificate() {
    check_teleportation_phase_product(
        include_str!("../benchmarks/sqbricks/generated/programs/owm-vs-tele/0220/left.qasm"),
        include_str!("../benchmarks/sqbricks/generated/programs/owm-vs-tele/0220/right.qasm"),
        &[0, 15, 36, 63, 96, 135, 180],
        &[14, 35, 62, 95, 134, 179, 228],
    );
}

#[test]
fn frozen_teleportation_conditional_orientation_has_an_exact_certificate() {
    check_teleportation_phase_product(
        include_str!("../benchmarks/sqbricks/generated/programs/owm-vs-tele/0217/left.qasm"),
        include_str!("../benchmarks/sqbricks/generated/programs/owm-vs-tele/0217/right.qasm"),
        &[0, 9, 24, 45],
        &[8, 23, 44, 69],
    );
}

fn check_teleportation_phase_product(
    left_source: &str,
    right_source: &str,
    inputs: &[usize],
    outputs: &[usize],
) {
    let left =
        irene::frontend::openqasm2::parse_str(left_source, "owm-phase-product.qasm").unwrap();
    let right =
        irene::frontend::openqasm2::parse_str(right_source, "tele-phase-product.qasm").unwrap();
    // Explicit interface from the frozen fixture; no truth label is read.
    let config = EquivalenceConfig {
        input_pairs: inputs
            .iter()
            .copied()
            .enumerate()
            .map(|(index, physical)| InputPair {
                left: Endpoint::Quantum(qubit_at(&left, "q", physical)),
                right: Endpoint::Quantum(qubit_at(&right, "q", 3 * index)),
            })
            .collect(),
        output_pairs: outputs
            .iter()
            .copied()
            .enumerate()
            .map(|(index, physical)| OutputPair {
                left: Endpoint::Quantum(qubit_at(&left, "q", physical)),
                right: Endpoint::Quantum(qubit_at(&right, "q", 3 * index + 2)),
            })
            .collect(),
        ..EquivalenceConfig::default()
    };
    let result = analyze(&left, &right, &config).unwrap();
    assert_eq!(result.verdict, Verdict::Equivalent);
    assert!(matches!(
        result.evidence,
        Evidence::ExactHps | Evidence::DensityKernelExact
    ));
}

#[test]
fn frozen_grover_witness_matches_independent_integer_state_evolution() {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    // Independent simulator for this H/X/CCX fixture only: all amplitudes
    // have the common scale (sqrt(2))^-h, so signed integers suffice. This
    // does not call Irene's parser, optimizer or path-sum arithmetic.
    fn amplitude(source: &str, input: usize, output: usize) -> (BigInt, usize) {
        let mut amplitudes = vec![0i64; 1 << 9];
        amplitudes[input] = 1;
        let mut hadamards = 0usize;
        for line in source.lines().map(str::trim) {
            if line.is_empty()
                || line == "OPENQASM 2.0;"
                || line == "include \"qelib1.inc\";"
                || line == "qreg q[9];"
            {
                continue;
            }
            let (gate, operands) = line.split_once(' ').unwrap();
            let qubits = operands
                .trim_end_matches(';')
                .split(',')
                .map(|q| {
                    q.trim()
                        .strip_prefix("q[")
                        .unwrap()
                        .strip_suffix(']')
                        .unwrap()
                        .parse::<usize>()
                        .unwrap()
                })
                .collect::<Vec<_>>();
            assert!(qubits.iter().all(|&q| q < 9));
            assert_eq!(qubits.len(), if gate == "ccx" { 3 } else { 1 });
            let target = 1 << qubits[qubits.len() - 1];
            match gate {
                "h" => {
                    hadamards += 1;
                    for basis in 0..amplitudes.len() {
                        if basis & target == 0 {
                            let a = amplitudes[basis];
                            let b = amplitudes[basis | target];
                            amplitudes[basis] = a.checked_add(b).unwrap();
                            amplitudes[basis | target] = a.checked_sub(b).unwrap();
                        }
                    }
                }
                "x" | "ccx" => {
                    for basis in 0..amplitudes.len() {
                        if basis & target == 0
                            && qubits[..qubits.len() - 1]
                                .iter()
                                .all(|q| basis & (1 << q) != 0)
                        {
                            amplitudes.swap(basis, basis | target);
                        }
                    }
                }
                _ => panic!("unsupported independent-check gate: {gate}"),
            }
        }
        (BigInt::from(amplitudes[output]), hadamards)
    }

    let left_source =
        include_str!("../benchmarks/sqbricks/programs/buggy/grover_9_veriqbench_FALSE_gate.qasm");
    let right_source = include_str!(
        "../benchmarks/sqbricks/programs/VeriQbench/combinational/grover/grover_9.qasm"
    );
    let channel = |source: &str, ket: usize, bra: usize, out: usize, out_bra: usize| {
        let (a, h) = amplitude(source, ket, out);
        let (b, hb) = amplitude(source, bra, out_bra);
        assert_eq!(h, hb);
        BigRational::new(a * b, BigInt::from(1) << h)
    };
    let left_probability = channel(left_source, 0, 0, 0, 0);
    let right_probability = channel(right_source, 0, 0, 0, 0);
    assert_eq!(left_probability, BigRational::new(1.into(), 1024.into()));
    assert_eq!(right_probability, BigRational::new(1.into(), 32.into()));
    // This test exercises the independent density-entry witness, not a
    // full-unitary trace certificate. An untouched, unobserved initialized
    // spectator preserves the entire original nine-qubit channel while
    // making this explicitly a partial interface of the extended program.
    // The frozen fixture files and independent integer simulator stay intact.
    let left = irene::frontend::openqasm2::parse_str(
        &format!("{left_source}\nqreg trace_test_spectator[1];"),
        "grover-bug.qasm",
    )
    .unwrap();
    let right = irene::frontend::openqasm2::parse_str(
        &format!("{right_source}\nqreg trace_test_spectator[1];"),
        "grover-original.qasm",
    )
    .unwrap();
    let endpoints = |i| {
        (
            Endpoint::Quantum(qubit_at(&left, "q", i)),
            Endpoint::Quantum(qubit_at(&right, "q", i)),
        )
    };
    let config = EquivalenceConfig {
        input_pairs: (0..9)
            .map(|i| {
                let (left, right) = endpoints(i);
                InputPair { left, right }
            })
            .collect(),
        output_pairs: (0..9)
            .map(|i| {
                let (left, right) = endpoints(i);
                OutputPair { left, right }
            })
            .collect(),
        ..EquivalenceConfig::default()
    };
    let result = analyze(&left, &right, &config).unwrap();
    assert_eq!(result.verdict, Verdict::NotEquivalent);
    let witness = result.density_counterexample.unwrap();
    assert!(witness.classical_outputs.is_empty());
    let index = |bits: &[bool]| {
        bits.iter()
            .enumerate()
            .fold(0usize, |n, (i, b)| n | ((usize::from(*b)) << i))
    };
    let coordinates = [
        index(&witness.ket_inputs),
        index(&witness.bra_inputs),
        index(&witness.ket_outputs),
        index(&witness.bra_outputs),
    ];
    let difference = channel(
        left_source,
        coordinates[0],
        coordinates[1],
        coordinates[2],
        coordinates[3],
    ) - channel(
        right_source,
        coordinates[0],
        coordinates[1],
        coordinates[2],
        coordinates[3],
    );
    assert_ne!(difference, BigRational::from_integer(0.into()));
    assert_eq!(
        literal_witness_value(&witness),
        std::collections::BTreeMap::from([(0, difference)])
    );
}

#[test]
fn exact_density_entry_witness_detects_off_diagonal_t_phase() {
    let left = parse("qubit q; h q; t q;");
    let right = parse("qubit q; h q;");
    let result = analyze(
        &left,
        &right,
        &output_config(
            Endpoint::Quantum(qubit(&left, "q")),
            Endpoint::Quantum(qubit(&right, "q")),
        ),
    )
    .unwrap();
    assert_eq!(result.verdict, Verdict::NotEquivalent);
    assert_eq!(result.evidence, Evidence::DensityEntryCounterexample);
    let witness = result.density_counterexample.unwrap();
    assert!(witness.ket_inputs.is_empty() && witness.bra_inputs.is_empty());
    assert_ne!(witness.ket_outputs, witness.bra_outputs);
    let mut expected = std::collections::BTreeMap::new();
    let order = witness.root_of_unity_order;
    literal_add_root(
        &mut expected,
        0,
        num_rational::BigRational::new((-1).into(), 2.into()),
        order,
    );
    let p = if witness.ket_outputs[0] {
        order / 8
    } else {
        7 * order / 8
    };
    literal_add_root(
        &mut expected,
        p,
        num_rational::BigRational::new(1.into(), 2.into()),
        order,
    );
    assert_eq!(literal_witness_value(&witness), expected);
}

#[test]
fn exact_density_entry_witness_evaluates_rotation_scalars_without_floats() {
    let left = parse("qubit q; rx(pi/4) q;");
    let right = parse("qubit q; rx(-pi/4) q;");
    let result = analyze(
        &left,
        &right,
        &output_config(
            Endpoint::Quantum(qubit(&left, "q")),
            Endpoint::Quantum(qubit(&right, "q")),
        ),
    )
    .unwrap();
    assert_eq!(result.verdict, Verdict::NotEquivalent);
    assert_eq!(result.evidence, Evidence::DensityEntryCounterexample);
    let witness = result.density_counterexample.unwrap();
    assert_ne!(witness.ket_outputs, witness.bra_outputs);
    assert!(!witness.difference_coefficients.is_empty());
}

#[test]
fn cyclotomic_leaf_equality_matches_hth_with_rx_up_to_global_phase() {
    let left = parse("qubit q; h q; t q; h q;");
    let right = parse("qubit q; rx(pi/4) q;");
    let result = analyze(
        &left,
        &right,
        &output_config(
            Endpoint::Quantum(qubit(&left, "q")),
            Endpoint::Quantum(qubit(&right, "q")),
        ),
    )
    .unwrap();
    assert_eq!(result.verdict, Verdict::Equivalent);
    assert_eq!(result.evidence, Evidence::DensityKernelExact);
    assert!(result.density_counterexample.is_none());
}

#[test]
fn sparse_cyclotomic_witness_detects_tiny_phase_without_approximation() {
    let right = parse("qubit q; h q;");
    for (denominator, power) in [(1u64 << 42, 1u64 << 19), (1u64 << 61, 1u64)] {
        let left = parse(&format!("qubit q; h q; p(pi/{denominator}) q;"));
        let result = analyze(
            &left,
            &right,
            &output_config(
                Endpoint::Quantum(qubit(&left, "q")),
                Endpoint::Quantum(qubit(&right, "q")),
            ),
        )
        .unwrap();
        assert_eq!(result.verdict, Verdict::NotEquivalent);
        assert_eq!(result.evidence, Evidence::DensityEntryCounterexample);
        let witness = result.density_counterexample.unwrap();
        assert_eq!(witness.root_of_unity_order, 1 << 62);
        assert_ne!(witness.ket_outputs, witness.bra_outputs);
        let order = witness.root_of_unity_order;
        let mut expected = std::collections::BTreeMap::new();
        literal_add_root(
            &mut expected,
            0,
            num_rational::BigRational::new((-1).into(), 2.into()),
            order,
        );
        literal_add_root(
            &mut expected,
            if witness.ket_outputs[0] {
                power
            } else {
                order - power
            },
            num_rational::BigRational::new(1.into(), 2.into()),
            order,
        );
        assert_eq!(literal_witness_value(&witness), expected);
    }
    let unsupported = parse("qubit q; h q; p(pi/4611686018427387904) q;");
    let result = analyze(
        &unsupported,
        &right,
        &output_config(
            Endpoint::Quantum(qubit(&unsupported, "q")),
            Endpoint::Quantum(qubit(&right, "q")),
        ),
    )
    .unwrap();
    assert_eq!(result.verdict, Verdict::Unknown);
    assert!(result.density_counterexample.is_none());
}

#[test]
fn visible_measurements_remove_duplicate_history_constraints() {
    let left = parse(
        "qubit[2] q; bit[2] c; h q[0]; h q[1]; \
         c[0] = measure q[0]; c[1] = measure q[1];",
    );
    let right = parse(
        "qubit[2] q; bit[2] scratch; bit[2] out; h q[0]; h q[1]; \
         scratch[0] = measure q[0]; scratch[1] = measure q[1]; \
         out[0] = scratch[1]; out[1] = scratch[0];",
    );
    let config = EquivalenceConfig {
        output_pairs: (0..2)
            .map(|index| OutputPair {
                left: Endpoint::Classical(bit_at(&left, "c", index)),
                right: Endpoint::Classical(bit_at(&right, "out", index)),
            })
            .collect(),
        ..EquivalenceConfig::default()
    };

    let result = analyze(&left, &right, &config).unwrap();

    assert_eq!(result.verdict, Verdict::Equivalent);
}

fn config(
    left_input: Qubit,
    right_input: Qubit,
    left_output: Endpoint,
    right_output: Endpoint,
) -> EquivalenceConfig {
    EquivalenceConfig {
        input_pairs: vec![InputPair::quantum(left_input, right_input)],
        output_pairs: vec![OutputPair {
            left: left_output,
            right: right_output,
        }],
        ..EquivalenceConfig::default()
    }
}

#[test]
fn undefined_numeric_gate_domain_cannot_be_hidden_by_zero_phase() {
    let right = parse("qubit q;");
    let right_q = qubit(&right, "q");
    let lefts = [
        parse("qubit q; p(0.0 * (1.0 / (0.0 + 0.0))) q;"),
        parse("qubit q; qubit dead; p(1.0 / (0.0 + 0.0)) dead;"),
        parse("qubit q; if (false) { p(1.0 / (0.0 + 0.0)) q; }"),
        parse("qubit q; p(1.0 / (pi-pi)) q;"),
    ];
    for left in lefts {
        let left_q = qubit(&left, "q");
        let result = analyze(
            &left,
            &right,
            &config(
                left_q.clone(),
                right_q.clone(),
                Endpoint::Quantum(left_q),
                Endpoint::Quantum(right_q.clone()),
            ),
        );
        assert!(
            result.is_err(),
            "undefined source parameter was accepted: {result:?}"
        );
    }
    // QASM2 already rejects this rational-zero divisor in its frontend.
    assert!(
        irene::frontend::openqasm2::parse_str(
            "OPENQASM 2.0; include \"qelib1.inc\"; qreg q[1]; u1(0 * (1 / (0+0))) q[0];",
            "qasm2-domain.qasm",
        )
        .is_err()
    );
}

#[test]
fn openqasm3_integer_division_must_not_create_a_false_phase_equivalence() {
    // Integer 1/2 is zero before multiplication by pi or promotion to the
    // gate parameter's type. Treating it as a rational would falsely prove S.
    let left = parse("qubit q; p((1 / 2) * pi) q;");
    let right = parse("qubit q; s q;");
    let left_q = qubit(&left, "q");
    let right_q = qubit(&right, "q");
    let result = analyze(
        &left,
        &right,
        &config(
            left_q.clone(),
            right_q.clone(),
            Endpoint::Quantum(left_q),
            Endpoint::Quantum(right_q),
        ),
    )
    .unwrap();
    assert_eq!(result.verdict, Verdict::NotEquivalent);
}

#[test]
fn integer_division_fix_preserves_float_parameters_and_openqasm2_real_parameters() {
    let right = parse("qubit q; s q;");
    let lefts = [
        parse("qubit q; p((1.0 / 2) * pi) q;"),
        irene::frontend::openqasm2::parse_str(
            "OPENQASM 2.0; include \"qelib1.inc\"; qreg q[1]; u1((1 / 2) * pi) q[0];",
            "qasm2-real-parameter.qasm",
        )
        .unwrap(),
    ];
    for left in lefts {
        let left_q = qubit(&left, "q");
        let right_q = qubit(&right, "q");
        let result = analyze(
            &left,
            &right,
            &config(
                left_q.clone(),
                right_q.clone(),
                Endpoint::Quantum(left_q),
                Endpoint::Quantum(right_q),
            ),
        )
        .unwrap();
        assert_eq!(result.verdict, Verdict::Equivalent);
    }
}

#[test]
fn explicit_pairs_ignore_local_register_names() {
    let left = parse("qubit a;");
    let right = parse("bit scratch = false; qubit b;");
    let left_q = qubit(&left, "a");
    let right_q = qubit(&right, "b");
    let result = analyze(
        &left,
        &right,
        &config(
            left_q.clone(),
            right_q.clone(),
            Endpoint::Quantum(left_q),
            Endpoint::Quantum(right_q),
        ),
    )
    .unwrap();

    assert_eq!(result.verdict, Verdict::Equivalent);
}

#[test]
fn nonlinear_reversible_output_map_has_a_checked_phase_counterexample() {
    let root =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("benchmarks/sqbricks/programs");
    let load = |relative: &str| {
        irene::frontend::openqasm2::parse_str(
            &std::fs::read_to_string(root.join(relative)).unwrap(),
            relative,
        )
        .unwrap()
    };
    let left = load("buggy/gf2^32_mult_veriqbench_FALSE_angle.qasm");
    let right = load("VeriQbench/combinational/rev_circuit/gf2^32mult_1117_5213.qasm");
    let config = EquivalenceConfig {
        input_pairs: (0..96)
            .map(|i| InputPair::quantum(qubit_at(&left, "q", i), qubit_at(&right, "q", i)))
            .collect(),
        output_pairs: (0..96)
            .map(|i| OutputPair {
                left: Endpoint::Quantum(qubit_at(&left, "q", i)),
                right: Endpoint::Quantum(qubit_at(&right, "q", i)),
            })
            .collect(),
        ..EquivalenceConfig::default()
    };
    let analysis = analyze(&left, &right, &config).unwrap();
    assert_eq!(analysis.verdict, Verdict::NotEquivalent);
    assert_eq!(analysis.evidence, Evidence::PhaseCounterexample);
    assert!(analysis.counterexample.unwrap().bra_inputs.is_some());
    // Algebraic input recovery discharged injectivity; the sole SMT query
    // finds phase variation, whose model the verifier checks exactly.
    assert_eq!(analysis.solver_queries.len(), 1);
}

#[test]
fn density_kernel_matches_nonlinear_owm_and_teleportation_selectors() {
    // This real circuit pair produces {f, f XOR g} on the OWM side and
    // {f, g} on the teleportation side, with cubic output relations. Both
    // programs go through the actual parser, interface and exact semantics.
    check_owm_selector("0002", &[0, 5, 22, 27, 88], &[4, 21, 26, 87, 132]);
}

#[test]
fn density_kernel_uses_affine_equalities_inside_nonlinear_selectors() {
    check_owm_selector(
        "0003",
        &[0, 5, 22, 31, 36, 113, 214],
        &[4, 21, 30, 35, 112, 213, 256],
    );
}

#[test]
fn density_kernel_uses_nonlinear_triangular_selector_definitions() {
    check_owm_selector(
        "0006",
        &[
            0, 7, 10, 23, 50, 55, 58, 99, 146, 173, 200, 203, 244, 301, 328,
        ],
        &[
            6, 9, 22, 49, 54, 57, 98, 145, 172, 199, 202, 243, 300, 327, 374,
        ],
    );
}

#[test]
fn density_kernel_aggregates_bounded_sums_across_classical_selector_partitions() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("benchmarks/sqbricks/generated/programs/owm-vs-qiskit/0001");
    let load = |name: &str| {
        irene::frontend::openqasm2::parse_str(
            &std::fs::read_to_string(root.join(name)).unwrap(),
            name,
        )
        .unwrap()
    };
    let left = load("left.qasm");
    let right = load("right.qasm");
    let config = EquivalenceConfig {
        input_pairs: [0, 7, 20]
            .into_iter()
            .enumerate()
            .map(|(i, index)| {
                InputPair::quantum(qubit_at(&left, "q", index), qubit_at(&right, "q", i))
            })
            .collect(),
        output_pairs: vec![
            OutputPair {
                left: Endpoint::Quantum(qubit_at(&left, "q", 6)),
                right: Endpoint::Classical(bit_at(&right, "c0", 0)),
            },
            OutputPair {
                left: Endpoint::Quantum(qubit_at(&left, "q", 19)),
                right: Endpoint::Classical(bit_at(&right, "c1", 0)),
            },
            OutputPair {
                left: Endpoint::Quantum(qubit_at(&left, "q", 36)),
                right: Endpoint::Quantum(qubit_at(&right, "q", 2)),
            },
        ],
        ..EquivalenceConfig::default()
    };
    let result = analyze(&left, &right, &config).unwrap();
    assert_eq!(result.verdict, Verdict::Equivalent);
    assert!(matches!(
        result.evidence,
        Evidence::ExactHps | Evidence::DensityKernelExact
    ));
}

fn check_owm_selector(case: &str, inputs: &[usize], outputs: &[usize]) {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("benchmarks/sqbricks/generated/programs/owm-vs-tele")
        .join(case);
    let load = |name: &str| {
        let source = std::fs::read_to_string(root.join(name)).unwrap();
        irene::frontend::openqasm2::parse_str(&source, name).unwrap()
    };
    let left = load("left.qasm");
    let right = load("right.qasm");
    let config = EquivalenceConfig {
        input_pairs: inputs
            .iter()
            .copied()
            .enumerate()
            .map(|(i, index)| {
                InputPair::quantum(qubit_at(&left, "q", index), qubit_at(&right, "q", 3 * i))
            })
            .collect(),
        output_pairs: outputs
            .iter()
            .copied()
            .enumerate()
            .map(|(i, index)| OutputPair {
                left: Endpoint::Quantum(qubit_at(&left, "q", index)),
                right: Endpoint::Quantum(qubit_at(&right, "q", 3 * i + 2)),
            })
            .collect(),
        ..EquivalenceConfig::default()
    };
    let result = analyze(&left, &right, &config).unwrap();
    assert_eq!(result.verdict, Verdict::Equivalent);
    // XAG outputs may have distinct syntax. A deterministic graph-miter
    // certificate is as valid as the structural HPS or kernel certificate.
    assert!(matches!(
        result.evidence,
        Evidence::ExactHps | Evidence::DensityKernelExact | Evidence::DeterministicExact
    ));
}

#[test]
fn different_basis_outputs_are_not_equivalent() {
    let left = parse("qubit q;");
    let right = parse("qubit q; x q;");
    let left_q = qubit(&left, "q");
    let right_q = qubit(&right, "q");
    let result = analyze(
        &left,
        &right,
        &config(
            left_q.clone(),
            right_q.clone(),
            Endpoint::Quantum(left_q),
            Endpoint::Quantum(right_q),
        ),
    )
    .unwrap();

    assert_eq!(result.verdict, Verdict::NotEquivalent);
}

#[test]
fn different_injective_output_supports_are_not_equivalent() {
    let left = parse("qubit q; h q;");
    let right = parse("qubit q;");
    let left_q = qubit(&left, "q");
    let right_q = qubit(&right, "q");
    let result = analyze(
        &left,
        &right,
        &config(
            left_q.clone(),
            right_q.clone(),
            Endpoint::Quantum(left_q),
            Endpoint::Quantum(right_q),
        ),
    )
    .unwrap();

    assert_eq!(result.verdict, Verdict::NotEquivalent);
}

#[test]
fn different_affine_output_subspaces_are_not_equivalent() {
    let left = parse("qubit[2] q; h q[0];");
    let right = parse("qubit[2] q; h q[1];");
    let config = EquivalenceConfig {
        input_pairs: (0..2)
            .map(|index| {
                InputPair::quantum(qubit_at(&left, "q", index), qubit_at(&right, "q", index))
            })
            .collect(),
        output_pairs: (0..2)
            .map(|index| OutputPair {
                left: Endpoint::Quantum(qubit_at(&left, "q", index)),
                right: Endpoint::Quantum(qubit_at(&right, "q", index)),
            })
            .collect(),
        ..EquivalenceConfig::default()
    };

    let result = analyze(&left, &right, &config).unwrap();

    assert_eq!(result.verdict, Verdict::NotEquivalent);
}

#[test]
fn hidden_history_makes_visible_support_exact() {
    let left = parse("qubit[2] q; bit c; h q[0]; h q[1]; c = measure q[1];");
    let right = parse("qubit[2] q; bit c; h q[1]; c = measure q[1];");
    let config = EquivalenceConfig {
        input_pairs: (0..2)
            .map(|index| {
                InputPair::quantum(qubit_at(&left, "q", index), qubit_at(&right, "q", index))
            })
            .collect(),
        output_pairs: vec![OutputPair {
            left: Endpoint::Quantum(qubit_at(&left, "q", 0)),
            right: Endpoint::Quantum(qubit_at(&right, "q", 0)),
        }],
        ..EquivalenceConfig::default()
    };

    let result = analyze(&left, &right, &config).unwrap();

    assert_eq!(result.verdict, Verdict::NotEquivalent);
}

#[test]
fn predicated_branch_is_not_erased_by_join_discard() {
    let left = parse("qubit[2] q; bit c; h q[0]; c = measure q[0]; if (c) { x q[1]; }");
    let right = parse("qubit q;");
    let result = analyze(
        &left,
        &right,
        &output_config(
            Endpoint::Quantum(qubit_at(&left, "q", 1)),
            Endpoint::Quantum(qubit(&right, "q")),
        ),
    )
    .unwrap();

    assert_ne!(result.verdict, Verdict::Equivalent);
}

#[test]
fn input_dependent_phase_changes_the_quantum_channel() {
    let left = parse("qubit q;");
    let right = parse("qubit q; z q;");
    let left_q = qubit(&left, "q");
    let right_q = qubit(&right, "q");
    let result = analyze(
        &left,
        &right,
        &config(
            left_q.clone(),
            right_q.clone(),
            Endpoint::Quantum(left_q),
            Endpoint::Quantum(right_q),
        ),
    )
    .unwrap();

    assert_eq!(result.verdict, Verdict::NotEquivalent);
}

#[test]
fn z_phase_disappears_under_terminal_z_observation() {
    let left = parse("qubit q;");
    let right = parse("qubit q; bit c; z q; c = measure q;");
    let left_q = qubit(&left, "q");
    let right_q = qubit(&right, "q");
    let right_c = bit(&right, "c");
    let result = analyze(
        &left,
        &right,
        &config(
            left_q.clone(),
            right_q,
            Endpoint::Quantum(left_q),
            Endpoint::Classical(right_c),
        ),
    )
    .unwrap();

    assert_eq!(result.verdict, Verdict::Equivalent);
}

#[test]
fn measured_superposition_matches_terminal_z_observation() {
    let left = parse("qubit q; h q;");
    let right = parse("qubit q; bit c; h q; c = measure q;");
    let left_q = qubit(&left, "q");
    let right_q = qubit(&right, "q");
    let right_c = bit(&right, "c");
    let result = analyze(
        &left,
        &right,
        &config(
            left_q.clone(),
            right_q,
            Endpoint::Quantum(left_q),
            Endpoint::Classical(right_c),
        ),
    )
    .unwrap();

    assert_eq!(result.verdict, Verdict::Equivalent);
}

#[test]
fn measurement_is_not_erased_when_the_quantum_output_is_retained() {
    let left = parse("qubit q; h q;");
    let right = parse("qubit q; bit c; h q; c = measure q;");
    let left_q = qubit(&left, "q");
    let right_q = qubit(&right, "q");
    let result = analyze(
        &left,
        &right,
        &output_config(Endpoint::Quantum(left_q), Endpoint::Quantum(right_q)),
    )
    .unwrap();

    assert_ne!(result.verdict, Verdict::Equivalent);
}

#[test]
fn reset_discards_phase_history_and_restores_zero() {
    let left = parse("qubit q; h q; reset q;");
    let right = parse("qubit q;");
    let left_q = qubit(&left, "q");
    let right_q = qubit(&right, "q");
    let result = analyze(
        &left,
        &right,
        &output_config(Endpoint::Quantum(left_q), Endpoint::Quantum(right_q)),
    )
    .unwrap();

    assert_eq!(result.verdict, Verdict::Equivalent);
}

#[test]
fn bell_partial_trace_matches_a_measured_superposition() {
    let left = parse("qubit[2] q; h q[0]; cx q[0], q[1]; reset q[0];");
    let right = parse("qubit q; bit c; h q; c = measure q;");
    let left_output = qubit_at(&left, "q", 1);
    let right_output = qubit(&right, "q");
    let result = analyze(
        &left,
        &right,
        &output_config(
            Endpoint::Quantum(left_output),
            Endpoint::Quantum(right_output),
        ),
    )
    .unwrap();

    assert_eq!(result.verdict, Verdict::Equivalent);
}

#[test]
fn constant_global_phase_is_ignored() {
    let left = parse("qubit q;");
    let right = parse("qubit q; x q; z q; x q; z q;");
    let left_q = qubit(&left, "q");
    let right_q = qubit(&right, "q");
    let result = analyze(
        &left,
        &right,
        &config(
            left_q.clone(),
            right_q.clone(),
            Endpoint::Quantum(left_q),
            Endpoint::Quantum(right_q),
        ),
    )
    .unwrap();

    assert_eq!(result.verdict, Verdict::Equivalent);
}

#[test]
fn constant_global_phase_is_ignored_with_live_paths() {
    let left = parse("qubit q; h q;");
    let right = parse("qubit q; x q; z q; x q; z q; h q;");
    let left_q = qubit(&left, "q");
    let right_q = qubit(&right, "q");
    let result = analyze(
        &left,
        &right,
        &config(
            left_q.clone(),
            right_q.clone(),
            Endpoint::Quantum(left_q),
            Endpoint::Quantum(right_q),
        ),
    )
    .unwrap();

    assert_eq!(result.verdict, Verdict::Equivalent);
}

#[test]
fn local_fourier_elimination_proves_hadamard_cancellation() {
    let left = parse("qubit q; h q; h q;");
    let right = parse("qubit q;");
    let left_q = qubit(&left, "q");
    let right_q = qubit(&right, "q");
    let result = analyze(
        &left,
        &right,
        &config(
            left_q.clone(),
            right_q.clone(),
            Endpoint::Quantum(left_q),
            Endpoint::Quantum(right_q),
        ),
    )
    .unwrap();

    assert_eq!(result.verdict, Verdict::Equivalent);
}

#[test]
fn independent_measurement_order_does_not_change_the_terminal_state() {
    let left = parse("qubit a; qubit b; bit ca; bit cb; h a; h b; ca = measure a; cb = measure b;");
    let right =
        parse("qubit a; qubit b; bit ca; bit cb; h a; h b; cb = measure b; ca = measure a;");
    let result = analyze(
        &left,
        &right,
        &EquivalenceConfig {
            output_pairs: vec![
                OutputPair {
                    left: Endpoint::Classical(bit(&left, "ca")),
                    right: Endpoint::Classical(bit(&right, "ca")),
                },
                OutputPair {
                    left: Endpoint::Classical(bit(&left, "cb")),
                    right: Endpoint::Classical(bit(&right, "cb")),
                },
            ],
            ..EquivalenceConfig::default()
        },
    )
    .unwrap();

    assert_eq!(result.verdict, Verdict::Equivalent);
}

#[test]
fn hidden_measurement_phase_survives_orthogonal_world_merging() {
    let left = parse("qubit q;");
    let right = parse(
        "qubit[3] q; bit m0; bit m1; h q[1]; cx q[1], q[2]; \
         cx q[0], q[1]; h q[0]; m0 = measure q[0]; m1 = measure q[1]; \
         if (m1) x q[2];",
    );
    let left_q = qubit(&left, "q");
    let right_input = qubit_at(&right, "q", 0);
    let right_output = qubit_at(&right, "q", 2);
    let result = analyze(
        &left,
        &right,
        &config(
            left_q.clone(),
            right_input,
            Endpoint::Quantum(left_q),
            Endpoint::Quantum(right_output),
        ),
    )
    .unwrap();

    assert_ne!(result.verdict, Verdict::Equivalent);
}

#[test]
fn branch_local_measurement_targets_and_overwrites_keep_full_history_mixture() {
    // Four distinct measurement histories, each probability 1/4. Clearing
    // current storage cannot turn the two output values into coherent rays.
    let nested = parse(
        "qubit a; qubit b; qubit r; bit m; bit mt; bit mu; \
         h a; m=measure a; \
         if(m) { h b; mt=measure b; if(mt) { x r; } reset b; } \
         else { h b; mu=measure b; if(mu) { x r; } reset b; } \
         m=false; mt=false; mu=false;",
    );
    let reference =
        parse("qubit b; qubit r; bit mt; h b; mt=measure b; if(mt) { x r; } reset b; mt=false;");
    let config = EquivalenceConfig {
        // r stays a FREE input in the entire exact bit-flip-mixture channel.
        input_pairs: vec![InputPair {
            left: Endpoint::Quantum(qubit(&nested, "r")),
            right: Endpoint::Quantum(qubit(&reference, "r")),
        }],
        output_pairs: vec![OutputPair {
            left: Endpoint::Quantum(qubit(&nested, "r")),
            right: Endpoint::Quantum(qubit(&reference, "r")),
        }],
        ..EquivalenceConfig::default()
    };
    assert_eq!(
        analyze(&nested, &reference, &config).unwrap().verdict,
        Verdict::Equivalent
    );
    let pure = parse("qubit r; h r;");
    let mut negative = config;
    negative.input_pairs[0].right = Endpoint::Quantum(qubit(&pure, "r"));
    negative.output_pairs[0].right = Endpoint::Quantum(qubit(&pure, "r"));
    // At free input0 the complete mixture has off-diagonal0, versus1/2
    // for H|0>. No source label or structural circuit difference certifies it.
    assert_eq!(
        analyze(&nested, &pure, &negative).unwrap().verdict,
        Verdict::NotEquivalent
    );
}

#[test]
fn nested_branch_compaction_preserves_the_hidden_measurement_mixture() {
    // The inner reset joins execute on only one branch of the outer `m0`
    // split. Compaction there must not discard the outer history or density
    // merge that branch as though it were the complete component set.
    let nested = parse(
        "qubit a; qubit b; qubit r; bit m0; bit m1; \
         h a; m0 = measure a; \
         if (m0) { \
             x r; h b; m1 = measure b; \
             if (m1) { reset b; } else { reset b; } \
         } else { \
             h b; m1 = measure b; \
             if (m1) { reset b; } else { reset b; } \
         }",
    );
    let mixed = parse(
        "qubit a; qubit b; qubit r; bit m0; \
         h a; m0 = measure a; \
         if (m0) { x r; reset b; } else { reset b; }",
    );
    let config = EquivalenceConfig {
        output_pairs: vec![
            OutputPair {
                left: Endpoint::Quantum(qubit(&nested, "b")),
                right: Endpoint::Quantum(qubit(&mixed, "b")),
            },
            OutputPair {
                left: Endpoint::Quantum(qubit(&nested, "r")),
                right: Endpoint::Quantum(qubit(&mixed, "r")),
            },
        ],
        ..EquivalenceConfig::default()
    };

    let result = analyze(&nested, &mixed, &config).unwrap();

    assert_eq!(result.verdict, Verdict::Equivalent);
    assert_eq!(result.evidence, Evidence::DensityKernelExact);
    // Kernel term counts are representation details: the existing history
    // reductions already produce (2, 4), even with region summaries disabled.
    // Check the channel above and its distinction from a pure state below.

    // The same nested program is not the pure |+> state on `r`: the hidden
    // `m0` histories add as an incoherent mixture, so its off-diagonal density
    // entries vanish.
    let pure = parse("qubit b; qubit r; h r; reset b;");
    let pure_config = EquivalenceConfig {
        output_pairs: vec![
            OutputPair {
                left: Endpoint::Quantum(qubit(&nested, "b")),
                right: Endpoint::Quantum(qubit(&pure, "b")),
            },
            OutputPair {
                left: Endpoint::Quantum(qubit(&nested, "r")),
                right: Endpoint::Quantum(qubit(&pure, "r")),
            },
        ],
        ..EquivalenceConfig::default()
    };
    let result = analyze(&nested, &pure, &pure_config).unwrap();

    assert_ne!(result.verdict, Verdict::Equivalent);
    assert_ne!(result.evidence, Evidence::ExactHps);
}

#[test]
fn multi_component_mixture_never_uses_the_snapshot_certificate() {
    let mixed = parse(
        "qubit a; qubit r; qubit d; bit m; \
         h a; m = measure a; \
         if (m) { x r; reset d; } else { reset d; }",
    );
    let pure = parse("qubit r; qubit d; h r; reset d;");
    let config = EquivalenceConfig {
        output_pairs: vec![
            OutputPair {
                left: Endpoint::Quantum(qubit(&mixed, "r")),
                right: Endpoint::Quantum(qubit(&pure, "r")),
            },
            OutputPair {
                left: Endpoint::Quantum(qubit(&mixed, "d")),
                right: Endpoint::Quantum(qubit(&pure, "d")),
            },
        ],
        ..EquivalenceConfig::default()
    };

    let prepared = prepare_comparison(&mixed, &pure, &config).unwrap();
    assert!(prepared.left.hps.components.len() > 1);
    assert_eq!(prepared.right.hps.components.len(), 1);

    let result = analyze(&mixed, &pure, &config).unwrap();

    assert_ne!(result.verdict, Verdict::Equivalent);
    assert_ne!(result.evidence, Evidence::ExactHps);
}

type LiteralCyclotomic = std::collections::BTreeMap<u64, num_rational::BigRational>;
fn literal_add_root(
    out: &mut LiteralCyclotomic,
    p: u64,
    mut c: num_rational::BigRational,
    order: u64,
) {
    let p = p % order;
    let p = if p >= order / 2 {
        c = -c;
        p - order / 2
    } else {
        p
    };
    let total = out
        .remove(&p)
        .unwrap_or_else(|| num_rational::BigRational::from_integer(0.into()))
        + c;
    if total != num_rational::BigRational::from_integer(0.into()) {
        out.insert(p, total);
    }
}
fn literal_product(a: &LiteralCyclotomic, b: &LiteralCyclotomic, order: u64) -> LiteralCyclotomic {
    let mut out = LiteralCyclotomic::new();
    for (pa, ca) in a {
        for (pb, cb) in b {
            literal_add_root(&mut out, pa + pb, ca * cb, order);
        }
    }
    out
}
fn literal_witness_value(w: &irene::equivalence::DensityCounterexample) -> LiteralCyclotomic {
    assert!(w.sqrt_three_coefficients.is_empty());
    let mut value = w.difference_coefficients.iter().cloned().collect();
    for f in &w.exact_factors {
        assert!(f.sqrt_three_coefficients.is_empty());
        value = literal_product(
            &value,
            &f.coefficients.iter().cloned().collect(),
            w.root_of_unity_order,
        );
    }
    value
}
