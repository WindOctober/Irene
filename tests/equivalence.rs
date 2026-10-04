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
