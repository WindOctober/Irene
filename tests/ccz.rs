use irene::equivalence::{Endpoint, EquivalenceConfig, InputPair, OutputPair, Verdict, analyze};
use irene::frontend::{openqasm2, openqasm3};
use irene::ir::{Program, Qubit};

fn source(version: u8, body: &str) -> String {
    let declarations = if version == 2 {
        "include \"qelib1.inc\"; qreg q[4]; creg c[1];"
    } else {
        "include \"stdgates.inc\"; qubit[4] q; bit[1] c;"
    };
    format!("OPENQASM {version}.0; {declarations} {body}")
}

fn parse(version: u8, body: &str) -> Program {
    let text = source(version, body);
    if version == 2 {
        openqasm2::parse_str(&text, "ccz.qasm").unwrap()
    } else {
        openqasm3::parse_str(&text, "ccz.qasm").unwrap()
    }
}

fn compare(left: &Program, right: &Program, expected: Verdict) {
    let endpoint = |p: &Program, index| {
        Endpoint::Quantum(Qubit {
            register: p.quantum_registers[0].id,
            index,
        })
    };
    let config = EquivalenceConfig {
        input_pairs: (0..4)
            .map(|i| InputPair {
                left: endpoint(left, i),
                right: endpoint(right, i),
            })
            .collect(),
        output_pairs: (0..4)
            .map(|i| OutputPair {
                left: endpoint(left, i),
                right: endpoint(right, i),
            })
            .collect(),
        ..EquivalenceConfig::default()
    };
    let result = analyze(left, right, &config).unwrap();
    assert_eq!(result.verdict, expected, "{result:?}");
}

#[test]
fn ccz_matches_h_ccx_h_for_every_operand_order() {
    for version in [2, 3] {
        let reference = parse(version, "h q[2]; ccx q[0],q[1],q[2]; h q[2];");
        for [a, b, c] in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            let direct = parse(version, &format!("ccz q[{a}],q[{b}],q[{c}];"));
            compare(&direct, &reference, Verdict::Equivalent);
        }
        compare(
            &parse(version, "ccz q[0],q[1],q[2]; ccz q[0],q[1],q[2];"),
            &parse(version, ""),
            Verdict::Equivalent,
        );
        compare(
            &parse(version, "ccz q[0],q[1],q[2];"),
            &parse(version, ""),
            Verdict::NotEquivalent,
        );
    }
}

#[test]
fn ccz_supports_control_modifiers_and_measurement_feedback() {
    let direct = parse(3, "ccz q[0],q[1],q[2];");
    for spelling in ["ctrl @ cz", "ctrl(2) @ z", "ctrl @ ctrl @ z"] {
        compare(
            &direct,
            &parse(3, &format!("{spelling} q[0],q[1],q[2];")),
            Verdict::Equivalent,
        );
    }
    for version in [2, 3] {
        let condition = if version == 2 { "c == 1" } else { "c[0]" };
        let prefix = "h q[3]; measure q[3] -> c[0];";
        let direct = parse(
            version,
            &format!("{prefix} if ({condition}) ccz q[0],q[1],q[2];"),
        );
        let reference = parse(
            version,
            &format!(
                "{prefix} if ({condition}) h q[2];
             if ({condition}) ccx q[0],q[1],q[2]; if ({condition}) h q[2];"
            ),
        );
        compare(&direct, &reference, Verdict::Equivalent);
        compare(&direct, &parse(version, prefix), Verdict::NotEquivalent);
    }
}
