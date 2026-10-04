use irene::equivalence::{Endpoint, EquivalenceConfig, InputPair, OutputPair, Verdict, analyze};
use irene::frontend::openqasm3;
use irene::ir::{Program, Qubit};

fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
        "static-integers.qasm",
    )
    .unwrap()
}

#[test]
fn static_signed_and_machine_integers_preserve_the_complete_channel() {
    for (source, reference) in [
        (
            "const int[32] n=-2; qubit[4] q;
             for int[32] i in [n:1] x q[i - n];
             for int j in [3:-1:0] z q[j];
             if(n < 0) h q[0];",
            "qubit[4] q; x q; z q; h q[0];",
        ),
        (
            "const uint n=4; qubit[n] q; for uint i in [0:n-1] x q[i];
             const int signed_value=-1; if(uint(signed_value) == 4294967295) h q[0];",
            "qubit[4] q; x q; h q[0];",
        ),
        (
            "const int[32] a=-7; const int[32] b=3;
             const int[32] d=a/b; const int[32] r=a%b; qubit[4] q;
             if(d == -2) x q[0]; if(r == -1) h q[1];",
            "qubit[4] q; x q[0]; h q[1];",
        ),
    ] {
        let left = parse(source);
        let right = parse(reference);
        let endpoint = |p: &Program, index| {
            Endpoint::Quantum(Qubit {
                register: p.quantum_registers[0].id,
                index,
            })
        };
        let config = EquivalenceConfig {
            input_pairs: (0..4)
                .map(|i| InputPair {
                    left: endpoint(&left, i),
                    right: endpoint(&right, i),
                })
                .collect(),
            output_pairs: (0..4)
                .map(|i| OutputPair {
                    left: endpoint(&left, i),
                    right: endpoint(&right, i),
                })
                .collect(),
            ..EquivalenceConfig::default()
        };
        let result = analyze(&left, &right, &config).unwrap();
        assert_eq!(result.verdict, Verdict::Equivalent, "{source}: {result:?}");
    }
}
