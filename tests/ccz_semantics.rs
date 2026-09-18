use irene::frontend::{openqasm2, openqasm3};
use irene::ir::{ClassicalBit, Program, Qubit};
use irene::symbolic::{
    ExecutionConfig, HybridPathSum, OutputSelection, PhaseCoefficient, Scalar, Variable, execute,
};
use num_rational::BigRational;

fn parse(version: u8, body: &str) -> Result<Program, String> {
    let declarations = if version == 2 {
        "include \"qelib1.inc\"; qreg q[4]; creg c[1];"
    } else {
        "include \"stdgates.inc\"; qubit[4] q; bit[1] c;"
    };
    let source = format!("OPENQASM {version}.0; {declarations} {body}");
    if version == 2 {
        openqasm2::parse_str(&source, "ccz-test.qasm").map_err(|e| format!("{e:?}"))
    } else {
        openqasm3::parse_str(&source, "ccz-test.qasm").map_err(|e| format!("{e:?}"))
    }
}

fn run(version: u8, body: &str) -> HybridPathSum {
    run_observed(version, body, false)
}

fn run_observed(version: u8, body: &str, keep_classical: bool) -> HybridPathSum {
    let program = parse(version, body).unwrap();
    let outputs = (0..4).map(|index| Qubit {
        register: program.quantum_registers[0].id,
        index,
    });
    execute(
        &program,
        &ExecutionConfig::all_symbolic(),
        &OutputSelection::new(
            outputs,
            keep_classical.then(|| ClassicalBit {
                register: program.classical_registers[0].id,
                index: 0,
            }),
        ),
    )
    .unwrap()
}

// Inspect the exact symbolic phase, not only basis-state output probabilities:
// a diagonal gate must retain its relative phase on arbitrary superpositions.
fn check_phase(hps: &HybridPathSum, feedback: bool) {
    assert_eq!(hps.components.len(), 1);
    let component = &hps.components[0];
    assert!(component.path_support.is_empty());
    assert!(component.guard.is_empty());
    assert_eq!(component.scalar, Scalar::one());
    assert_eq!(component.output.quantum, hps.input.quantum);
    let terms: Vec<_> = component.phase.terms().collect();
    assert_eq!(terms.len(), 1);
    let (monomial, coefficient) = terms[0];
    assert_eq!(
        *coefficient,
        PhaseCoefficient::rational(BigRational::new(1.into(), 2.into()))
    );
    let mut indices = monomial
        .variables()
        .map(|variable| match variable {
            Variable::Input(qubit) => qubit.index,
            Variable::Path(_) => panic!("CCZ must not introduce paths"),
        })
        .collect::<Vec<_>>();
    indices.sort_unstable();
    assert_eq!(
        indices,
        if feedback {
            vec![0, 1, 2, 3]
        } else {
            vec![0, 1, 2]
        }
    );
    for input in 0..16 {
        let negative = indices.iter().all(|index| (input >> index) & 1 == 1);
        let expected = input & 7 == 7 && (!feedback || input & 8 != 0);
        assert_eq!(negative, expected, "input={input:04b}");
    }
}

#[test]
fn ccz_has_exact_diagonal_phase_for_all_operand_orders() {
    for version in [2, 3] {
        for [a, b, c] in [
            [0, 1, 2],
            [0, 2, 1],
            [1, 0, 2],
            [1, 2, 0],
            [2, 0, 1],
            [2, 1, 0],
        ] {
            let hps = run(version, &format!("ccz q[{a}],q[{b}],q[{c}];"));
            check_phase(&hps, false);
            assert!(hps.components[0].output.history.is_empty());
        }
    }
}

#[test]
fn two_ccz_gates_cancel_exactly() {
    for version in [2, 3] {
        assert_eq!(
            run(version, "ccz q[0],q[1],q[2]; ccz q[0],q[1],q[2];"),
            run(version, ""),
        );
    }
}

#[test]
fn feedback_ccz_preserves_history_and_uses_the_measurement_predicate() {
    for version in [2, 3] {
        let condition = if version == 2 { "c == 1" } else { "c[0]" };
        let prefix = "measure q[3] -> c[0];";
        let hps = run_observed(
            version,
            &format!("{prefix} if ({condition}) ccz q[0],q[1],q[2];"),
            true,
        );
        check_phase(&hps, true);
        let measured = run_observed(version, prefix, true);
        assert_eq!(hps.components[0].output, measured.components[0].output);
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
            assert!(parse(version, body).is_err(), "OpenQASM {version}: {body}");
        }
    }
}
