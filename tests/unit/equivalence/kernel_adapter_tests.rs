use super::kernel::{KernelBooleanPolynomial as Bool, KernelVariable as Var};
use super::*;
use crate::frontend::openqasm3;

fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; bit c0 = 0; bit c1 = 0; {body}"),
        "kernel-adapter.qasm",
    )
    .unwrap()
}

fn prepare(body: &str) -> PreparedComparison {
    let p = parse(body);
    let config = EquivalenceConfig::positional(&p, &p).unwrap();
    prepare_comparison(&p, &p, &config).unwrap()
}

#[test]
fn interleaved_outputs_and_reversed_inputs_preserve_pairing_order() {
    let p = parse("");
    let mut config = EquivalenceConfig::positional(&p, &p).unwrap();
    config.input_pairs.reverse();
    let outputs = config.output_pairs.clone();
    // Q0,C0,Q1,C1, with reversed quantum output order.
    config.output_pairs = vec![
        outputs[1].clone(),
        outputs[2].clone(),
        outputs[0].clone(),
        outputs[3].clone(),
    ];
    let prepared = prepare_comparison(&p, &p, &config).unwrap();
    let before = prepared.clone();
    let left = kernel_for(&prepared.left).unwrap();
    let right = kernel_for(&prepared.right).unwrap();
    assert_eq!(left, right);
    assert_eq!(prepared, before);
    assert_eq!(left.input_pairs.len(), 2);
    assert_eq!(
        (left.quantum_output_count, left.classical_output_count),
        (2, 2)
    );
    let term = &left.terms[0];
    assert_eq!(
        term.quantum_outputs_ket,
        vec![
            Bool::variable(Var::InputKet(0)),
            Bool::variable(Var::InputKet(1))
        ]
    );
    assert_eq!(
        term.quantum_outputs_bra,
        vec![
            Bool::variable(Var::InputBra(0)),
            Bool::variable(Var::InputBra(1))
        ]
    );
    assert!(
        term.classical_outputs
            .iter()
            .all(|o| o.ket.is_zero() && o.bra.is_zero())
    );
}

#[test]
fn discarded_quantum_output_becomes_internal_history() {
    let p = parse("");
    let mut config = EquivalenceConfig::positional(&p, &p).unwrap();
    config.output_pairs.truncate(1);
    let prepared = prepare_comparison(&p, &p, &config).unwrap();
    let kernel = kernel_for(&prepared.left).unwrap();
    assert_eq!(kernel.input_pairs.len(), 2); // Includes the unobserved input.
    assert_eq!(
        (kernel.quantum_output_count, kernel.classical_output_count),
        (1, 0)
    );
    let history = &kernel.terms[0].history_equalities;
    assert!(
        history
            .iter()
            .any(|eq| eq.left == Bool::variable(Var::InputKet(1))
                && eq.right == Bool::variable(Var::InputBra(1)))
    );
}

#[test]
fn ket_bra_paths_are_disjoint_and_components_form_cross_product() {
    let mut prepared = prepare("h q[0];");
    let component = prepared.left.hps.components[0].clone();
    let terminal = prepared.left.terminals[0].clone();
    prepared.left.hps.components.push(component);
    prepared.left.terminals.push(terminal);
    let kernel = kernel_for(&prepared.left).unwrap();
    assert_eq!(kernel.terms.len(), 4); // Not two independent density terms.
    for (index, term) in kernel.terms.iter().enumerate() {
        assert!(!term.ket_paths.is_empty());
        assert!(term.ket_paths.is_disjoint(&term.bra_paths));
        assert!(
            term.ket_paths
                .iter()
                .all(|v| matches!(v, Var::PathKet { term, .. } if *term == index))
        );
        assert!(
            term.bra_paths
                .iter()
                .all(|v| matches!(v, Var::PathBra { term, .. } if *term == index))
        );
    }
}

#[test]
fn terminal_mismatch_and_noncanonical_input_are_build_errors() {
    let mut p = prepare("");
    p.left.terminals.clear();
    assert!(matches!(
        kernel_for(&p.left),
        Err(KernelBuildError::TerminalCount { .. })
    ));
    let mut p = prepare("");
    *p.left.hps.input.quantum.values_mut().next().unwrap() = BooleanPolynomial::zero();
    assert_eq!(
        kernel_for(&p.left),
        Err(KernelBuildError::NonCanonicalInputSignature)
    );
}

#[test]
fn each_program_keeps_its_own_history_constraints() {
    let left = parse("reset q[0];");
    let right = parse("x q[0]; reset q[0];");
    let config = EquivalenceConfig::positional(&left, &right).unwrap();
    let prepared = prepare_comparison(&left, &right, &config).unwrap();
    for side in [&prepared.left, &prepared.right] {
        let kernel = kernel_for(side).unwrap();
        assert!(!kernel.terms[0].history_equalities.is_empty());
        for equality in &kernel.terms[0].history_equalities {
            assert!(
                equality
                    .left
                    .variables()
                    .iter()
                    .all(|v| matches!(v, Var::InputKet(_) | Var::PathKet { .. }))
            );
            assert!(
                equality
                    .right
                    .variables()
                    .iter()
                    .all(|v| matches!(v, Var::InputBra(_) | Var::PathBra { .. }))
            );
        }
    }
}
