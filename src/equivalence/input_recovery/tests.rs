use super::*;
use crate::ir::SymbolId;

fn qubit(index: usize) -> Qubit {
    Qubit {
        register: SymbolId(7),
        index,
    }
}
fn x(index: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Input(qubit(index)))
}
fn inputs(width: usize) -> BTreeMap<Qubit, usize> {
    (0..width).map(|i| (qubit(i), i)).collect()
}

fn truth_table_is_injective(
    outputs: &[BooleanPolynomial],
    inputs: &BTreeMap<Qubit, usize>,
) -> bool {
    let images = (0..1usize << inputs.len())
        .map(|mask| {
            outputs
                .iter()
                .map(|p| {
                    p.evaluate::<std::convert::Infallible>(|v| {
                        let Variable::Input(q) = v else {
                            panic!("unexpected path in oracle")
                        };
                        Ok(mask & (1 << inputs[q]) != 0)
                    })
                    .unwrap()
                })
                .collect::<Vec<_>>()
        })
        .collect::<BTreeSet<_>>();
    images.len() == 1usize << inputs.len()
}

#[test]
fn recovery_handles_nonlinear_dependencies_output_permutations_and_constants() {
    let outputs = [
        x(2).xor(&x(0).and(&x(1))).complement(),
        x(1).xor(&x(0)),
        x(0),
    ];
    assert!(triangular_injectivity(&outputs, &inputs(3)));
    assert!(truth_table_is_injective(&outputs, &inputs(3)));
    let mut reversed = outputs.to_vec();
    reversed.reverse();
    assert!(triangular_injectivity(&reversed, &inputs(3)));
}

#[test]
fn gaussian_recovery_can_unlock_further_nonlinear_rows() {
    let outputs = [
        x(0).xor(&x(1)),
        x(1).xor(&x(2)),
        x(0).xor(&x(1)).xor(&x(2)),
        x(3).xor(&x(0).and(&x(2))),
    ];
    assert!(triangular_injectivity(&outputs, &inputs(4)));
    assert!(truth_table_is_injective(&outputs, &inputs(4)));
}

#[test]
fn self_dependence_missing_inputs_and_foreign_variables_are_not_certificates() {
    for outputs in [
        vec![x(0).xor(&x(0).and(&x(1))), x(1)],
        vec![x(0), x(0)],
        vec![x(0), x(2)],
        vec![x(0), BooleanPolynomial::variable(Variable::Path(0))],
    ] {
        assert!(!triangular_injectivity(&outputs, &inputs(2)));
    }
    assert!(!triangular_injectivity(
        &[BooleanPolynomial::one()],
        &inputs(1)
    ));
    assert!(triangular_injectivity(&[], &inputs(0)));
    assert!(triangular_injectivity(
        &[BooleanPolynomial::one()],
        &inputs(0)
    ));
}

#[test]
fn all_256_two_input_boolean_maps_have_sound_positive_certificates() {
    let terms = [BooleanPolynomial::one(), x(0), x(1), x(0).and(&x(1))];
    let polynomials = (0..16)
        .map(|mask| {
            terms
                .iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .fold(BooleanPolynomial::zero(), |a, (_, b)| a.xor(b))
        })
        .collect::<Vec<_>>();
    let mut accepted = 0;
    for a in &polynomials {
        for b in &polynomials {
            let outputs = [a.clone(), b.clone()];
            if triangular_injectivity(&outputs, &inputs(2)) {
                assert!(truth_table_is_injective(&outputs, &inputs(2)));
                accepted += 1;
            }
        }
    }
    assert!(accepted > 0);
}

#[test]
fn all_three_input_affine_maps_agree_with_exhaustive_injectivity() {
    for matrix in 0..512 {
        for constant in 0..8 {
            let outputs = (0..3)
                .map(|row| {
                    let mut p = if constant & (1 << row) != 0 {
                        BooleanPolynomial::one()
                    } else {
                        BooleanPolynomial::zero()
                    };
                    for column in 0..3 {
                        if matrix & (1 << (3 * row + column)) != 0 {
                            p = p.xor(&x(column));
                        }
                    }
                    p
                })
                .collect::<Vec<_>>();
            assert_eq!(
                triangular_injectivity(&outputs, &inputs(3)),
                truth_table_is_injective(&outputs, &inputs(3)),
                "matrix {matrix}, constant {constant}"
            );
        }
    }
}

#[test]
fn insufficient_budget_refuses_without_proving_noninjectivity() {
    let outputs = [
        x(0).xor(&x(1)),
        x(1).xor(&x(2)),
        x(0).xor(&x(1)).xor(&x(2)),
        x(3).xor(&x(0).and(&x(2))),
    ];
    let mut refused = false;
    let mut accepted = false;
    for budget in 0..256 {
        if with_budget(&outputs, &inputs(4), budget) {
            accepted = true;
        } else {
            refused = true;
        }
        assert!(!with_budget(&[x(0), x(0)], &inputs(2), budget));
    }
    assert!(refused && accepted);
    assert!(truth_table_is_injective(&outputs, &inputs(4)));
}

#[test]
fn actual_frontend_and_execution_outputs_admit_reversible_boolean_circuits() {
    use crate::equivalence::{EquivalenceConfig, prepare_comparison};
    use crate::frontend::openqasm3;
    for body in [
        "cx q[0],q[1]; ccx q[0],q[1],q[2];",
        "ccx q[0],q[1],q[2]; swap q[0],q[2]; x q[1];",
    ] {
        let program = openqasm3::parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {body}"),
            "input-recovery.qasm",
        )
        .unwrap();
        let p = prepare_comparison(
            &program,
            &program,
            &EquivalenceConfig::positional(&program, &program).unwrap(),
        )
        .unwrap();
        let inputs = p
            .left
            .hps
            .input
            .quantum
            .keys()
            .cloned()
            .enumerate()
            .map(|(i, q)| (q, i))
            .collect();
        let outputs = p.left.terminals[0]
            .outputs
            .iter()
            .map(|o| o.value.clone())
            .collect::<Vec<_>>();
        assert!(triangular_injectivity(&outputs, &inputs));
        assert!(truth_table_is_injective(&outputs, &inputs));
    }
}
