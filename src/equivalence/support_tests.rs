use super::*;
use crate::frontend::openqasm3;
use crate::symbolic::{Component, HybridMemory, PhaseCoefficient, PhasePolynomial};

fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; {body}"),
        "support.qasm",
    )
    .unwrap()
}

fn enumerate_support(side: &PreparedSide, inputs: &[bool]) -> BTreeSet<Vec<bool>> {
    let paths = side.hps.components[0]
        .path_support
        .iter()
        .copied()
        .collect::<Vec<_>>();
    (0..1usize << paths.len())
        .map(|mask| {
            side.terminals[0]
                .outputs
                .iter()
                .map(|o| {
                    o.value
                        .evaluate::<std::convert::Infallible>(|v| {
                            Ok(match v {
                                Variable::Input(q) => inputs[q.index],
                                Variable::Path(p) => {
                                    mask & (1 << paths.iter().position(|i| i == p).unwrap()) != 0
                                }
                            })
                        })
                        .unwrap()
                })
                .collect()
        })
        .collect()
}

#[test]
fn public_support_witnesses_replay_on_actual_parsed_programs_in_both_directions() {
    for (a, b) in [
        (
            "bit c; h q[0]; c = measure q[0];",
            "bit c; c = measure q[0];",
        ),
        ("bit c = 0; h q[0];", "bit c = 0; h q[1];"),
        ("bit c = 0; x q[0];", "bit c = 0;"),
        ("bit c = 0; cx q[0],q[1];", "bit c = 0;"),
    ] {
        let left = parse(a);
        let right = parse(b);
        for (left, right) in [(&left, &right), (&right, &left)] {
            let config = EquivalenceConfig::positional(left, right).unwrap();
            assert!(unitary_trace::certificate(left, right, &config).is_none());
            let result = analyze(left, right, &config).unwrap();
            assert_eq!(result.verdict, Verdict::NotEquivalent);
            assert_eq!(result.evidence, Evidence::OutputSupportMismatch);
            let witness = result.counterexample.unwrap();
            assert_eq!(witness.bra_inputs, None);
            assert_eq!(witness.ket_inputs.len(), config.input_pairs.len());
            let p = prepare_comparison(left, right, &config).unwrap();
            assert_ne!(
                enumerate_support(&p.left, &witness.ket_inputs),
                enumerate_support(&p.right, &witness.ket_inputs)
            );
        }
    }
}

#[test]
fn initialized_inputs_and_hidden_history_supports_are_handled() {
    let left = parse("bit c; h q[0]; c = measure q[0];");
    let right = parse("bit c; c = measure q[0];");
    let mut config = EquivalenceConfig::positional(&left, &right).unwrap();
    config.input_pairs.clear();
    let result = analyze(&left, &right, &config).unwrap();
    assert_eq!(result.evidence, Evidence::OutputSupportMismatch);
    assert_eq!(
        result.counterexample.unwrap().ket_inputs,
        Vec::<bool>::new()
    );

    let left = parse("bit c; h q[0]; h q[1]; c = measure q[1];");
    let right = parse("bit c; h q[1]; c = measure q[1];");
    let mut config = EquivalenceConfig::positional(&left, &right).unwrap();
    config.output_pairs.truncate(1);
    let result = analyze(&left, &right, &config).unwrap();
    assert_eq!(result.evidence, Evidence::OutputSupportMismatch);
    let p = prepare_comparison(&left, &right, &config).unwrap();
    let witness = result.counterexample.unwrap().ket_inputs;
    assert_ne!(
        enumerate_support(&p.left, &witness),
        enumerate_support(&p.right, &witness)
    );
}

#[test]
fn equal_support_does_not_prove_equal_phase_or_probabilities() {
    let left = parse("bit c = 0; z q[0];");
    let right = parse("bit c = 0;");
    let config = EquivalenceConfig::positional(&left, &right).unwrap();
    let result = analyze(&left, &right, &config).unwrap();
    assert_eq!(result.verdict, Verdict::Unknown);
    assert_eq!(result.evidence, Evidence::KernelAggregationRequired);
    assert!(result.counterexample.is_none());
}

fn bits(mask: usize, width: usize) -> Vec<bool> {
    (0..width).map(|i| mask & (1 << i) != 0).collect()
}
fn q(index: usize) -> Qubit {
    Qubit {
        register: SymbolId(7),
        index,
    }
}

fn descriptor(code: usize) -> ExactOutputSupport {
    let columns = vec![bits(code & 3, 2), bits((code >> 2) & 3, 2)];
    ExactOutputSupport {
        width: 2,
        rank: column_rank(2, &columns),
        path_columns: columns,
        offset: bits((code >> 4) & 3, 2),
        input_columns: [
            (q(0), bits((code >> 6) & 3, 2)),
            (q(1), bits((code >> 8) & 3, 2)),
        ]
        .into(),
    }
}

// Independent truth-table oracle: no Gaussian elimination or span membership.
fn table_support(code: usize, input: usize) -> BTreeSet<usize> {
    let mut offset = (code >> 4) & 3;
    if input & 1 != 0 {
        offset ^= (code >> 6) & 3;
    }
    if input & 2 != 0 {
        offset ^= (code >> 8) & 3;
    }
    (0..4)
        .map(|y| {
            offset
                ^ if y & 1 != 0 { code & 3 } else { 0 }
                ^ if y & 2 != 0 { (code >> 2) & 3 } else { 0 }
        })
        .collect()
}

#[test]
fn generated_affine_coset_witnesses_match_exhaustive_truth_tables() {
    let mut equal = 0;
    let mut different = 0;
    for a in 0..1024 {
        for b in [a, (37 * a + 19) % 1024, (a + 277) % 1024] {
            let witness = output_support_witness(&descriptor(a), &descriptor(b), 2);
            let all_equal = (0..4).all(|x| table_support(a, x) == table_support(b, x));
            assert_eq!(witness.is_none(), all_equal, "{a} {b}");
            if let Some(witness) = witness {
                let x = usize::from(witness[0]) | (usize::from(witness[1]) << 1);
                assert_ne!(table_support(a, x), table_support(b, x));
                different += 1;
            } else {
                equal += 1;
            }
        }
    }
    assert!(equal > 0 && different > 0);
    assert_eq!(column_rank(0, &[]), 0);
    assert!(column_span_contains(0, &[], &[]));
}

fn y(index: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(index))
}
fn side() -> PreparedSide {
    PreparedSide {
        hps: HybridPathSum {
            input: HybridMemory::default(),
            components: vec![Component {
                guard: vec![],
                path_support: [0, 1].into(),
                scalar: Scalar::one(),
                phase: PhasePolynomial::zero(),
                output: HybridMemory {
                    history: vec![HistoryEntry::Discard { value: y(1) }],
                    ..Default::default()
                },
            }],
        },
        terminals: vec![PreparedTerminal {
            outputs: vec![PreparedOutput {
                kind: PreparedOutputKind::Quantum,
                value: y(0),
            }],
        }],
        quantum_input_positions: Default::default(),
    }
}

#[test]
fn hidden_history_can_prevent_interference_but_phase_cancellation_cannot_be_ignored() {
    let mut s = side();
    assert!(
        exact_output_support(&s).is_some(),
        "history distinguishes paths with the same visible output"
    );
    s.hps.components[0].output.history.clear();
    s.hps.components[0].phase.add_boolean(
        &y(1),
        PhaseCoefficient::rational(BigRational::new(1.into(), 2.into())),
    );
    // sum_y1 (-1)^y1 = 0. Merely reading the output expression would invent
    // support for this zero amplitude; the joint-rank condition must refuse.
    assert!(exact_output_support(&s).is_none());
}

#[test]
fn guards_nonlinearity_multiple_components_and_possibly_zero_weights_are_refused() {
    let base = side();
    let mut guard = base.clone();
    guard.hps.components[0].guard.push(y(0));
    assert!(exact_output_support(&guard).is_none());
    let mut nonlinear = base.clone();
    nonlinear.terminals[0].outputs[0].value = y(0).and(&y(1));
    assert!(exact_output_support(&nonlinear).is_none());
    let mut history = base.clone();
    history.hps.components[0].output.history = vec![HistoryEntry::Discard {
        value: y(0).and(&y(1)),
    }];
    assert!(exact_output_support(&history).is_none());
    let mut multiple = base.clone();
    multiple.hps.components.push(base.hps.components[0].clone());
    multiple.terminals.push(base.terminals[0].clone());
    assert!(exact_output_support(&multiple).is_none());
    for scalar in [
        Scalar::zero(),
        Scalar::Select {
            condition: y(0),
            when_true: Box::new(Scalar::one()),
            when_false: Box::new(Scalar::zero()),
        },
        Scalar::Add(
            Box::new(Scalar::one()),
            Box::new(Scalar::Neg(Box::new(Scalar::one()))),
        ),
        Scalar::Sqrt(Box::new(Scalar::Rational(BigRational::from_integer(
            (-1).into(),
        )))),
    ] {
        let mut s = base.clone();
        s.hps.components[0].scalar = scalar;
        assert!(exact_output_support(&s).is_none());
    }
    let mut signed = base;
    signed.hps.components[0].scalar = Scalar::Select {
        condition: y(0),
        when_true: Box::new(Scalar::one()),
        when_false: Box::new(Scalar::Neg(Box::new(Scalar::one()))),
    };
    assert!(exact_output_support(&signed).is_some());
}

#[test]
fn joint_rank_admission_matches_exhaustive_path_injectivity() {
    // Every linear map from two paths to one output and one history bit.
    for code in 0..16 {
        let expression = |mask: usize| {
            let mut value = BooleanPolynomial::zero();
            if mask & 1 != 0 {
                value = value.xor(&y(0));
            }
            if mask & 2 != 0 {
                value = value.xor(&y(1));
            }
            value
        };
        let mut s = side();
        s.terminals[0].outputs[0].value = expression(code & 3);
        s.hps.components[0].output.history = vec![HistoryEntry::Discard {
            value: expression(code >> 2),
        }];
        let pairs = (0usize..4)
            .map(|y| {
                (
                    (y & (code & 3)).count_ones() % 2,
                    (y & (code >> 2)).count_ones() % 2,
                )
            })
            .collect::<BTreeSet<_>>();
        assert_eq!(
            exact_output_support(&s).is_some(),
            pairs.len() == 4,
            "map {code}"
        );
    }
}
