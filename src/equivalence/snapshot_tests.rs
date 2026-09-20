use super::*;
use crate::symbolic::{
    BooleanPolynomial, Component, HybridMemory, PhaseCoefficient, PhasePolynomial, Scalar, Variable,
};
use num_rational::BigRational;
use std::collections::BTreeMap;

fn q(index: usize) -> Qubit {
    Qubit {
        register: SymbolId(7),
        index,
    }
}
fn x(index: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Input(q(index)))
}
fn y() -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(0))
}
fn side(kind: PreparedOutputKind, value: BooleanPolynomial) -> PreparedSide {
    PreparedSide {
        hps: HybridPathSum {
            input: HybridMemory {
                quantum: [(q(0), x(0)), (q(1), x(1))].into(),
                ..Default::default()
            },
            components: vec![Component {
                guard: vec![],
                path_support: [0].into(),
                scalar: Scalar::one(),
                phase: PhasePolynomial::zero(),
                output: HybridMemory::default(),
            }],
        },
        terminals: vec![PreparedTerminal {
            outputs: vec![PreparedOutput { kind, value }],
        }],
        quantum_input_positions: BTreeMap::new(),
    }
}
fn matched(a: &HybridPathSum, b: &HybridPathSum) -> bool {
    matches!(
        canonical::exact_match(a, b),
        canonical::ExactMatch::Match { .. }
    )
}
fn phase_term(side: &mut PreparedSide, selector: BooleanPolynomial, numerator: i64) {
    side.hps.components[0].phase.add_boolean(
        &selector,
        PhaseCoefficient::rational(BigRational::new(numerator.into(), 8.into())),
    );
}
fn eval(p: &BooleanPolynomial, assignment: usize) -> bool {
    p.evaluate::<std::convert::Infallible>(|v| {
        Ok(match v {
            Variable::Input(q) => assignment & (1 << q.index) != 0,
            Variable::Path(0) => assignment & 4 != 0,
            _ => panic!("unexpected fixture variable"),
        })
    })
    .unwrap()
}
fn phase(phase: &PhasePolynomial, assignment: usize) -> BigRational {
    phase
        .selectors()
        .filter(|(p, _)| eval(p, assignment))
        .map(|(_, c)| c.as_rational().unwrap())
        .sum()
}
fn history_equal(c: &Component, ket: usize, bra: usize) -> bool {
    c.output
        .history
        .iter()
        .all(|h| eval(h.value(), ket) == eval(h.value(), bra))
}

#[test]
fn selected_outputs_cannot_be_omitted_from_matching() {
    let a = side(PreparedOutputKind::Quantum, x(0));
    let b = side(PreparedOutputKind::Quantum, x(0).complement());
    assert!(matched(&a.hps, &b.hps));
    assert!(!matched(&complete_snapshot(&a), &complete_snapshot(&b)));
}

#[test]
fn quantum_and_classical_observations_remain_distinct() {
    let quantum = side(PreparedOutputKind::Quantum, y());
    let classical = side(PreparedOutputKind::Classical, y());
    assert!(!matched(
        &complete_snapshot(&quantum),
        &complete_snapshot(&classical)
    ));
}

#[test]
fn only_constant_phase_is_ignored_with_live_paths() {
    let base = side(PreparedOutputKind::Quantum, y().xor(&x(0)));
    let mut global = base.clone();
    phase_term(&mut global, BooleanPolynomial::one(), 3);
    assert!(matched(
        &complete_snapshot(&base),
        &complete_snapshot(&global)
    ));
    for selector in [x(0), y()] {
        let mut relative = base.clone();
        phase_term(&mut relative, selector, 3);
        assert!(!matched(
            &complete_snapshot(&base),
            &complete_snapshot(&relative)
        ));
    }
}

#[test]
fn history_redundancy_preserves_all_ket_bra_constraints_and_phase_differences() {
    let mut original = side(PreparedOutputKind::Quantum, x(0).xor(&y()));
    original.terminals[0].outputs.push(PreparedOutput {
        kind: PreparedOutputKind::Classical,
        value: x(1),
    });
    original.hps.components[0].output.history = vec![
        HistoryEntry::Discard {
            value: BooleanPolynomial::zero(),
        },
        HistoryEntry::Write {
            target: ClassicalBit {
                register: SymbolId(9),
                index: 3,
            },
            value: BooleanPolynomial::one(),
        },
        HistoryEntry::Discard { value: y() },
        HistoryEntry::Write {
            target: ClassicalBit {
                register: SymbolId(9),
                index: 4,
            },
            value: y(),
        },
        HistoryEntry::Discard { value: x(1) },
        HistoryEntry::Discard {
            value: x(0).xor(&y()),
        },
    ];
    phase_term(&mut original, BooleanPolynomial::one(), 3);
    phase_term(&mut original, x(0), 2);
    phase_term(&mut original, y(), 1);
    let snapshot = complete_snapshot(&original);
    let before = &original.hps.components[0];
    let after = &snapshot.components[0];
    assert_eq!(before.scalar, after.scalar);
    assert_eq!(before.guard, after.guard);
    assert_eq!(before.path_support, after.path_support);
    // Independent ket and bra input/path assignments include off-diagonal
    // channel entries, not just computational-basis probabilities.
    for ket in 0..8 {
        for bra in 0..8 {
            let visible_equal = original.terminals[0]
                .outputs
                .iter()
                .filter(|o| o.kind == PreparedOutputKind::Classical)
                .all(|o| eval(&o.value, ket) == eval(&o.value, bra));
            let original_constraint = visible_equal && history_equal(before, ket, bra);
            let snapshot_constraint = history_equal(after, ket, bra)
                && after
                    .output
                    .classical
                    .values()
                    .all(|v| eval(v, ket) == eval(v, bra));
            assert_eq!(original_constraint, snapshot_constraint);
            let delta = (phase(&before.phase, ket) - phase(&before.phase, bra))
                - (phase(&after.phase, ket) - phase(&after.phase, bra));
            assert!(delta.is_integer());
            for (i, output) in original.terminals[0].outputs.iter().enumerate() {
                let actual = match output.kind {
                    PreparedOutputKind::Quantum => {
                        &after.output.quantum[&Qubit {
                            register: SymbolId(0),
                            index: i,
                        }]
                    }
                    PreparedOutputKind::Classical => {
                        &after.output.classical[&ClassicalBit {
                            register: SymbolId(0),
                            index: i,
                        }]
                    }
                };
                assert_eq!(eval(actual, ket), eval(&output.value, ket));
                assert_eq!(eval(actual, bra), eval(&output.value, bra));
            }
        }
    }
    // Useful dephasing must survive; |0><1| on y is still suppressed.
    assert!(!history_equal(after, 0, 4));
}

#[test]
fn parsed_selected_outputs_are_reinserted_in_paired_order() {
    let parse = |body: &str| {
        crate::frontend::openqasm3::parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
            "snapshot.qasm",
        )
        .unwrap()
    };
    let a = parse("qubit a;");
    let b = parse("qubit b; x b;");
    let aq = super::qubits(&a)[0].clone();
    let bq = super::qubits(&b)[0].clone();
    let config = EquivalenceConfig {
        output_pairs: vec![OutputPair {
            left: Endpoint::Quantum(aq),
            right: Endpoint::Quantum(bq),
        }],
        ..Default::default()
    };
    let prepared = prepare_comparison(&a, &b, &config).unwrap();
    assert!(matched(&prepared.left.hps, &prepared.right.hps));
    assert!(!matched(
        &complete_snapshot(&prepared.left),
        &complete_snapshot(&prepared.right)
    ));
}
