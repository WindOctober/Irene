use super::*;
use crate::symbolic::{Component, HybridMemory};
use std::convert::Infallible;

fn rational(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}
fn q() -> Qubit {
    Qubit {
        register: SymbolId(8),
        index: 0,
    }
}
fn path() -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(0))
}
fn component() -> Component {
    Component {
        guard: vec![],
        scalar: Scalar::one(),
        path_support: BTreeSet::new(),
        phase: PhasePolynomial::zero(),
        output: HybridMemory::default(),
    }
}

// Small exact test oracle: enumerate kernel binders and evaluate Q(i) entries.
// This does not call the production aggregator or solver.
fn entry(
    kernel: &DensityKernel,
    x: bool,
    xp: bool,
    out: bool,
    outp: bool,
    classical: Option<bool>,
) -> (BigRational, BigRational) {
    let mut total = (rational(0), rational(0));
    for term in &kernel.terms {
        let paths: Vec<_> = term
            .ket_paths
            .iter()
            .chain(&term.bra_paths)
            .cloned()
            .collect();
        for mask in 0..1usize << paths.len() {
            let mut values: BTreeMap<_, _> = paths
                .iter()
                .enumerate()
                .map(|(i, p)| (p.clone(), mask & (1 << i) != 0))
                .collect();
            values.insert(KernelVariable::InputKet(0), x);
            values.insert(KernelVariable::InputBra(0), xp);
            let eval = |p: &KernelBooleanPolynomial| {
                p.as_graph()
                    .evaluate::<Infallible>(|v| Ok(values[&KernelVariable::from_graph_variable(v)]))
                    .unwrap()
            };
            if term.constraint_equations().iter().any(&eval) {
                continue;
            }
            if term.quantum_outputs_ket.iter().any(|p| eval(p) != out)
                || term.quantum_outputs_bra.iter().any(|p| eval(p) != outp)
            {
                continue;
            }
            if term
                .classical_outputs
                .iter()
                .any(|p| Some(eval(&p.ket)) != classical)
            {
                continue;
            }
            let phase = |p: &KernelPhasePolynomial| -> BigRational {
                p.selectors()
                    .filter(|(s, _)| eval(s))
                    .map(|(_, c)| c.as_rational().unwrap())
                    .sum()
            };
            let quarter_turns = (phase(&term.phase.ket) - phase(&term.phase.bra)) * rational(4);
            assert!(quarter_turns.is_integer());
            let quarter = quarter_turns
                .to_integer()
                .to_string()
                .parse::<i64>()
                .unwrap()
                .rem_euclid(4);
            let (KernelScalar::Rational(a), KernelScalar::Rational(b)) =
                (&term.weight.ket, &term.weight.bra)
            else {
                panic!("oracle fixtures use rational amplitudes")
            };
            let weight = a * b;
            match quarter {
                0 => total.0 += weight,
                1 => total.1 += weight,
                2 => total.0 -= weight,
                3 => total.1 -= weight,
                _ => unreachable!(),
            }
        }
    }
    total
}

#[test]
fn coherent_cross_terms_preserve_constructive_and_destructive_interference() {
    for opposite in [false, true] {
        let a = component();
        let mut b = component();
        if opposite {
            b.phase.add_boolean(
                &BooleanPolynomial::one(),
                PhaseCoefficient::rational(BigRational::new(1.into(), 2.into())),
            );
        }
        let hps = HybridPathSum {
            input: HybridMemory::default(),
            components: vec![a, b],
        };
        let terminal = KernelTerminalInput {
            quantum: vec![BooleanPolynomial::zero()],
            classical: vec![],
        };
        let kernel = build_kernel(&KernelInput::new(
            &hps,
            vec![],
            vec![terminal.clone(), terminal],
        ))
        .unwrap();
        assert_eq!(
            entry(&kernel, false, false, false, false, None),
            (rational(if opposite { 0 } else { 4 }), rational(0))
        );
    }
}

#[test]
fn guards_on_independent_ket_bra_paths_need_history_to_exclude_cross_terms() {
    for measured in [false, true] {
        let mut a = component();
        a.path_support.insert(0);
        a.guard.push(path()); // y = 0
        if measured {
            a.output
                .history
                .push(HistoryEntry::Discard { value: path() });
        }
        let mut b = a.clone();
        b.guard = vec![path().complement()]; // y = 1
        let hps = HybridPathSum {
            input: HybridMemory::default(),
            components: vec![a, b],
        };
        let terminal = KernelTerminalInput {
            quantum: vec![path()],
            classical: vec![],
        };
        let kernel = build_kernel(&KernelInput::new(
            &hps,
            vec![],
            vec![terminal.clone(), terminal],
        ))
        .unwrap();
        for out in [false, true] {
            for outp in [false, true] {
                assert_eq!(
                    entry(&kernel, false, false, out, outp, None),
                    (
                        rational(if !measured || out == outp { 1 } else { 0 }),
                        rational(0)
                    )
                );
            }
        }
    }
}

#[test]
fn classical_outputs_supply_the_same_dephasing_constraint() {
    let mut a = component();
    a.path_support.insert(0);
    let hps = HybridPathSum {
        input: HybridMemory::default(),
        components: vec![a],
    };
    let kernel = build_kernel(&KernelInput::new(
        &hps,
        vec![],
        vec![KernelTerminalInput {
            quantum: vec![path()],
            classical: vec![path()],
        }],
    ))
    .unwrap();
    for out in [false, true] {
        for outp in [false, true] {
            for c in [false, true] {
                assert_eq!(
                    entry(&kernel, false, false, out, outp, Some(c)),
                    (
                        rational(if out == outp && out == c { 1 } else { 0 }),
                        rational(0)
                    )
                );
            }
        }
    }
}

#[test]
fn independent_input_indices_and_bra_conjugation_preserve_channel_entries() {
    let input = BooleanPolynomial::variable(Variable::Input(q()));
    let mut a = component();
    a.phase.add_boolean(
        &input,
        PhaseCoefficient::rational(BigRational::new(1.into(), 4.into())),
    );
    let hps = HybridPathSum {
        input: HybridMemory {
            quantum: [(q(), input.clone())].into(),
            ..Default::default()
        },
        components: vec![a],
    };
    let kernel = build_kernel(&KernelInput::new(
        &hps,
        vec![q()],
        vec![KernelTerminalInput {
            quantum: vec![input],
            classical: vec![],
        }],
    ))
    .unwrap();
    for x in [false, true] {
        for xp in [false, true] {
            for out in [false, true] {
                for outp in [false, true] {
                    let expected = if out != x || outp != xp {
                        (0, 0)
                    } else if x == xp {
                        (1, 0)
                    } else if x {
                        (0, 1)
                    } else {
                        (0, -1)
                    };
                    assert_eq!(
                        entry(&kernel, x, xp, out, outp, None),
                        (rational(expected.0), rational(expected.1))
                    );
                }
            }
        }
    }
}

#[test]
fn malformed_terminal_rows_and_unbound_paths_are_rejected() {
    let hps = HybridPathSum {
        input: HybridMemory::default(),
        components: vec![component()],
    };
    assert!(matches!(
        build_kernel(&KernelInput::new(&hps, vec![], vec![])),
        Err(KernelBuildError::TerminalCount { .. })
    ));
    assert!(matches!(
        build_kernel(&KernelInput::new(
            &hps,
            vec![],
            vec![KernelTerminalInput {
                quantum: vec![path()],
                classical: vec![],
            }]
        )),
        Err(KernelBuildError::UndeclaredPath { .. })
    ));
}
