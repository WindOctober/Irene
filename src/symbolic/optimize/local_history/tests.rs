use std::collections::BTreeMap;

use num_rational::BigRational;

use super::*;
use crate::ir::{ClassicalBit, Qubit, SymbolId};
use crate::symbolic::{HybridMemory, PhaseCoefficient, Scalar, ScalarBindings};

fn q(index: usize) -> Qubit {
    Qubit {
        register: SymbolId(0),
        index,
    }
}
fn p(index: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(index))
}
fn x() -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Input(q(0)))
}
fn ratio(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}
fn phase(c: &mut Component, value: BooleanPolynomial, n: i64, d: i64) {
    c.phase
        .add_boolean(&value, PhaseCoefficient::rational(ratio(n, d)));
}
fn h_component() -> Component {
    let mut c = Component {
        guard: vec![],
        scalar: Scalar::rational(ratio(1, 2)),
        path_support: BTreeSet::from([0, 1]),
        phase: PhasePolynomial::zero(),
        output: HybridMemory {
            quantum: BTreeMap::from([(q(1), p(0).xor(&p(1)))]),
            classical: BTreeMap::new(),
            history: vec![HistoryEntry::Discard { value: p(1) }],
        },
    };
    phase(&mut c, x().and(&p(0)), 1, 2);
    phase(&mut c, x().and(&p(1)), 1, 2);
    c
}
fn tdg_component() -> Component {
    let mut c = h_component();
    c.output.quantum.insert(q(1), x());
    c.output.history.push(HistoryEntry::Discard {
        value: x().xor(&p(0)),
    });
    c.phase = PhasePolynomial::zero();
    phase(&mut c, x(), -1, 8);
    phase(&mut c, x().and(&p(1)), 1, 2);
    phase(&mut c, p(0).and(&p(1)), 1, 2);
    c
}

// Independent, tiny test-only contraction. Compare ALL density entries,
// including |0><1| inputs, not just basis-state output probabilities.
fn density(c: &Component) -> Vec<(f64, f64)> {
    type Key = (Vec<bool>, bool);
    let mut amplitudes = [BTreeMap::<Key, (f64, f64)>::new(), BTreeMap::new()];
    for (input, world) in amplitudes.iter_mut().enumerate() {
        for bits in 0..1usize << c.path_support.len() {
            let mut bindings = ScalarBindings::default();
            bindings.booleans.insert(Variable::Input(q(0)), input != 0);
            for (i, path) in c.path_support.iter().enumerate() {
                bindings
                    .booleans
                    .insert(Variable::Path(*path), bits & (1 << i) != 0);
            }
            let monomial =
                |m: &crate::symbolic::Monomial| m.variables().all(|v| bindings.booleans[v]);
            let boolean =
                |p: &BooleanPolynomial| p.terms().filter(|m| monomial(m)).count() % 2 == 1;
            if c.guard.iter().any(boolean) {
                continue;
            }
            let turns: f64 = c
                .phase
                .terms()
                .filter(|(m, _)| monomial(m))
                .map(|(_, coefficient)| {
                    let r = coefficient.as_rational().unwrap();
                    r.numer().to_string().parse::<f64>().unwrap()
                        / r.denom().to_string().parse::<f64>().unwrap()
                })
                .sum();
            let scale = c.scalar.evaluate(128, &bindings).unwrap().to_f64();
            let history = c
                .output
                .history
                .iter()
                .map(|h| boolean(HistoryEntry::value(h)))
                .collect();
            let value = world
                .entry((history, boolean(&c.output.quantum[&q(1)])))
                .or_default();
            value.0 += scale * (std::f64::consts::TAU * turns).cos();
            value.1 += scale * (std::f64::consts::TAU * turns).sin();
        }
    }
    let mut kernel = vec![];
    for left in &amplitudes {
        for right in &amplitudes {
            for z in [false, true] {
                for zp in [false, true] {
                    let mut value = (0., 0.);
                    for ((h, output), a) in left {
                        if *output == z
                            && let Some(b) = right.get(&(h.clone(), zp))
                        {
                            value.0 += a.0 * b.0 + a.1 * b.1;
                            value.1 += a.1 * b.0 - a.0 * b.1;
                        }
                    }
                    kernel.push(value);
                }
            }
        }
    }
    kernel
}
fn check_density(before: &Component, after: &Component) {
    for (a, b) in density(before).into_iter().zip(density(after)) {
        assert!(
            (a.0 - b.0).abs() < 1e-12 && (a.1 - b.1).abs() < 1e-12,
            "{a:?} != {b:?}"
        );
    }
}

#[test]
fn affine_live_coordinate_exposes_corrected_h_history() {
    let before = h_component();
    let mut after = before.clone();
    collapse_local_history(&mut after);
    assert!(after.output.history.is_empty());
    assert_eq!(after.path_support.len(), 1);
    check_density(&before, &after);
}

#[test]
fn input_shifted_history_and_history_phase_collapse_tdg() {
    let before = tdg_component();
    let mut after = before.clone();
    collapse_local_history(&mut after);
    assert!(after.output.history.is_empty());
    assert!(after.path_support.is_empty());
    assert_eq!(after.scalar, Scalar::one());
    let mut expected_phase = PhasePolynomial::zero();
    expected_phase.add_boolean(&x(), PhaseCoefficient::rational(ratio(-1, 8)));
    assert_eq!(after.phase, expected_phase);
    check_density(&before, &after);
}

#[test]
fn arbitrary_hidden_phase_is_not_limited_to_clifford() {
    let mut before = tdg_component();
    phase(&mut before, p(1).and(&x().xor(&p(0))), 1, 7);
    let mut after = before.clone();
    collapse_local_history(&mut after);
    assert!(after.output.history.is_empty());
    check_density(&before, &after);
}

#[test]
fn live_quantum_or_classical_outcome_cannot_be_erased() {
    for quantum in [false, true] {
        let mut c = h_component();
        if quantum {
            c.output.quantum.insert(q(2), p(1));
        } else {
            c.output.classical.insert(
                ClassicalBit {
                    register: SymbolId(1),
                    index: 0,
                },
                p(1),
            );
        }
        let before = c.clone();
        collapse_local_history(&mut c);
        assert_eq!(c, before);
    }
}

#[test]
fn input_dependent_relative_phase_and_wrong_correction_remain() {
    for coefficient in [(1, 2), (1, 4)] {
        let mut before = h_component();
        phase(&mut before, x().and(&p(1)), coefficient.0, coefficient.1);
        let mut after = before.clone();
        collapse_local_history(&mut after);
        assert!(!after.output.history.is_empty());
        check_density(&before, &after);
    }
}

#[test]
fn guard_and_input_dependent_probability_are_not_ignored() {
    for guard in [false, true] {
        let mut before = tdg_component();
        if guard {
            before.guard.push(x().and(&p(1)));
        } else {
            before.scalar =
                Scalar::select(x().xor(&p(1)), Scalar::one(), Scalar::rational(ratio(1, 2)));
        }
        let mut after = before.clone();
        collapse_local_history(&mut after);
        assert!(!after.output.history.is_empty());
        check_density(&before, &after);
    }
}

#[test]
fn phase_only_input_is_preserved_even_when_basis_probabilities_agree() {
    let mut before = tdg_component();
    phase(&mut before, x(), 1, 3);
    let mut after = before.clone();
    collapse_local_history(&mut after);
    assert!(after.output.history.is_empty());
    check_density(&before, &after);
    assert_eq!(
        after
            .phase
            .coefficient(&crate::symbolic::Monomial::variable(Variable::Input(q(0)))),
        PhaseCoefficient::rational(ratio(5, 24))
    );
}

#[test]
fn graph_native_history_elimination_has_no_path_count_admission_cap() {
    let mut c = h_component();
    c.path_support.extend(2..=128);
    collapse_local_history(&mut c);
    assert!(c.output.history.is_empty());
    assert_eq!(c.path_support.len(), 1);
    assert!(c.path_support.iter().all(|path| *path < 2));
}

#[test]
fn many_exact_phase_variants_preserve_complete_density_kernel() {
    for a in -2..=2 {
        for b in -2..=2 {
            for d in -2..=2 {
                let mut before = tdg_component();
                phase(&mut before, x().and(&p(0)), a, 8);
                phase(&mut before, p(1), b, 8);
                phase(&mut before, p(0).and(&p(1)), d, 8);
                let mut after = before.clone();
                collapse_local_history(&mut after);
                check_density(&before, &after);
            }
        }
    }
}
