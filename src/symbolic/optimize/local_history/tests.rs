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

#[test]
fn coordinate_change_reindexes_every_semantic_field_bijectively() {
    use std::convert::Infallible;
    let mut before = h_component();
    let history = p(0).xor(&x());
    before.output.history = vec![HistoryEntry::Discard {
        value: history.clone(),
    }];
    before.output.classical.insert(
        ClassicalBit {
            register: SymbolId(1),
            index: 0,
        },
        p(0).xor(&p(1)).xor(&x()),
    );
    before.guard.push(p(0).and(&p(1)));
    before.scalar = Scalar::select(
        p(0),
        Scalar::rational(ratio(3, 5)),
        Scalar::rational(ratio(2, 5)),
    );
    phase(&mut before, p(0).and(&p(1)), 1, 7);
    let mut after = before.clone();
    coordinate(&mut after, &history, &mut BTreeSet::new());
    assert_eq!(before.path_support, after.path_support);
    for input in [false, true] {
        for bits in 0..4 {
            let old_y = bits & 1 != 0;
            let mut old = ScalarBindings::default();
            old.booleans.insert(Variable::Input(q(0)), input);
            old.booleans.insert(Variable::Path(0), old_y);
            old.booleans.insert(Variable::Path(1), bits & 2 != 0);
            let mut new = old.clone();
            new.booleans.insert(Variable::Path(0), old_y ^ input);
            let fields = |c: &Component, bindings: &ScalarBindings| {
                c.guard
                    .iter()
                    .chain(c.output.quantum.values())
                    .chain(c.output.classical.values())
                    .chain(c.output.history.iter().map(HistoryEntry::value))
                    .map(|p| {
                        p.evaluate::<Infallible>(|v| Ok(bindings.booleans[v]))
                            .unwrap()
                    })
                    .collect::<Vec<_>>()
            };
            assert_eq!(fields(&before, &old), fields(&after, &new));
            let phase_value = |c: &Component, bindings: &ScalarBindings| {
                c.phase
                    .selectors()
                    .filter(|(p, _)| {
                        p.evaluate::<Infallible>(|v| Ok(bindings.booleans[v]))
                            .unwrap()
                    })
                    .map(|(_, c)| c.as_rational().unwrap())
                    .sum::<BigRational>()
            };
            assert!((phase_value(&before, &old) - phase_value(&after, &new)).is_integer());
            let a = before.scalar.evaluate(128, &old).unwrap().to_f64();
            let b = after.scalar.evaluate(128, &new).unwrap().to_f64();
            assert!((a - b).abs() < 1e-12);
        }
    }
}

#[test]
fn final_execution_contracts_hidden_outcome_correction() {
    use crate::symbolic::{ExecutionConfig, OutputSelection, execute};
    let program = crate::frontend::openqasm3::parse_str(
        "OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q;
         h q[1]; cz q[0], q[1]; h q[0]; cx q[0], q[1]; reset q[0];",
        "history-coordinate.qasm",
    )
    .unwrap();
    let register = program.quantum_registers[0].id;
    let input = Qubit { register, index: 0 };
    let output = Qubit { register, index: 1 };
    let result = execute(
        &program,
        &ExecutionConfig::with_symbolic_inputs([input.clone()]),
        &OutputSelection::new([output.clone()], []),
    )
    .unwrap();
    assert_eq!(result.components.len(), 1);
    let mut actual = result.components[0].clone();
    assert!(actual.output.history.is_empty());
    substitute_component(&mut actual, &Variable::Input(input), &x());
    let value = actual.output.quantum.remove(&output).unwrap();
    actual.output.quantum.insert(q(1), value);
    let mut expected = Component {
        guard: vec![],
        scalar: Scalar::sqrt(Scalar::rational(ratio(1, 2))),
        path_support: BTreeSet::from([0]),
        phase: PhasePolynomial::zero(),
        output: HybridMemory {
            quantum: BTreeMap::from([(q(1), p(0))]),
            classical: BTreeMap::new(),
            history: vec![],
        },
    };
    phase(&mut expected, x().and(&p(0)), 1, 2);
    check_density(&expected, &actual);
}
