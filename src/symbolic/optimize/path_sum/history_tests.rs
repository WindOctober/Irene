use super::tests::{Eighth, multiply, vector, zero};
use super::*;
use crate::ir::{ClassicalBit, Qubit, SymbolId};
use crate::symbolic::{HybridMemory, HybridPathSum, PhasePolynomial};
use std::collections::BTreeMap;

fn q(i: usize) -> Qubit {
    Qubit {
        register: SymbolId(0),
        index: i,
    }
}
fn x(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Input(q(i)))
}
fn y(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(i))
}
fn bit() -> ClassicalBit {
    ClassicalBit {
        register: SymbolId(1),
        index: 0,
    }
}
fn discard(value: BooleanPolynomial) -> HistoryEntry {
    HistoryEntry::Discard { value }
}
fn fixture() -> Component {
    let mut phase = PhasePolynomial::zero();
    phase.add_boolean(&x(1), PhaseCoefficient::rational(ratio(1, 8)));
    Component {
        guard: vec![],
        scalar: Scalar::select(
            x(0),
            Scalar::rational(ratio(-1, 3)),
            Scalar::rational(ratio(2, 3)),
        ),
        path_support: [0].into(),
        phase,
        output: HybridMemory {
            quantum: BTreeMap::from([(q(0), x(0)), (q(1), x(1))]),
            classical: BTreeMap::new(),
            history: vec![discard(y(0))],
        },
    }
}
fn conjugate(a: &Eighth) -> Eighth {
    [a[0].clone(), -a[3].clone(), -a[2].clone(), -a[1].clone()]
}

// Exact reduced density map, including independent ket/bra inputs and
// cross-component terms. Compare maps, not only diagonal probabilities.
type Density = BTreeMap<(usize, usize, Vec<bool>, Vec<bool>), Eighth>;
fn density(components: &[Component]) -> Density {
    let mut amplitudes = Vec::new();
    for component in components {
        let quantum = component.output.quantum.len();
        let classical = component.output.classical.len();
        for ((input, signature), amplitude) in vector(component) {
            let visible = signature[..quantum + classical].to_vec();
            let classical = signature[quantum..quantum + classical].to_vec();
            let history = signature[visible.len()..].to_vec();
            amplitudes.push((input, visible, classical, history, amplitude));
        }
    }
    let mut result = Density::new();
    for (ket_input, ket, ket_classical, ket_history, a) in &amplitudes {
        for (bra_input, bra, bra_classical, bra_history, b) in &amplitudes {
            if ket_classical != bra_classical || ket_history != bra_history {
                continue;
            }
            let product = multiply(a, &conjugate(b));
            let entry = result
                .entry((*ket_input, *bra_input, ket.clone(), bra.clone()))
                .or_insert_with(zero);
            for (r, v) in entry.iter_mut().zip(product) {
                *r += v;
            }
        }
    }
    result.retain(|_, value| value.iter().any(|r| *r != integer(0)));
    result
}

#[test]
fn singleton_history_removal_preserves_the_full_density_map() {
    for offset in [
        BooleanPolynomial::zero(),
        x(0),
        x(0).xor(&x(1)),
        x(0).and(&x(1)),
    ] {
        for write in [false, true] {
            let mut c = fixture();
            let value = y(0).xor(&offset);
            c.output.history = vec![if write {
                HistoryEntry::Write {
                    target: bit(),
                    value,
                }
            } else {
                discard(value)
            }];
            let before = density(&[c.clone()]);
            let reduced = super::super::simplify(HybridPathSum {
                input: HybridMemory::default(),
                components: vec![c],
            });
            assert_eq!(reduced.components.len(), 1);
            assert!(reduced.components[0].path_support.is_empty());
            assert!(reduced.components[0].output.history.is_empty());
            assert_eq!(density(&reduced.components), before);
        }
    }
}

#[test]
fn history_row_operations_retain_residual_dephasing() {
    let mut c = fixture();
    c.output.history = vec![discard(y(0).xor(&x(0))), discard(y(0).xor(&x(1)))];
    let before = density(&[c.clone()]);
    assert!(reduce_path_sums(&mut c, true));
    assert!(c.path_support.is_empty());
    assert_eq!(c.output.history.len(), 1);
    assert_eq!(density(&[c.clone()]), before);
    // Removing the residual history would restore forbidden input coherence.
    c.output.history.clear();
    assert_ne!(density(&[c]), before);
}

#[test]
fn one_noninjective_history_row_blocks_the_pivot() {
    for histories in [
        vec![discard(y(0).and(&x(0)))],
        vec![discard(y(0)), discard(y(0).and(&x(0)))],
    ] {
        let mut c = fixture();
        c.output.history = histories;
        let before = c.clone();
        assert!(!reduce_path(&mut c, &Variable::Path(0), true));
        assert_eq!(c, before);
    }
}

#[test]
fn guard_scalar_phase_and_visible_dependencies_block_history_elimination() {
    for field in 0..5 {
        let mut c = fixture();
        match field {
            0 => c.guard.push(y(0).and(&x(0))),
            1 => c.scalar = Scalar::select(y(0), Scalar::one(), Scalar::zero()),
            2 => c
                .phase
                .add_boolean(&y(0).and(&x(0)), PhaseCoefficient::rational(ratio(1, 8))),
            3 => {
                c.output.quantum.insert(q(0), y(0));
            }
            4 => {
                c.output.classical.insert(bit(), y(0));
            }
            _ => unreachable!(),
        }
        let before = c.clone();
        assert!(!reduce_path(&mut c, &Variable::Path(0), true));
        assert_eq!(c, before);
    }
}

#[test]
fn multiple_components_keep_their_history_separation() {
    let mut left = fixture();
    left.output.history = vec![discard(BooleanPolynomial::zero()), discard(y(0))];
    left.output.quantum.insert(q(0), BooleanPolynomial::zero());
    let mut right = fixture();
    right.path_support = [1].into();
    right.output.history = vec![discard(BooleanPolynomial::one()), discard(y(1))];
    right.output.quantum.insert(q(0), BooleanPolynomial::one());
    let originals = vec![left, right];
    let before = density(&originals);
    let reduced = super::super::simplify(HybridPathSum {
        input: HybridMemory::default(),
        components: originals.clone(),
    });
    assert_eq!(reduced.components.len(), 2);
    for (old, new) in originals.iter().zip(&reduced.components) {
        assert_eq!(new.path_support, old.path_support);
        assert_eq!(new.output.history, old.output.history);
    }
    assert_eq!(density(&reduced.components), before);
}

#[test]
fn explicit_coherent_mode_never_removes_a_history_pivot() {
    let mut c = fixture();
    let before = c.clone();
    assert!(reduce_path_sums(&mut c, false));
    assert_eq!(c.output.history, before.output.history);
    assert_eq!(c.path_support, before.path_support);
    assert_eq!(density(&[c]), density(&[before]));
}

#[test]
fn history_elimination_can_unblock_omega_in_a_later_round() {
    let mut c = fixture();
    c.path_support = [0, 1].into();
    c.output.history = vec![discard(y(0).xor(&y(1)))];
    c.phase
        .add_boolean(&y(1), PhaseCoefficient::rational(ratio(1, 4)));
    let before = density(&[c.clone()]);
    assert!(reduce_path_sums(&mut c, true));
    assert!(c.path_support.is_empty());
    assert!(c.output.history.is_empty());
    assert_eq!(density(&[c]), before);
}
