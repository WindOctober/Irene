use super::history_tests::density;
use super::*;
use crate::ir::{Qubit, SymbolId};
use crate::symbolic::{HybridMemory, PhasePolynomial};
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
fn fixture(history: Vec<BooleanPolynomial>, paths: &[usize]) -> Component {
    Component {
        guard: vec![],
        scalar: Scalar::rational(ratio(1, 2)),
        phase: PhasePolynomial::zero(),
        path_support: paths.iter().copied().collect(),
        output: HybridMemory {
            quantum: BTreeMap::from([(q(0), x(0)), (q(1), x(1))]),
            classical: BTreeMap::new(),
            history: history
                .into_iter()
                .map(|value| HistoryEntry::Discard { value })
                .collect(),
        },
    }
}
fn add_phase(c: &mut Component, value: &BooleanPolynomial, numerator: i64, denominator: i64) {
    c.phase.add_boolean(
        value,
        PhaseCoefficient::rational(ratio(numerator, denominator)),
    );
}
fn reduce_and_check(before: &Component) -> Component {
    let mut after = before.clone();
    assert!(reduce_path_sums(&mut after, true));
    assert_eq!(
        density(std::slice::from_ref(before)),
        density(std::slice::from_ref(&after))
    );
    after
}

#[test]
fn reset_hidden_sign_combines_orthogonal_weights_without_cancellation() {
    // H; Z; reset on an initially zero ancillary wire.
    let mut c = fixture(vec![y(0)], &[0]);
    c.scalar = Scalar::sqrt(Scalar::rational(ratio(1, 2)));
    c.output.quantum.insert(q(2), BooleanPolynomial::zero());
    add_phase(&mut c, &y(0), 1, 2);
    let after = reduce_and_check(&c);
    assert!(after.path_support.is_empty());
    assert!(after.output.history.is_empty());
    assert!(after.phase.selectors().next().is_none());
    let mut identity = fixture(vec![], &[]);
    identity.scalar = Scalar::rational(integer(1));
    identity
        .output
        .quantum
        .insert(q(2), BooleanPolynomial::zero());
    assert_eq!(density(&[after]), density(&[identity]));
}

#[test]
fn affine_history_phase_preserves_input_coherences() {
    let h = y(0).xor(&x(0));
    let mut c = fixture(vec![h.clone()], &[0]);
    add_phase(&mut c, &h, 1, 2);
    add_phase(&mut c, &x(1), 1, 8);
    let after = reduce_and_check(&c);
    assert!(after.path_support.is_empty());
    let mut expected = PhasePolynomial::zero();
    expected.add_boolean(&x(1), PhaseCoefficient::rational(ratio(1, 8)));
    assert_eq!(after.phase, expected);
}

#[test]
fn quadratic_history_phase_unblocks_both_hidden_paths() {
    let a = y(0).xor(&x(0));
    let b = y(1).xor(&x(1));
    let mut c = fixture(vec![a.clone(), b.clone()], &[0, 1]);
    add_phase(&mut c, &a.and(&b), 1, 2);
    let after = reduce_and_check(&c);
    assert!(after.path_support.is_empty());
    assert!(after.phase.selectors().next().is_none());
}

#[test]
fn visible_history_coupling_retains_dephasing() {
    let mut c = fixture(vec![y(0)], &[0]);
    add_phase(&mut c, &y(0), 1, 2);
    add_phase(&mut c, &y(0).and(&x(0)), 1, 2);
    let after = reduce_and_check(&c);
    assert!(!after.phase.selectors().next().is_none());
    assert!(after.path_support.contains(&0));
    let mut wrongly_cleared = after.clone();
    wrongly_cleared.phase = PhasePolynomial::zero();
    assert_ne!(density(&[after]), density(&[wrongly_cleared]));
}

#[test]
fn half_turn_collision_keeps_the_non_half_turn_coefficient() {
    let f = x(0).and(&x(1));
    let mut c = fixture(vec![y(0)], &[0]);
    add_phase(&mut c, &f.xor(&y(0)), 1, 2);
    add_phase(&mut c, &f, 1, 4);
    let after = reduce_and_check(&c);
    let mut expected = PhasePolynomial::zero();
    expected.add_boolean(&f, PhaseCoefficient::rational(ratio(3, 4)));
    assert_eq!(after.phase, expected);
    assert!(after.path_support.is_empty());
}

#[test]
fn coherent_mode_preserves_history_relative_amplitudes() {
    let mut c = fixture(vec![y(0)], &[0]);
    add_phase(&mut c, &y(0), 1, 2);
    let before = super::tests::vector(&c);
    assert!(reduce_path_sums(&mut c, false));
    assert_eq!(before, super::tests::vector(&c));
    assert!(c.path_support.contains(&0));
    assert!(!c.phase.selectors().next().is_none());
}

#[test]
fn sibling_components_do_not_receive_independent_history_phase_changes() {
    let mut a = fixture(vec![y(0)], &[0]);
    add_phase(&mut a, &y(0), 1, 2);
    let b = fixture(vec![y(0)], &[0]);
    let before = density(&[a.clone(), b.clone()]);
    let hps = crate::symbolic::HybridPathSum {
        input: Default::default(),
        components: vec![a, b],
    };
    let hps = super::super::simplify::simplify(hps);
    assert_eq!(before, density(&hps.components));
}

#[test]
fn large_history_still_allows_linear_phase_cleanup() {
    let mut c = fixture(vec![y(0); 65], &[0]);
    add_phase(&mut c, &y(0), 1, 2);
    let after = reduce_and_check(&c);
    assert!(after.phase.selectors().next().is_none());
    assert!(after.path_support.is_empty());
}

#[test]
fn nonaffine_history_is_conservatively_left_unchanged() {
    let h = y(0).and(&x(0));
    let mut c = fixture(vec![h.clone()], &[0]);
    add_phase(&mut c, &h, 1, 2);
    let after = reduce_and_check(&c);
    assert_eq!(after.phase, c.phase);
    assert!(after.path_support.contains(&0));
}
