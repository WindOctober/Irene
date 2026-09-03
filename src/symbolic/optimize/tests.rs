use num_bigint::BigInt;
use num_rational::BigRational;

use crate::symbolic::{
    BooleanPolynomial, Component, HistoryEntry, HybridMemory, PhaseCoefficient, PhasePolynomial,
    Scalar, Variable,
};

use super::merge_components;

fn rational(numerator: i64, denominator: i64) -> Scalar {
    Scalar::rational(BigRational::new(
        BigInt::from(numerator),
        BigInt::from(denominator),
    ))
}

fn component(scalar: Scalar, history: Vec<HistoryEntry>) -> Component {
    Component {
        guard: Vec::new(),
        scalar,
        path_support: Default::default(),
        phase: PhasePolynomial::zero(),
        output: HybridMemory {
            quantum: Default::default(),
            classical: Default::default(),
            history,
        },
    }
}

fn discard(value: bool) -> HistoryEntry {
    HistoryEntry::Discard {
        value: BooleanPolynomial::from(value),
    }
}

fn merge(components: Vec<Component>) -> Vec<Component> {
    merge_components(components)
}

#[test]
fn same_history_adds_amplitudes() {
    let history = vec![discard(false)];
    let result = merge(vec![
        component(rational(1, 3), history.clone()),
        component(rational(1, 6), history.clone()),
    ]);

    assert_eq!(result.len(), 1);
    assert_eq!(result[0].scalar, rational(1, 2));
    assert_eq!(result[0].output.history, history);
}

#[test]
fn opposite_amplitudes_in_the_same_history_cancel() {
    let history = vec![discard(false)];
    let result = merge(vec![
        component(Scalar::one(), history.clone()),
        component(Scalar::one().negate(), history),
    ]);

    assert!(result.is_empty());
}

#[test]
fn different_phases_in_the_same_history_remain_separate() {
    let history = vec![discard(false)];
    let plain = component(Scalar::one(), history.clone());
    let mut shifted = component(Scalar::one(), history);
    shifted.phase.add_boolean(
        &BooleanPolynomial::one(),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(2))),
    );

    let result = merge(vec![plain, shifted]);

    assert_eq!(result.len(), 2);
}

#[test]
fn coherent_merging_precedes_density_merging() {
    let result = merge(vec![
        component(rational(1, 2), vec![discard(false)]),
        component(rational(1, 2), vec![discard(false)]),
        component(rational(1, 2), vec![discard(true)]),
        component(rational(1, 2), vec![discard(true)]),
    ]);

    assert_eq!(result.len(), 1);
    assert_eq!(result[0].scalar, Scalar::sqrt(rational(2, 1)));
    assert!(result[0].output.history.is_empty());
}

#[test]
fn symbolic_histories_are_not_density_merged() {
    let value = BooleanPolynomial::variable(Variable::Path(0));
    let result = merge(vec![
        component(
            Scalar::one(),
            vec![HistoryEntry::Discard {
                value: value.clone(),
            }],
        ),
        component(
            Scalar::one(),
            vec![HistoryEntry::Discard {
                value: value.complement(),
            }],
        ),
    ]);

    assert_eq!(result.len(), 2);
}
