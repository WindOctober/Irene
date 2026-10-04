use num_bigint::BigInt;
use num_rational::BigRational;

use super::*;
use crate::ir::{ClassicalBit, Qubit, SymbolId};
use crate::symbolic::PhaseCoefficient;

pub(super) fn q(index: usize) -> Qubit {
    Qubit {
        register: SymbolId(0),
        index,
    }
}

pub(super) fn c(index: usize) -> ClassicalBit {
    ClassicalBit {
        register: SymbolId(1),
        index,
    }
}

pub(super) fn y(index: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(index))
}

pub(super) fn x(index: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Input(q(index)))
}

pub(super) fn component(paths: &[usize], output: BooleanPolynomial) -> Component {
    Component {
        guard: Vec::new(),
        scalar: Scalar::one(),
        path_support: paths.iter().copied().collect(),
        phase: PhasePolynomial::zero(),
        output: HybridMemory {
            quantum: BTreeMap::from([(q(0), output)]),
            classical: BTreeMap::new(),
            history: Vec::new(),
        },
    }
}

pub(super) fn hps(components: Vec<Component>) -> HybridPathSum {
    HybridPathSum {
        input: HybridMemory {
            quantum: BTreeMap::from([(q(0), x(0))]),
            classical: BTreeMap::new(),
            history: Vec::new(),
        },
        components,
    }
}

#[test]
fn ablation_keeps_vf2_alpha_matching() {
    crate::ablation::run(
        crate::ablation::Config::without(crate::ablation::Group::ALL),
        || {
            matches_bijective_path_alpha_renaming_and_component_order();
        },
    );
}

#[test]
fn matches_bijective_path_alpha_renaming_and_component_order() {
    let mut left_first = component(&[3, 8], y(3).xor(&y(8)));
    left_first.guard = vec![y(8).xor(&x(0)), y(3)];
    left_first.output.history = vec![HistoryEntry::Write {
        target: c(0),
        value: y(8),
    }];
    let left_second = component(&[21], y(21));

    let mut right_first = component(&[90, 11], y(90).xor(&y(11)));
    right_first.guard = vec![y(90), y(11).xor(&x(0))];
    right_first.output.history = vec![HistoryEntry::Write {
        target: c(0),
        value: y(11),
    }];
    let right_second = component(&[4], y(4));

    assert!(matches!(
        exact_match(
            &hps(vec![left_first, left_second]),
            &hps(vec![right_second, right_first]),
        ),
        ExactMatch::Match { .. }
    ));
}

#[test]
fn preserves_and_renames_scalar_phase_and_hidden_history() {
    let mut left = component(&[7], y(7));
    left.scalar = Scalar::Select {
        condition: y(7),
        when_true: Box::new(Scalar::one()),
        when_false: Box::new(Scalar::zero()),
    };
    left.phase.add_boolean(
        &y(7),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(8))),
    );
    left.output.history = vec![HistoryEntry::Discard { value: y(7) }];

    let mut right = component(&[42], y(42));
    right.scalar = Scalar::Select {
        condition: y(42),
        when_true: Box::new(Scalar::one()),
        when_false: Box::new(Scalar::zero()),
    };
    right.phase.add_boolean(
        &y(42),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(8))),
    );
    right.output.history = vec![HistoryEntry::Discard { value: y(42) }];

    assert!(matches!(
        exact_match(&hps(vec![left]), &hps(vec![right])),
        ExactMatch::Match { .. }
    ));
}

#[test]
fn rejects_different_path_counts_before_alpha_search() {
    let left = hps(vec![component(&[0, 1], y(0).xor(&y(1)))]);
    let right = hps(vec![component(&[2], y(2))]);

    assert_eq!(exact_match(&left, &right), ExactMatch::NoMatch);
}
