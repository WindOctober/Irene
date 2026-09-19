use super::*;
use crate::ir::{Qubit, SymbolId};
use crate::symbolic::{
    BooleanPolynomial as B, HybridMemory, PhaseCoefficient, PhasePolynomial, Scalar, Variable,
};
use num_rational::BigRational;

fn checked_merge(components: Vec<Component>, retired: &[ClassicalBit]) -> Vec<Component> {
    let result = merge_feedback_groups(components.clone(), retired);
    super::super::merge::tests::assert_density(&components, &result);
    result
}

fn bit() -> ClassicalBit {
    ClassicalBit {
        register: SymbolId(1),
        index: 0,
    }
}
fn q() -> Qubit {
    Qubit {
        register: SymbolId(0),
        index: 0,
    }
}
fn ratio(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}
fn branch(outcome: bool, path: usize) -> Component {
    let y = B::variable(Variable::Path(path));
    let x = B::variable(Variable::Input(q()));
    let mut phase = PhasePolynomial::zero();
    phase.add_boolean(&x.and(&y), PhaseCoefficient::rational(ratio(1, 2)));
    Component {
        guard: vec![],
        scalar: Scalar::rational(ratio(1, 2)),
        path_support: [path].into(),
        phase,
        output: HybridMemory {
            quantum: [(q(), y)].into(),
            classical: BTreeMap::new(),
            history: vec![
                HistoryEntry::Discard { value: B::zero() },
                HistoryEntry::Write {
                    target: bit(),
                    value: B::from(outcome),
                },
            ],
        },
    }
}

#[test]
fn local_group_merges_with_an_unrelated_component_present() {
    let a = branch(false, 7);
    let mut b = branch(true, 25);
    b.phase
        .add_boolean(&B::one(), PhaseCoefficient::rational(ratio(1, 7)));
    let mut outside = branch(false, 40);
    outside.output.history[0] = HistoryEntry::Discard { value: B::one() };
    outside.phase = PhasePolynomial::zero(); // Different operator: cannot globally merge.
    let result = checked_merge(vec![a, outside.clone(), b], &[bit()]);
    assert_eq!(result.len(), 2);
    assert!(result.contains(&outside));
    assert_eq!(
        result[0].scalar,
        Scalar::rational(ratio(1, 2)).multiply(Scalar::sqrt(Scalar::rational(ratio(2, 1))))
    );
}

#[test]
fn unequal_global_weights_add_as_density_not_amplitude() {
    let a = branch(false, 7);
    let mut b = branch(true, 25);
    b.scalar = Scalar::rational(ratio(1, 3));
    let result = checked_merge(vec![a, b], &[bit()]);
    assert_eq!(result.len(), 1);
    assert_eq!(
        result[0].scalar,
        Scalar::sqrt(Scalar::rational(ratio(13, 36)))
    );
}

#[test]
fn relative_input_phase_wrong_output_and_live_control_refuse() {
    for kind in 0..3 {
        let a = branch(false, 7);
        let mut b = branch(true, 25);
        match kind {
            0 => b.phase.add_boolean(
                &B::variable(Variable::Input(q())),
                PhaseCoefficient::rational(ratio(1, 2)),
            ),
            1 => {
                b.output.quantum.insert(q(), B::zero());
            }
            _ => {
                b.output.classical.insert(bit(), B::one());
            }
        }
        let original = vec![a, b];
        assert_eq!(checked_merge(original.clone(), &[bit()]), original);
    }
}

#[test]
fn potentially_coherent_outsider_blocks_local_density_compression() {
    let mut outside = branch(false, 40);
    outside.output.history[0] = HistoryEntry::Discard {
        value: B::variable(Variable::Input(q())),
    };
    let original = vec![branch(false, 7), branch(true, 25), outside];
    assert_eq!(checked_merge(original.clone(), &[bit()]), original);
}

#[test]
fn two_local_groups_can_merge_without_becoming_one_global_component() {
    let mut c = branch(false, 40);
    let mut d = branch(true, 50);
    for component in [&mut c, &mut d] {
        component.output.history[0] = HistoryEntry::Discard { value: B::one() };
        component.phase = PhasePolynomial::zero();
    }
    let result = checked_merge(vec![branch(false, 7), branch(true, 25), c, d], &[bit()]);
    assert_eq!(result.len(), 2);
    assert!(histories_are_orthogonal(
        &result[0].output.history,
        &result[1].output.history
    ));
}

#[test]
fn compression_refuses_new_overlap_without_a_shared_label() {
    let mut a = branch(false, 7);
    let mut b = branch(true, 25);
    a.output.history.remove(0);
    b.output.history.remove(0);
    let mut outside = branch(false, 40);
    outside.output.history.clear();
    outside.phase = PhasePolynomial::zero();
    let original = vec![a, b, outside];
    assert_eq!(checked_merge(original.clone(), &[bit()]), original);
}

#[test]
fn shared_constant_label_preserves_outsider_isolation() {
    let mut outside = branch(false, 40);
    outside.output.history.clear();
    outside.phase = PhasePolynomial::zero();
    let result = checked_merge(vec![branch(false, 7), branch(true, 25), outside], &[bit()]);
    assert_eq!(result.len(), 2);
    assert!(histories_are_orthogonal(
        &result[0].output.history,
        &result[1].output.history
    ));
}

#[test]
fn repeated_target_keeps_the_earlier_symbolic_record() {
    let mut a = branch(false, 7);
    let mut b = branch(true, 25);
    for component in [&mut a, &mut b] {
        component.output.history[0] = HistoryEntry::Write {
            target: bit(),
            value: B::variable(Variable::Input(q())),
        };
    }
    let result = checked_merge(vec![a, b], &[bit()]);
    assert_eq!(result.len(), 1);
}

#[test]
fn nonorthogonal_outcomes_are_not_density_merged() {
    let original = vec![branch(false, 7), branch(false, 25)];
    assert_eq!(checked_merge(original.clone(), &[bit()]), original);
}
