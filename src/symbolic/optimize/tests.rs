use num_bigint::BigInt;
use num_rational::BigRational;

use crate::ir::{Qubit, SymbolId};
use crate::symbolic::{
    BooleanPolynomial, Component, HistoryEntry, HybridMemory, HybridPathSum, PhaseCoefficient,
    PhasePolynomial, Scalar, Variable,
};

use super::{merge_components, simplify};

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

#[test]
fn fourier_uses_factored_cofactors_and_keeps_the_zero_cofactor_phase() {
    let input = |i| {
        BooleanPolynomial::variable(Variable::Input(Qubit {
            register: SymbolId(0),
            index: i,
        }))
    };
    let f = (0..7).fold(BooleanPolynomial::one(), |p, i| {
        p.and(&input(i).complement())
    });
    let y = BooleanPolynomial::variable(Variable::Path(0));
    let z = input(7);
    let mut c = component(Scalar::one(), Vec::new());
    c.path_support.insert(0);
    c.phase.add_boolean(
        &y.and(&f).xor(&z),
        PhaseCoefficient::rational(BigRational::new(1.into(), 2.into())),
    );
    assert!(super::reduce_path_sums(&mut c, false));
    assert!(c.path_support.is_empty());
    assert_eq!(c.scalar, rational(2, 1));
    for bits in 0..256 {
        let eval = |p: &BooleanPolynomial| {
            p.evaluate::<std::convert::Infallible>(|v| match v {
                Variable::Input(q) => Ok(bits & (1 << q.index) != 0),
                _ => panic!("eliminated path leaked into the result"),
            })
            .unwrap()
        };
        let expected = if eval(&f) {
            0
        } else if eval(&z) {
            -2
        } else {
            2
        };
        let phase_sign = c.phase.selectors().fold(false, |sign, (p, coefficient)| {
            assert_eq!(
                coefficient.as_rational(),
                Some(BigRational::new(1.into(), 2.into()))
            );
            sign ^ eval(&p)
        });
        let actual = if c.guard.iter().any(eval) {
            0
        } else if phase_sign {
            -2
        } else {
            2
        };
        assert_eq!(actual, expected);
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

#[test]
fn vacuous_path_sum_contributes_a_factor_of_two() {
    let mut value = component(Scalar::one(), Vec::new());
    value.path_support.insert(0);

    let result = simplify(HybridPathSum {
        input: HybridMemory::default(),
        components: vec![value],
    });

    assert_eq!(result.components.len(), 1);
    assert!(result.components[0].path_support.is_empty());
    assert_eq!(result.components[0].scalar, rational(2, 1));
}

#[test]
fn contradictory_fourier_path_sum_cancels() {
    let mut value = component(Scalar::one(), Vec::new());
    value.path_support.insert(0);
    value.phase.add_boolean(
        &BooleanPolynomial::variable(Variable::Path(0)),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(2))),
    );

    let result = simplify(HybridPathSum {
        input: HybridMemory::default(),
        components: vec![value],
    });

    assert!(result.components.is_empty());
}

#[test]
fn positive_omega_path_sum_has_closed_form() {
    let mut value = component(Scalar::one(), Vec::new());
    value.path_support.insert(0);
    value.phase.add_boolean(
        &BooleanPolynomial::variable(Variable::Path(0)),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(4))),
    );

    let result = simplify(HybridPathSum {
        input: HybridMemory::default(),
        components: vec![value],
    });

    assert_eq!(result.components.len(), 1);
    let value = &result.components[0];
    assert!(value.path_support.is_empty());
    assert_eq!(value.scalar, Scalar::sqrt(rational(2, 1)));
    assert_eq!(
        value.phase.coefficient(&crate::symbolic::Monomial::one()),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(8)))
    );
}

#[test]
fn negative_omega_path_sum_has_closed_form() {
    let mut value = component(Scalar::one(), Vec::new());
    value.path_support.insert(0);
    value.phase.add_boolean(
        &BooleanPolynomial::variable(Variable::Path(0)),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(3), BigInt::from(4))),
    );

    let result = simplify(HybridPathSum {
        input: HybridMemory::default(),
        components: vec![value],
    });

    let value = &result.components[0];
    assert!(value.path_support.is_empty());
    assert_eq!(value.scalar, Scalar::sqrt(rational(2, 1)));
    assert_eq!(
        value.phase.coefficient(&crate::symbolic::Monomial::one()),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(7), BigInt::from(8)))
    );
}

#[test]
fn path_reduction_canonicalizes_nested_normalization_factors() {
    let root_half = Scalar::sqrt(rational(1, 2));
    let scalar = rational(2, 1).multiply(
        rational(2, 1).multiply(rational(1, 2).multiply(root_half.clone().multiply(root_half))),
    );
    let value = component(scalar, Vec::new());

    let result = simplify(HybridPathSum {
        input: HybridMemory::default(),
        components: vec![value],
    });

    assert_eq!(result.components[0].scalar, Scalar::one());
}

#[test]
fn affine_hidden_history_eliminates_its_path_as_orthogonal_worlds() {
    let input = Variable::Input(crate::ir::Qubit {
        register: crate::ir::SymbolId(0),
        index: 0,
    });
    let path = Variable::Path(0);
    let mut value = component(
        Scalar::one(),
        vec![HistoryEntry::Discard {
            value: BooleanPolynomial::variable(input)
                .xor(&BooleanPolynomial::variable(path.clone())),
        }],
    );
    value.path_support.insert(0);

    let result = simplify(HybridPathSum {
        input: HybridMemory::default(),
        components: vec![value],
    });

    assert_eq!(result.components.len(), 1);
    assert!(result.components[0].path_support.is_empty());
    assert!(result.components[0].output.history.is_empty());
    assert_eq!(result.components[0].scalar, Scalar::sqrt(rational(2, 1)));
}

#[test]
fn affine_history_row_reduction_retains_only_the_residual_relation() {
    let left = BooleanPolynomial::variable(Variable::Input(crate::ir::Qubit {
        register: crate::ir::SymbolId(0),
        index: 0,
    }));
    let right = BooleanPolynomial::variable(Variable::Input(crate::ir::Qubit {
        register: crate::ir::SymbolId(0),
        index: 1,
    }));
    let path = BooleanPolynomial::variable(Variable::Path(0));
    let mut value = component(
        Scalar::one(),
        vec![
            HistoryEntry::Discard {
                value: path.xor(&left),
            },
            HistoryEntry::Discard {
                value: path.xor(&right),
            },
        ],
    );
    value.path_support.insert(0);

    let result = simplify(HybridPathSum {
        input: HybridMemory::default(),
        components: vec![value],
    });

    assert_eq!(result.components.len(), 1);
    assert!(result.components[0].path_support.is_empty());
    assert_eq!(
        result.components[0].output.history,
        vec![HistoryEntry::Discard {
            value: left.xor(&right),
        }]
    );
    assert_eq!(result.components[0].scalar, Scalar::sqrt(rational(2, 1)));
}

#[test]
fn noninjective_hidden_history_keeps_its_path() {
    let input = BooleanPolynomial::variable(Variable::Input(crate::ir::Qubit {
        register: crate::ir::SymbolId(0),
        index: 0,
    }));
    let path = BooleanPolynomial::variable(Variable::Path(0));
    let mut value = component(
        Scalar::one(),
        vec![HistoryEntry::Discard {
            value: input.and(&path),
        }],
    );
    value.path_support.insert(0);

    let result = simplify(HybridPathSum {
        input: HybridMemory::default(),
        components: vec![value],
    });

    assert_eq!(result.components[0].path_support, [0].into());
    assert_eq!(result.components[0].output.history.len(), 1);
}

#[test]
fn phase_dependent_hidden_history_keeps_its_path() {
    let path = BooleanPolynomial::variable(Variable::Path(0));
    let input = BooleanPolynomial::variable(Variable::Input(crate::ir::Qubit {
        register: crate::ir::SymbolId(0),
        index: 0,
    }));
    let mut value = component(
        Scalar::one(),
        vec![HistoryEntry::Discard {
            value: path.clone(),
        }],
    );
    value.path_support.insert(0);
    value.phase.add_boolean(
        &path.and(&input),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(2))),
    );

    let result = simplify(HybridPathSum {
        input: HybridMemory::default(),
        components: vec![value],
    });

    assert_eq!(result.components[0].path_support, [0].into());
    assert_eq!(result.components[0].output.history.len(), 1);
}

#[test]
fn history_phase_blocked_paths_are_reconsidered_after_a_rewrite() {
    let x = BooleanPolynomial::variable(Variable::Path(0));
    let y = BooleanPolynomial::variable(Variable::Path(1));
    let mut value = component(
        Scalar::one(),
        vec![HistoryEntry::Discard { value: x.xor(&y) }],
    );
    value.path_support.extend([0, 1]);
    value.phase.add_boolean(
        &y,
        PhaseCoefficient::rational(BigRational::new(1.into(), 4.into())),
    );
    // y is scanned first and is blocked by both phase and history. History
    // elimination of x then removes that history; the next round must revisit
    // y and apply Omega. A once-for-the-whole-pass cache would miss it.
    assert!(super::reduce_path_sums(&mut value, true));
    assert!(value.path_support.is_empty());
    assert!(value.output.history.is_empty());
    assert_eq!(value.scalar, rational(2, 1));
    let mut expected = PhasePolynomial::zero();
    expected.add_boolean(
        &BooleanPolynomial::one(),
        PhaseCoefficient::rational(BigRational::new(1.into(), 8.into())),
    );
    assert_eq!(value.phase, expected);
}

#[test]
fn phase_over_hidden_history_is_removed_before_path_elimination() {
    let first = BooleanPolynomial::variable(Variable::Path(0));
    let second = BooleanPolynomial::variable(Variable::Path(1));
    let mut value = component(
        Scalar::one(),
        vec![
            HistoryEntry::Discard {
                value: first.clone(),
            },
            HistoryEntry::Discard {
                value: second.clone(),
            },
        ],
    );
    value.path_support.extend([0, 1]);
    value.phase.add_boolean(
        &first.and(&second),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(2))),
    );

    let result = simplify(HybridPathSum {
        input: HybridMemory::default(),
        components: vec![value],
    });

    let result = &result.components[0];
    assert!(result.path_support.is_empty());
    assert!(result.output.history.is_empty());
    assert_eq!(result.phase, PhasePolynomial::zero());
    assert_eq!(result.scalar, rational(2, 1));
}

#[test]
fn hidden_history_is_not_collapsed_across_sibling_components() {
    let path = BooleanPolynomial::variable(Variable::Path(0));
    let mut hidden_worlds = component(Scalar::one(), vec![HistoryEntry::Discard { value: path }]);
    hidden_worlds.path_support.insert(0);
    let sibling = component(Scalar::one(), Vec::new());

    let result = simplify(HybridPathSum {
        input: HybridMemory::default(),
        components: vec![hidden_worlds, sibling],
    });

    assert_eq!(result.components.len(), 2);
    assert_eq!(result.components[0].path_support, [0].into());
    assert_eq!(result.components[0].output.history.len(), 1);
}

#[test]
fn orthogonal_worlds_add_unequal_density_weights_and_ignore_global_phase() {
    let mut first = component(Scalar::sqrt(rational(3, 4)), Vec::new());
    let mut second = component(rational(1, 2), vec![discard(true)]);
    second.phase.add_boolean(
        &BooleanPolynomial::one(),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(2))),
    );
    first.output.quantum.clear();

    let result = merge(vec![first, second]);

    assert_eq!(result.len(), 1);
    assert_eq!(result[0].scalar, Scalar::one());
    assert_eq!(result[0].phase, PhasePolynomial::zero());
    assert!(result[0].output.history.is_empty());
}

#[test]
fn density_merge_retains_history_shared_by_orthogonal_worlds() {
    let shared = BooleanPolynomial::variable(Variable::Path(0));
    let mut first = component(
        rational(1, 2),
        vec![
            HistoryEntry::Discard {
                value: shared.clone(),
            },
            discard(false),
        ],
    );
    let mut second = component(
        rational(1, 2),
        vec![
            HistoryEntry::Discard {
                value: shared.clone(),
            },
            discard(true),
        ],
    );
    first.path_support.insert(0);
    second.path_support.insert(0);

    let result = merge(vec![first, second]);

    assert_eq!(result.len(), 1);
    assert_eq!(
        result[0].output.history,
        vec![HistoryEntry::Discard { value: shared }]
    );
}

#[test]
fn density_merge_preserves_unequal_boolean_dependent_amplitudes() {
    let condition = BooleanPolynomial::variable(Variable::Path(0));
    let mut first = component(
        Scalar::select(condition.clone(), Scalar::one(), rational(-1, 1)),
        vec![discard(false)],
    );
    let mut second = component(
        Scalar::select(condition, rational(-1, 1), Scalar::one()),
        vec![discard(true)],
    );
    first.path_support.insert(0);
    second.path_support.insert(0);

    let result = merge(vec![first, second]);

    // sqrt(s_0(y)^2+s_1(y)^2) would erase the signed amplitude profiles and
    // introduce ket/bra coherence that the two histories do not possess.
    assert_eq!(result.len(), 2);
    assert!(result.iter().all(|value| value.output.history.len() == 1));
}

#[test]
fn density_merge_does_not_restore_coherence_between_visible_groups() {
    let output = Qubit {
        register: SymbolId(0),
        index: 0,
    };
    let mut components = Vec::new();
    for (value, histories) in [
        (false, [[false, false], [true, true]]),
        (true, [[false, true], [true, false]]),
    ] {
        for history in histories {
            let mut component =
                component(rational(1, 2), history.into_iter().map(discard).collect());
            component
                .output
                .quantum
                .insert(output.clone(), BooleanPolynomial::from(value));
            components.push(component);
        }
    }

    let result = merge(components);

    // Collapsing each output group independently would erase all histories;
    // the two representatives would then spuriously form |0><1| cross terms.
    assert_eq!(result.len(), 4);
    assert!(result.iter().all(|value| value.output.history.len() == 2));
}
