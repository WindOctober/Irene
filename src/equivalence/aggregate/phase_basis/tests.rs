use super::*;
use crate::symbolic::PhaseCoefficient;

fn bit(v: &KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v.clone())
}

#[test]
fn completed_reduction_components_keep_common_weight_phase_guards_and_ownership() {
    let a = KernelVariable::PathKet { term: 0, path: 0 };
    let b = KernelVariable::PathBra { term: 1, path: 0 };
    let free = KernelVariable::InputBra(0);
    let mut source = WorkingTerm {
        paths: BTreeSet::from([a.clone(), b.clone()]),
        constraints: vec![bit(&KernelVariable::InputKet(0))],
        coefficient: KernelScalar::Rational(integer(3)),
        phase: KernelPhasePolynomial::default(),
    };
    for path in [&a, &b] {
        source.phase.add_boolean(
            &bit(path).and(&bit(&free)),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    source
        .phase
        .add_boolean(&bit(&free), PhaseCoefficient::rational(ratio(1, 4)));
    let compare = |left: WorkingTerm, right: WorkingTerm| {
        matches_reduced_components(
            &Reduction::Sum(Box::new(left)),
            &Reduction::Sum(Box::new(right)),
            &mut 0,
        )
    };
    assert!(compare(source.clone(), source.clone()));
    let mut renamed = source.clone();
    let fresh = KernelVariable::PathKet { term: 12, path: 9 };
    renamed.paths.remove(&a);
    renamed.paths.insert(fresh.clone());
    renamed
        .phase
        .rename_variables(&BTreeMap::from([(a.clone(), fresh)]));
    assert!(compare(source.clone(), renamed));
    let mut changed = source.clone();
    changed.coefficient = KernelScalar::Rational(integer(4));
    assert!(!compare(source.clone(), changed));
    let mut changed = source.clone();
    changed.constraints[0] = changed.constraints[0].complement();
    assert!(!compare(source.clone(), changed));
    let mut changed = source.clone();
    changed
        .phase
        .add_boolean(&bit(&free), PhaseCoefficient::rational(ratio(1, 4)));
    assert!(!compare(source.clone(), changed));
    let mut malformed = source.clone();
    malformed.paths.remove(&a);
    assert!(!compare(source.clone(), malformed));
    assert!(!matches_reduced_components(
        &Reduction::Residual,
        &Reduction::Sum(Box::new(source)),
        &mut 0,
    ));
}

#[test]
fn completed_reduction_factorization_keeps_the_eight_binder_local_gate() {
    let paths = (0..10)
        .map(|path| KernelVariable::PathKet { term: 0, path })
        .collect::<Vec<_>>();
    let mut source = WorkingTerm {
        paths: paths.iter().cloned().collect(),
        constraints: Vec::new(),
        coefficient: KernelScalar::Rational(integer(1)),
        phase: KernelPhasePolynomial::default(),
    };
    source.phase.add_term(
        KernelMonomial::from_variables(paths[..9].iter().cloned()),
        PhaseCoefficient::rational(ratio(1, 8)),
    );
    source
        .phase
        .add_boolean(&bit(&paths[9]), PhaseCoefficient::rational(ratio(1, 8)));
    assert!(!matches_reduced_components(
        &Reduction::Sum(Box::new(source.clone())),
        &Reduction::Sum(Box::new(source)),
        &mut 0,
    ));
}

fn fixture() -> WorkingTerm {
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathBra { term: 0, path: 0 };
    let z = KernelVariable::PathKet { term: 0, path: 1 };
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(
        &bit(&x).xor(&bit(&y)),
        PhaseCoefficient::rational(ratio(1, 8)),
    );
    phase.add_boolean(&bit(&z), PhaseCoefficient::rational(ratio(1, 8)));
    WorkingTerm {
        paths: BTreeSet::from([x, y, z]),
        constraints: vec![bit(&KernelVariable::InputKet(0))],
        coefficient: KernelScalar::Select {
            condition: bit(&KernelVariable::InputBra(0)),
            when_true: Box::new(KernelScalar::Rational(integer(3))),
            when_false: Box::new(KernelScalar::Rational(integer(-2))),
        },
        phase,
    }
}

#[test]
fn complete_phase_basis_comparison_preserves_relative_weights_and_selectors() {
    assert!(!matches(
        &Reduction::Residual,
        &Reduction::Sum(Box::new(fixture()))
    ));
    let mut left = fixture();
    left.coefficient = KernelScalar::Rational(integer(1));
    let mut right = left.clone();
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathBra { term: 0, path: 0 };
    right.phase.substitute(&x, &bit(&x).xor(&bit(&y)));
    let compare = |a: WorkingTerm, b: WorkingTerm| {
        matches(&Reduction::Sum(Box::new(a)), &Reduction::Sum(Box::new(b)))
    };
    assert!(compare(left.clone(), right.clone()));
    let mut wrong = right.clone();
    wrong.coefficient = KernelScalar::Rational(integer(2));
    assert!(!compare(left.clone(), wrong));
    let mut wrong = right.clone();
    wrong.constraints.clear();
    assert!(!compare(left.clone(), wrong));
    let mut wrong = right.clone();
    wrong.phase.add_boolean(
        &bit(&KernelVariable::InputBra(0)),
        PhaseCoefficient::rational(ratio(1, 4)),
    );
    assert!(!compare(left.clone(), wrong));
    // A removed, now-vacuous binder still carries a factor of two.
    right.paths.remove(&y);
    assert!(!compare(left, right));
}

#[test]
fn checkpoint_capture_is_complete_and_does_not_change_ordinary_refusal() {
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathKet { term: 0, path: 1 };
    let mut large = KernelBooleanPolynomial::zero();
    for i in 0..100 {
        large = large.xor(&bit(&KernelVariable::InputKet(i)));
    }
    let mut source = WorkingTerm {
        paths: BTreeSet::from([x.clone(), y.clone()]),
        constraints: vec![bit(&x).xor(&large)],
        coefficient: KernelScalar::Rational(integer(3)),
        phase: KernelPhasePolynomial::default(),
    };
    source
        .phase
        .add_boolean(&bit(&x), PhaseCoefficient::rational(ratio(1, 8)));
    let mut checkpoint = None;
    assert!(matches!(
        reduce_working_term_with_checkpoint(source.clone(), Some(&mut checkpoint)),
        Reduction::Residual
    ));
    let checkpoint = checkpoint.unwrap();
    // The ordinary reducer already counted the absent y before its next
    // refused pivot. Capture preserves that COMPLETE updated term.
    assert_eq!(checkpoint.paths, BTreeSet::from([x.clone()]));
    assert_eq!(checkpoint.constraints, source.constraints);
    assert_eq!(checkpoint.coefficient, KernelScalar::Rational(integer(6)));
    assert_eq!(checkpoint.phase, source.phase);
    assert!(matches!(reduce_working_term(source), Reduction::Residual));
    assert!(!matches_checkpoints(
        &Reduction::Residual,
        &Reduction::Residual,
        None,
        None
    ));
    let mut oversized = checkpoint.clone();
    oversized
        .paths
        .extend((0..32769).map(|path| KernelVariable::PathKet { term: 7, path }));
    assert!(!checkpoint_admitted(&oversized));
    assert!(without_vacuous(&oversized).is_none());
    let mut missing = checkpoint;
    missing.paths.remove(&x);
    assert!(!checkpoint_admitted(&missing));
}
