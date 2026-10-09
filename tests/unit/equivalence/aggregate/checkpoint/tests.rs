use super::*;
use crate::equivalence::aggregate::scalar::{integer, normalize_scalar};
use crate::equivalence::kernel::{
    KernelBooleanPolynomial, KernelPhasePolynomial, KernelScalar, KernelVariable,
};
use crate::symbolic::PhaseCoefficient;
use std::collections::BTreeSet;

fn term(weight: i64) -> WorkingTerm {
    WorkingTerm {
        constraints: vec![KernelBooleanPolynomial::variable(KernelVariable::InputKet(
            0,
        ))],
        paths: BTreeSet::from([KernelVariable::PathKet { term: 0, path: 0 }]),
        coefficient: KernelScalar::Rational(integer(weight)),
        phase: KernelPhasePolynomial::default(),
    }
}

fn same(left: &WorkingTerm, right: &WorkingTerm) -> bool {
    left.paths == right.paths
        && left.constraints == right.constraints
        && left.phase == right.phase
        && left.coefficient == right.coefficient
}

fn equal_compacted(left: WorkingTerm, right: WorkingTerm) -> bool {
    same(&left, &right)
}

#[test]
fn capture_preserves_every_field_and_rejects_missing_ownership() {
    let mut input = term(-3);
    let path = input.paths.iter().next().unwrap().clone();
    input.phase.add_boolean(
        &KernelBooleanPolynomial::variable(path.clone()),
        PhaseCoefficient::rational(integer(1) / integer(8)),
    );
    let saved = capture(input.clone()).unwrap();
    assert!(same(&saved, &input));
    input.paths.remove(&path);
    assert!(capture(input).is_none());
}

#[test]
fn refusal_without_both_complete_sources_never_invokes_a_proof() {
    let input = term(1);
    for (left, right) in [(None, None), (Some(&input), None), (None, Some(&input))] {
        assert!(!matches(
            Source::Refused,
            Source::Refused,
            left,
            right,
            |_, _| panic!("missing source"),
            |_, _| panic!("missing source")
        ));
    }
    assert!(!matches(
        Source::Sum(&input),
        Source::Sum(&input),
        None,
        None,
        |_, _| panic!("ordinary route"),
        |_, _| panic!("ordinary route")
    ));
}

#[test]
fn finished_outcomes_cannot_reuse_stale_checkpoints() {
    let input = term(1);
    for left_finished in [false, true] {
        let (left, right) = if left_finished {
            (Source::Finished, Source::Refused)
        } else {
            (Source::Refused, Source::Finished)
        };
        assert!(!matches(
            left,
            right,
            Some(&input),
            Some(&input),
            |_, _| panic!("finished source"),
            |_, _| panic!("finished source")
        ));
    }
}

#[test]
fn complete_sums_take_precedence_over_stale_checkpoints() {
    let input = term(3);
    let stale = term(99);
    assert!(matches(
        Source::Sum(&input),
        Source::Refused,
        Some(&stale),
        Some(&input),
        equal_compacted,
        |_, _| panic!("unexpected wide route")
    ));
    assert!(matches(
        Source::Refused,
        Source::Sum(&input),
        Some(&input),
        Some(&stale),
        equal_compacted,
        |_, _| panic!("unexpected wide route")
    ));
}

#[test]
fn exact_multiplicity_is_retained_and_refused_proof_stays_inconclusive() {
    let left = term(3);
    let mut right = term(6);
    right.paths.clear();
    let prove = |a: WorkingTerm, b: WorkingTerm| {
        assert!(a.paths.is_empty() && b.paths.is_empty());
        assert_eq!(
            normalize_scalar(a.coefficient.clone()),
            KernelScalar::Rational(integer(6))
        );
        same(&a, &b)
    };
    assert!(matches(
        Source::Refused,
        Source::Sum(&right),
        Some(&left),
        None,
        prove,
        |_, _| panic!("unexpected wide route")
    ));
    assert!(!matches(
        Source::Refused,
        Source::Sum(&right),
        Some(&left),
        None,
        |_, _| false,
        |_, _| panic!("failed proof is not a new source")
    ));
    right.coefficient = KernelScalar::Rational(integer(5));
    assert!(!matches(
        Source::Refused,
        Source::Sum(&right),
        Some(&left),
        None,
        equal_compacted,
        |_, _| panic!("unexpected wide route")
    ));
}

#[test]
fn wide_route_receives_both_original_complete_terms() {
    let mut wide = term(1);
    wide.paths = (0..257)
        .map(|path| KernelVariable::PathKet { term: 0, path })
        .collect();
    for path in &wide.paths {
        wide.phase.add_boolean(
            &KernelBooleanPolynomial::variable(path.clone()),
            PhaseCoefficient::rational(integer(1) / integer(8)),
        );
    }
    let small = term(3);
    for verdict in [false, true] {
        assert_eq!(
            matches(
                Source::Refused,
                Source::Sum(&small),
                Some(&wide),
                None,
                |_, _| panic!("active path admission"),
                |a, b| {
                    assert!(same(a, &wide) && same(b, &small));
                    verdict
                }
            ),
            verdict
        );
    }
}

#[test]
fn malformed_sources_cannot_reach_either_proof_callback() {
    let input = term(1);
    let mut invalid = input.clone();
    invalid.paths.insert(KernelVariable::InputBra(8));
    assert!(!matches(
        Source::Refused,
        Source::Sum(&input),
        Some(&invalid),
        None,
        |_, _| panic!("invalid source"),
        |_, _| panic!("invalid source")
    ));
}
