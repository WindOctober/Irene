use super::super::scalar::{integer, ratio};
use super::super::{KernelBooleanPolynomial, KernelScalar, KernelVariable};
use super::*;
use crate::symbolic::PhaseCoefficient;
use num_rational::BigRational;
use std::collections::{BTreeMap, BTreeSet};

fn bit(v: &KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v.clone())
}

fn fixture() -> WorkingTerm {
    let [x, y, z] = [0, 1, 2].map(|path| KernelVariable::PathKet { term: 0, path });
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(
        &bit(&x).xor(&bit(&y)),
        PhaseCoefficient::rational(ratio(1, 8)),
    );
    phase.add_boolean(&bit(&z), PhaseCoefficient::rational(ratio(1, 8)));
    phase.add_boolean(
        &bit(&KernelVariable::InputKet(0)),
        PhaseCoefficient::rational(ratio(1, 4)),
    );
    WorkingTerm {
        paths: BTreeSet::from([x, y, z]),
        constraints: vec![bit(&KernelVariable::InputKet(0))],
        coefficient: KernelScalar::Select {
            condition: bit(&KernelVariable::InputBra(0)),
            when_true: Box::new(KernelScalar::Rational(integer(-3))),
            when_false: Box::new(KernelScalar::Rational(integer(2))),
        },
        phase,
    }
}

type Point = BTreeMap<KernelVariable, bool>;
type Histogram = BTreeMap<BigRational, BigRational>;

fn boolean(p: &KernelBooleanPolynomial, point: &Point) -> bool {
    p.terms()
        .fold(false, |parity, m| parity ^ m.variables().all(|v| point[v]))
}

fn scalar(s: &KernelScalar, point: &Point) -> BigRational {
    match s {
        KernelScalar::Rational(r) => r.clone(),
        KernelScalar::Mul(a, b) => scalar(a, point) * scalar(b, point),
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => scalar(
            if boolean(condition, point) {
                when_true
            } else {
                when_false
            },
            point,
        ),
        _ => panic!("unsupported test scalar"),
    }
}

// Literal weighted phase histograms: no production reducer or float oracle.
fn histogram(term: &WorkingTerm, input: usize) -> Histogram {
    assert!(term.paths.len() <= 10);
    let mut result = Histogram::new();
    for assignment in 0..1usize << term.paths.len() {
        let mut point = Point::from([
            (KernelVariable::InputKet(0), input & 1 != 0),
            (KernelVariable::InputBra(0), input & 2 != 0),
        ]);
        point.extend(
            term.paths
                .iter()
                .enumerate()
                .map(|(i, v)| (v.clone(), assignment & (1 << i) != 0)),
        );
        if term.constraints.iter().any(|g| boolean(g, &point)) {
            continue;
        }
        let turns: BigRational = term
            .phase
            .terms()
            .filter(|(m, _)| m.variables().all(|v| point[v]))
            .map(|(_, c)| c.as_rational().unwrap())
            .sum();
        let turns = (turns % integer(1) + integer(1)) % integer(1);
        *result.entry(turns).or_insert_with(|| integer(0)) += scalar(&term.coefficient, &point);
    }
    result.retain(|_, v| *v != integer(0));
    result
}

fn product(factors: &[WorkingTerm], input: usize) -> Histogram {
    let mut out = Histogram::from([(integer(0), integer(1))]);
    for factor in factors {
        let mut next = Histogram::new();
        for (a, weight) in out {
            for (b, other) in histogram(factor, input) {
                *next
                    .entry((&a + b) % integer(1))
                    .or_insert_with(|| integer(0)) += &weight * other;
            }
        }
        next.retain(|_, v| *v != integer(0));
        out = next;
    }
    out
}

fn equal_terms(a: WorkingTerm, b: WorkingTerm, _: &mut usize) -> bool {
    (0..4).all(|input| histogram(&a, input) == histogram(&b, input))
}
fn equal_factors(a: Vec<WorkingTerm>, b: Vec<WorkingTerm>) -> bool {
    (0..4).all(|input| product(&a, input) == product(&b, input))
}

#[test]
fn changed_syntax_requires_a_successful_complete_proof() {
    let source = fixture();
    let mut calls = 0;
    assert!(!matches(
        &source,
        &source,
        |left, right, work| {
            calls += 1;
            assert!(*work < WORK_CELLS);
            assert_eq!(left.paths, source.paths);
            assert_eq!(left.constraints, source.constraints);
            assert_eq!(left.coefficient, source.coefficient);
            assert!(left.phase.term_count() < source.phase.term_count());
            for input in 0..4 {
                assert_eq!(histogram(&source, input), histogram(&left, input));
                assert_eq!(histogram(&source, input), histogram(&right, input));
            }
            false
        },
        |_, _| false
    ));
    assert!(calls >= 1);
    assert!(matches(&source, &source, equal_terms, equal_factors));
}

#[test]
fn block_fallback_keeps_original_factors_after_consuming_term_proof() {
    let source = fixture();
    let called = std::cell::Cell::new(false);
    assert!(try_strategy(
        &source,
        &source,
        Strategy::Blocks8,
        &mut |left, right, work| {
            assert!(equal_terms(left, right, work));
            *work = 0;
            called.set(true);
            false
        },
        &mut |left, right| {
            assert!(called.get());
            for input in 0..4 {
                assert_eq!(product(&left, input), histogram(&source, input));
                assert_eq!(product(&right, input), histogram(&source, input));
            }
            equal_factors(left, right)
        }
    ));
}

#[test]
fn unequal_common_weights_guards_phases_and_multiplicities_are_not_dropped() {
    let source = fixture();
    for field in 0..4 {
        let mut other = source.clone();
        match field {
            0 => other.coefficient = KernelScalar::Rational(integer(1)),
            1 => other.constraints.clear(),
            2 => other.phase.add_boolean(
                &bit(&KernelVariable::InputBra(0)),
                PhaseCoefficient::rational(ratio(1, 4)),
            ),
            _ => {
                other
                    .paths
                    .insert(KernelVariable::PathBra { term: 9, path: 0 });
            }
        }
        assert!(!matches(&source, &other, equal_terms, equal_factors));
    }
}

#[test]
fn interrupted_and_skipped_block_rewrites_keep_every_factor() {
    let source = fixture();
    for width in [8, 16] {
        for mut work in [0, 1, 20, 100, 1000, WORK_CELLS] {
            let (factors, _, _) = compact_block_factors(&source, &mut work, width).unwrap();
            let paths: BTreeSet<_> = factors
                .iter()
                .flat_map(|f| f.paths.iter().cloned())
                .collect();
            assert_eq!(paths, source.paths);
            for input in 0..4 {
                assert_eq!(product(&factors, input), histogram(&source, input));
            }
        }
    }
}

#[test]
fn wide_attempt_can_rewrite_a_nine_path_factor_without_losing_the_other_factor() {
    let mut source = fixture();
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathKet { term: 0, path: 1 };
    for path in 3..10 {
        let v = KernelVariable::PathKet { term: 0, path };
        source.paths.insert(v.clone());
        source.phase.add_boolean(
            &bit(&x).xor(&bit(&y)).and(&bit(&v)),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    for strategy in [Strategy::Single, Strategy::Blocks8] {
        assert!(!try_strategy(
            &source,
            &source,
            strategy,
            &mut |_, _, _| panic!("no eligible changed factor"),
            &mut |_, _| panic!("no candidate")
        ));
    }
    assert!(try_strategy(
        &source,
        &source,
        Strategy::Blocks16,
        &mut |a, b, work| {
            assert_eq!(a.paths, source.paths);
            for input in 0..4 {
                assert_eq!(histogram(&a, input), histogram(&source, input));
            }
            equal_terms(a, b, work)
        },
        &mut equal_factors
    ));
}

#[test]
fn malformed_or_graph_only_sources_do_not_reach_proof_callbacks() {
    let source = fixture();
    let mut missing = source.clone();
    missing
        .paths
        .remove(&KernelVariable::PathKet { term: 0, path: 0 });
    let mut graph = source.clone();
    graph.constraints.push(KernelBooleanPolynomial::from_graph(
        bit(&KernelVariable::InputKet(0)).as_graph().and(
            &bit(&KernelVariable::InputBra(0))
                .as_graph()
                .xor(&bit(&KernelVariable::PathKet { term: 0, path: 0 }).as_graph()),
        ),
    ));
    for bad in [missing, graph] {
        assert!(!matches(
            &bad,
            &source,
            |_, _, _| panic!("inadmissible source"),
            |_, _| panic!("inadmissible source")
        ));
    }
}

#[test]
fn complete_reduced_factors_reuse_remaining_budget_without_omitting_common_fields() {
    let source = fixture();
    let mut work = 0;
    assert!(matches_reduced_components(
        &source,
        &source,
        &mut work,
        |left, right, changed| {
            assert!(!changed);
            for input in 0..4 {
                assert_eq!(product(&left, input), histogram(&source, input));
            }
            equal_factors(left, right)
        }
    ));
    assert_eq!(work, 0);
    assert!(!matches_reduced_components(
        &source,
        &source,
        &mut work,
        |_, _, _| false
    ));
}
