use super::super::scalar::{integer, ratio};
use super::super::{KernelBooleanPolynomial, KernelScalar};
use super::*;

#[test]
fn malformed_ownership_free_coordinates_and_graph_phases_are_refused() {
    let source = fixture();
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathBra { term: 0, path: 0 };
    let free = KernelVariable::InputKet(0);
    for (a, b) in [(&free, &y), (&x, &free)] {
        let mut phase = source.phase.clone();
        assert!(transvection(&mut phase, a, b, &mut work_budget()).is_none());
        assert_eq!(phase, source.phase);
    }
    let mut phase = source.phase.clone();
    assert_eq!(transvection(&mut phase, &x, &x, &mut 0), Some(false));
    assert_eq!(phase, source.phase);
    let mut missing = source.clone();
    missing.paths.remove(&x);
    assert!(!admitted(&missing));
    assert!(compact(&missing, &mut work_budget()).is_none());
    let mut illegal = source.clone();
    illegal.paths.insert(free.clone());
    assert!(compact(&illegal, &mut work_budget()).is_none());
    let a = bit(&x).as_graph();
    let b = bit(&y).as_graph();
    let c = bit(&free).as_graph();
    let mut graph = KernelPhasePolynomial::default();
    graph.add_boolean(
        &KernelBooleanPolynomial::from_graph(a.and(&b.xor(&c))),
        PhaseCoefficient::rational(ratio(1, 4)),
    );
    assert!(!graph.is_algebraic());
    let before = graph.clone();
    assert!(transvection(&mut graph, &x, &y, &mut work_budget()).is_none());
    assert_eq!(graph, before);
}

#[test]
fn every_refused_delta_is_atomic_including_late_budget_exhaustion() {
    let source = fixture();
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathBra { term: 0, path: 0 };
    let mut expected = source.phase.clone();
    assert_eq!(
        transvection(&mut expected, &x, &y, &mut work_budget()),
        Some(true)
    );
    let mut successes = 0;
    for limit in 0..256 {
        let mut phase = source.phase.clone();
        match transvection(&mut phase, &x, &y, &mut { limit }) {
            Some(true) => {
                assert_eq!(phase, expected);
                successes += 1;
            }
            _ => assert_eq!(phase, source.phase),
        }
    }
    assert!(successes > 0);
}

#[test]
fn compact_preserves_weighted_sums_for_every_free_input_and_guard_value() {
    let mut source = fixture();
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathBra { term: 0, path: 0 };
    let free = KernelVariable::InputBra(0);
    // Add input-dependent phase without changing guard/scalar independence.
    source.phase.add_boolean(
        &bit(&x).xor(&bit(&y)).and(&bit(&free)),
        PhaseCoefficient::rational(ratio(1, 8)),
    );
    let (result, changed) = compact(&source, &mut work_budget()).unwrap();
    assert!(changed);
    let boolean = |p: &KernelBooleanPolynomial, point: &BTreeMap<KernelVariable, bool>| {
        p.terms()
            .fold(false, |v, m| v ^ m.variables().all(|w| point[w]))
    };
    for guard in [false, true] {
        for input in [false, true] {
            let histogram = |term: &WorkingTerm| {
                let mut sums = BTreeMap::<BigRational, BigRational>::new();
                for assignment in 0..(1usize << term.paths.len()) {
                    let mut point = BTreeMap::from([
                        (KernelVariable::InputKet(0), guard),
                        (free.clone(), input),
                    ]);
                    for (i, v) in term.paths.iter().enumerate() {
                        point.insert(v.clone(), assignment & (1 << i) != 0);
                    }
                    if term.constraints.iter().any(|p| boolean(p, &point)) {
                        continue;
                    }
                    let KernelScalar::Select {
                        condition,
                        when_true,
                        when_false,
                    } = &term.coefficient
                    else {
                        panic!()
                    };
                    let KernelScalar::Rational(weight) = (if boolean(condition, &point) {
                        when_true
                    } else {
                        when_false
                    })
                    .as_ref() else {
                        panic!()
                    };
                    let phase = evaluate(&term.phase, &point);
                    let phase = (phase % integer(1) + integer(1)) % integer(1);
                    *sums.entry(phase).or_insert_with(|| integer(0)) += weight;
                }
                sums
            };
            assert_eq!(histogram(&source), histogram(&result));
        }
    }
}
use crate::symbolic::PhaseCoefficient;
use num_rational::BigRational;
use std::collections::BTreeSet;
fn work_budget() -> usize {
    1_000_000
}

fn bit(v: &KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v.clone())
}

fn evaluate(phase: &KernelPhasePolynomial, values: &BTreeMap<KernelVariable, bool>) -> BigRational {
    phase
        .terms()
        .filter(|(m, _)| m.variables().all(|v| values[v]))
        .map(|(_, c)| c.as_rational().unwrap())
        .sum()
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
fn complete_transvections_preserve_all_signed_phase_assignments() {
    let variables = [
        KernelVariable::PathKet { term: 0, path: 0 },
        KernelVariable::PathBra { term: 1, path: 0 },
        KernelVariable::InputKet(0),
    ];
    let mut changes = 0;
    for code in 0usize..256 {
        let mut phase = KernelPhasePolynomial::default();
        for mask in 0..8 {
            let monomial = variables
                .iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .fold(KernelBooleanPolynomial::one(), |m, (_, v)| m.and(&bit(v)));
            if code & (1 << mask) != 0 {
                phase.add_boolean(
                    &monomial,
                    PhaseCoefficient::rational(ratio(1 + mask as i64, 24)),
                );
            }
        }
        phase.substitute(&variables[0], &bit(&variables[0]).xor(&bit(&variables[1])));
        let original = phase.clone();
        let changed =
            transvection(&mut phase, &variables[0], &variables[1], &mut work_budget()).unwrap();
        if !changed {
            assert_eq!(phase, original);
            continue;
        }
        changes += 1;
        assert!(phase.term_count() <= original.term_count());
        for assignment in 0..8 {
            let values = variables
                .iter()
                .enumerate()
                .map(|(i, v)| (v.clone(), assignment & (1 << i) != 0))
                .collect::<BTreeMap<_, _>>();
            let mut before = values.clone();
            before.insert(
                variables[0].clone(),
                values[&variables[0]] ^ values[&variables[1]],
            );
            assert!((evaluate(&original, &before) - evaluate(&phase, &values)).is_integer());
        }
    }
    assert!(changes > 0);
}

#[test]
fn phase_basis_retains_guards_scalars_binders_and_refuses_missing_premises() {
    let source = fixture();
    let (compacted, changed) = compact(&source, &mut work_budget()).unwrap();
    assert!(changed);
    assert_eq!(source.paths, compacted.paths);
    assert_eq!(source.constraints, compacted.constraints);
    assert_eq!(source.coefficient, compacted.coefficient);
    assert!(compacted.phase.term_count() < source.phase.term_count());
    let x = source.paths.first().unwrap().clone();
    let mut blocked = source.clone();
    blocked.constraints.push(bit(&x));
    assert!(!compact(&blocked, &mut work_budget()).is_some_and(|(_, changed)| changed));
    blocked = source.clone();
    blocked.coefficient = KernelScalar::Select {
        condition: bit(&x),
        when_true: Box::new(KernelScalar::Rational(integer(1))),
        when_false: Box::new(KernelScalar::Rational(integer(0))),
    };
    assert!(!compact(&blocked, &mut work_budget()).is_some_and(|(_, changed)| changed));
    blocked = source.clone();
    blocked.paths.remove(&x);
    assert!(!admitted(&blocked));
    let (unchanged, changed) = compact(&source, &mut 0).unwrap();
    assert!(!changed);
    assert_eq!(unchanged.phase, source.phase);
    let mut phase = source.phase.clone();
    let y = source.paths.last().unwrap().clone();
    assert!(transvection(&mut phase, &x, &y, &mut 1).is_none());
    assert_eq!(phase, source.phase);
    phase.add_boolean(
        &bit(&x),
        PhaseCoefficient::rational(BigRational::new(1.into(), BigInt::from(1) << 300)),
    );
    let oversized = phase.clone();
    assert!(transvection(&mut phase, &x, &y, &mut work_budget()).is_none());
    assert_eq!(phase, oversized);
}

#[test]
fn sparse_delta_matches_full_substitution_and_partial_sweep_keeps_whole_terms() {
    let source = fixture();
    for x in &source.paths {
        for y in &source.paths {
            if x == y {
                continue;
            }
            let mut sparse = source.phase.clone();
            let changed = transvection(&mut sparse, x, y, &mut work_budget()).unwrap();
            let mut full = source.phase.clone();
            full.substitute(x, &bit(x).xor(&bit(y)));
            assert_eq!(sparse, if changed { full } else { source.phase.clone() });
        }
    }
    let mut mixed = source.clone();
    for path in [10, 11] {
        mixed
            .paths
            .insert(KernelVariable::PathKet { term: 0, path });
    }
    let a = bit(&KernelVariable::PathKet { term: 0, path: 10 });
    let b = bit(&KernelVariable::PathKet { term: 0, path: 11 });
    mixed
        .phase
        .add_boolean(&a.xor(&b), PhaseCoefficient::rational(ratio(1, 16)));
    let mut partial_found = false;
    for limit in 1..512 {
        let mut budget = limit;
        let (result, changed) = compact(&mixed, &mut budget).unwrap();
        assert_eq!(result.paths, mixed.paths);
        assert_eq!(result.constraints, mixed.constraints);
        assert_eq!(result.coefficient, mixed.coefficient);
        if changed && budget == 0 {
            partial_found = true;
            // Five binders remain; count ALL 32 assignments as an exact
            // phase histogram. No partial product or discarded tail.
            let histogram = |phase: &KernelPhasePolynomial| {
                let paths = mixed.paths.iter().collect::<Vec<_>>();
                let mut values = BTreeMap::new();
                for bits in 0..32 {
                    let point = paths
                        .iter()
                        .enumerate()
                        .map(|(i, v)| ((*v).clone(), bits & (1 << i) != 0))
                        .collect();
                    let turns = evaluate(phase, &point);
                    let reduced = (turns % integer(1) + integer(1)) % integer(1);
                    *values.entry(reduced).or_insert(0usize) += 1;
                }
                values
            };
            assert_eq!(histogram(&mixed.phase), histogram(&result.phase));
            break;
        }
    }
    assert!(partial_found);
    let mut illegal = source;
    illegal.paths.insert(KernelVariable::InputKet(0));
    assert!(!admitted(&illegal));
}

#[test]
fn cell_saving_does_not_allow_term_growth_or_oversized_inputs() {
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathBra { term: 0, path: 0 };
    let high = (0..8).fold(KernelBooleanPolynomial::one(), |m, i| {
        m.and(&bit(&KernelVariable::InputKet(i)))
    });
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(
        &bit(&x).xor(&bit(&y)).and(&high),
        PhaseCoefficient::rational(ratio(1, 8)),
    );
    for i in 10..13 {
        phase.add_boolean(
            &bit(&x)
                .and(&bit(&y))
                .and(&bit(&KernelVariable::InputKet(i))),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    let original = phase.clone();
    let mut transformed = original.clone();
    transformed.substitute(&x, &bit(&x).xor(&bit(&y)));
    let cells = |p: &KernelPhasePolynomial| {
        p.terms()
            .map(|(m, _)| 1 + m.variables().count())
            .sum::<usize>()
    };
    assert!(cells(&transformed) < cells(&original));
    assert!(transformed.term_count() > original.term_count());
    assert!(!transvection(&mut phase, &x, &y, &mut work_budget()).unwrap());
    assert_eq!(phase, original);
    let mut oversized = fixture();
    oversized
        .constraints
        .resize(65, bit(&KernelVariable::InputKet(0)));
    assert!(!admitted(&oversized));
    oversized = fixture();
    oversized
        .paths
        .extend((0..257).map(|path| KernelVariable::PathKet { term: 9, path }));
    assert!(!admitted(&oversized));
}
