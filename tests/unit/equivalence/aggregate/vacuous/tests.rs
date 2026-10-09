use super::*;

#[test]
fn exact_power_of_two_retains_free_phase_and_scales_negative_rational_weight() {
    for count in [0usize, 1, 3, 16, 512] {
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(
            &bit(&KernelVariable::InputKet(0)),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
        let source = WorkingTerm {
            paths: (0..count)
                .map(|path| KernelVariable::PathKet { term: 0, path })
                .collect(),
            constraints: vec![bit(&KernelVariable::InputBra(0))],
            coefficient: KernelScalar::Rational(ratio(-3, 7)),
            phase,
        };
        let result = remove(&source).unwrap();
        assert!(result.paths.is_empty());
        assert_eq!(result.constraints, source.constraints);
        assert_eq!(result.phase, source.phase);
        let coefficient = super::super::scalar::normalize_scalar(result.coefficient);
        assert_eq!(
            coefficient,
            KernelScalar::Rational(
                ratio(-3, 7) * BigRational::from_integer(BigInt::from(1) << count)
            )
        );
    }
}

#[test]
fn ownership_and_active_path_limits_refuse_without_altering_source() {
    let mut source = fixture();
    source.paths.insert(KernelVariable::InputKet(7));
    assert!(!admitted(&source));
    assert!(remove(&source).is_none());
    let mut source = fixture();
    let ghost = KernelVariable::PathBra { term: 99, path: 1 };
    source.constraints.push(bit(&ghost));
    assert!(!admitted(&source));
    assert!(remove(&source).is_none());
    let mut source = fixture();
    source.phase = KernelPhasePolynomial::default();
    source.paths = (0..257)
        .map(|path| KernelVariable::PathKet { term: 8, path })
        .collect();
    for p in &source.paths {
        source
            .phase
            .add_boolean(&bit(p), PhaseCoefficient::rational(ratio(1, 8)));
    }
    let before = source.clone();
    assert!(remove(&source).is_none());
    assert_eq!(source.paths, before.paths);
    assert_eq!(source.phase, before.phase);
    source.paths = (0..32769)
        .map(|path| KernelVariable::PathKet { term: 8, path })
        .collect();
    assert!(!admitted(&source));
}

#[test]
fn graph_only_dependencies_are_not_silently_ignored() {
    let a = bit(&KernelVariable::InputKet(0)).as_graph();
    let b = bit(&KernelVariable::InputBra(0)).as_graph();
    let c = bit(&KernelVariable::PathKet { term: 0, path: 0 }).as_graph();
    let graph = KernelBooleanPolynomial::from_graph(a.and(&b.xor(&c)));
    assert!(!graph.is_algebraic());
    for field in 0..3 {
        let mut source = fixture();
        match field {
            0 => source.constraints.push(graph.clone()),
            1 => source
                .phase
                .add_boolean(&graph, PhaseCoefficient::rational(ratio(1, 4))),
            _ => {
                source.coefficient = KernelScalar::Select {
                    condition: graph.clone(),
                    when_true: Box::new(KernelScalar::Rational(integer(1))),
                    when_false: Box::new(KernelScalar::Rational(integer(2))),
                }
            }
        };
        assert!(!admitted(&source));
        assert!(remove(&source).is_none());
    }
}
use super::super::KernelPhasePolynomial;
use super::super::scalar::{integer, ratio};
use crate::symbolic::PhaseCoefficient;
use std::collections::BTreeMap;

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
fn checkpoint_vacuous_count_preserves_complete_weight_and_dependencies() {
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathBra { term: 0, path: 0 };
    let z = KernelVariable::PathKet { term: 0, path: 1 };
    let free = KernelVariable::InputKet(0);
    for code in 0usize..16 {
        let mut source = fixture();
        source.coefficient = KernelScalar::Rational(ratio(-3, 8));
        source.constraints = vec![bit(&x).xor(&bit(&free))];
        source.phase = KernelPhasePolynomial::default();
        for mask in 0..4 {
            if code & (1 << mask) != 0 {
                let mut monomial = KernelBooleanPolynomial::one();
                if mask & 1 != 0 {
                    monomial = monomial.and(&bit(&y));
                }
                if mask & 2 != 0 {
                    monomial = monomial.and(&bit(&free));
                }
                source.phase.add_boolean(
                    &monomial,
                    PhaseCoefficient::rational(ratio(1 + mask as i64, 8)),
                );
            }
        }
        let result = remove(&source).unwrap();
        assert!(result.paths.contains(&x));
        assert!(!result.paths.contains(&z));
        // Literal finite weighted phase histogram, no production reduction
        // or cyclotomic arithmetic. Equal histograms imply equal sums.
        for free_value in [false, true] {
            let histogram = |term: &WorkingTerm| {
                let paths = term.paths.iter().collect::<Vec<_>>();
                let mut sum = BTreeMap::<BigRational, BigRational>::new();
                for bits in 0..(1 << paths.len()) {
                    let mut point = BTreeMap::from([(free.clone(), free_value)]);
                    point.extend(
                        paths
                            .iter()
                            .enumerate()
                            .map(|(i, v)| ((*v).clone(), bits & (1 << i) != 0)),
                    );
                    if term.constraints.iter().any(|row| {
                        row.terms()
                            .filter(|m| m.variables().all(|v| point[v]))
                            .count()
                            % 2
                            != 0
                    }) {
                        continue;
                    }
                    let turns = evaluate(&term.phase, &point);
                    let turns = (turns % integer(1) + integer(1)) % integer(1);
                    let KernelScalar::Rational(weight) = &term.coefficient else {
                        unreachable!()
                    };
                    *sum.entry(turns).or_insert_with(|| integer(0)) += weight;
                }
                sum
            };
            assert_eq!(histogram(&source), histogram(&result));
        }
    }
    let mut nested = fixture();
    nested.coefficient = KernelScalar::Select {
        condition: bit(&z),
        when_true: Box::new(KernelScalar::Rational(integer(1))),
        when_false: Box::new(KernelScalar::Select {
            condition: bit(&y),
            when_true: Box::new(KernelScalar::Rational(integer(3))),
            when_false: Box::new(KernelScalar::Rational(integer(-2))),
        }),
    };
    nested.phase = KernelPhasePolynomial::default();
    nested.constraints = vec![bit(&x)];
    let result = remove(&nested).unwrap();
    assert_eq!(result.paths, nested.paths);
    assert_eq!(result.coefficient, nested.coefficient);
    nested.paths.remove(&y);
    assert!(remove(&nested).is_none());
}

#[test]
fn checkpoint_vacuous_count_preserves_nested_zero_and_signed_weights() {
    fn scalar(s: &KernelScalar, point: &BTreeMap<KernelVariable, bool>) -> BigRational {
        match s {
            KernelScalar::Rational(r) => r.clone(),
            KernelScalar::Neg(a) => -scalar(a, point),
            KernelScalar::Add(a, b) => scalar(a, point) + scalar(b, point),
            KernelScalar::Mul(a, b) => scalar(a, point) * scalar(b, point),
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => {
                let active = condition
                    .terms()
                    .fold(false, |v, m| v ^ m.variables().all(|w| point[w]));
                scalar(if active { when_true } else { when_false }, point)
            }
            _ => panic!("unsupported independent test scalar"),
        }
    }
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathBra { term: 0, path: 0 };
    let z = KernelVariable::PathKet { term: 0, path: 1 };
    let free = KernelVariable::InputKet(0);
    for a in -2..3 {
        for b in -2..3 {
            let mut source = fixture();
            source.phase = KernelPhasePolynomial::default();
            source.constraints = vec![bit(&x).xor(&bit(&free))];
            source.coefficient = KernelScalar::Select {
                condition: bit(&free),
                when_true: Box::new(KernelScalar::Select {
                    condition: bit(&y),
                    when_true: Box::new(KernelScalar::Rational(integer(a))),
                    when_false: Box::new(KernelScalar::Rational(integer(b))),
                }),
                when_false: Box::new(KernelScalar::Neg(Box::new(KernelScalar::Rational(
                    integer(a + b),
                )))),
            };
            let result = remove(&source).unwrap();
            assert_eq!(result.paths, BTreeSet::from([x.clone(), y.clone()]));
            assert!(!result.paths.contains(&z));
            for value in [false, true] {
                let entry = |term: &WorkingTerm| {
                    let mut total = integer(0);
                    for bits in 0..1usize << term.paths.len() {
                        let mut point = BTreeMap::from([(free.clone(), value)]);
                        for (i, w) in term.paths.iter().enumerate() {
                            point.insert(w.clone(), bits & (1 << i) != 0);
                        }
                        if term.constraints.iter().any(|g| {
                            g.terms()
                                .fold(false, |v, m| v ^ m.variables().all(|w| point[w]))
                        }) {
                            continue;
                        }
                        total += scalar(&term.coefficient, &point);
                    }
                    total
                };
                assert_eq!(entry(&source), entry(&result));
            }
            let before = source.clone();
            source.paths.remove(&y);
            assert!(remove(&source).is_none());
            source = before;
            source.coefficient = KernelScalar::Select {
                condition: bit(&free),
                when_true: Box::new(KernelScalar::Rational(integer(0))),
                when_false: Box::new(KernelScalar::Inverse(Box::new(KernelScalar::Rational(
                    integer(0),
                )))),
            };
            assert!(remove(&source).is_none());
        }
    }
    assert!(weight(KernelScalar::Rational(integer(1)), 32769).is_none());
    assert!(
        weight(
            KernelScalar::Rational(BigRational::from_integer(BigInt::from(1) << 32768)),
            1
        )
        .is_none()
    );
}
