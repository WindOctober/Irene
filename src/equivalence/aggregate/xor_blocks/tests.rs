use super::*;

fn correlated_blocks() -> WorkingTerm {
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathBra { term: 1, path: 0 };
    let bit = |v| KernelBooleanPolynomial::variable(v);
    let a = bit(KernelVariable::InputKet(0));
    let b = bit(KernelVariable::InputBra(0));
    let parity = bit(x.clone()).xor(&bit(y.clone()));
    let mut phase = KernelPhasePolynomial::default();
    for free in [a.clone(), b.clone(), a.and(&b)] {
        phase.add_boolean(&parity.and(&free), PhaseCoefficient::rational(ratio(1, 8)));
    }
    // This distinct block must undergo the SAME coordinate change.
    phase.add_boolean(&bit(x.clone()), PhaseCoefficient::rational(ratio(1, 16)));
    phase.add_boolean(&bit(y.clone()), PhaseCoefficient::rational(ratio(1, 8)));
    WorkingTerm {
        paths: BTreeSet::from([x, y]),
        constraints: vec![bit(KernelVariable::ClassicalOutput(0))],
        coefficient: KernelScalar::Select {
            condition: a,
            when_true: Box::new(KernelScalar::Rational(integer(-3))),
            when_false: Box::new(KernelScalar::Rational(integer(2))),
        },
        phase,
    }
}
fn boolean(p: &KernelBooleanPolynomial, point: &BTreeMap<KernelVariable, bool>) -> bool {
    p.terms()
        .fold(false, |v, m| v ^ m.variables().all(|w| point[w]))
}
fn histogram(term: &WorkingTerm, free: u8) -> BTreeMap<BigRational, BigRational> {
    let mut result = BTreeMap::new();
    for assignment in 0..(1usize << term.paths.len()) {
        let mut point = BTreeMap::from([
            (KernelVariable::InputKet(0), free & 1 != 0),
            (KernelVariable::InputBra(0), free & 2 != 0),
            (KernelVariable::ClassicalOutput(0), free & 4 != 0),
        ]);
        for (i, p) in term.paths.iter().enumerate() {
            point.insert(p.clone(), assignment & (1 << i) != 0);
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
        let weight = if boolean(condition, &point) {
            when_true
        } else {
            when_false
        };
        let KernelScalar::Rational(weight) = weight.as_ref() else {
            panic!()
        };
        let phase: BigRational = term
            .phase
            .terms()
            .filter(|(m, _)| m.variables().all(|v| point[v]))
            .map(|(_, c)| c.as_rational().unwrap())
            .sum();
        let phase = (phase % integer(1) + integer(1)) % integer(1);
        *result.entry(phase).or_insert_with(|| integer(0)) += weight;
    }
    result
}
#[test]
fn shared_and_distinct_blocks_use_one_global_coordinate_change() {
    let source = correlated_blocks();
    let mut result = source.clone();
    assert_eq!(compact(&mut result, &mut WORK_CELLS.clone()), Some(true));
    assert_eq!(result.paths, source.paths);
    assert_eq!(result.constraints, source.constraints);
    assert_eq!(result.coefficient, source.coefficient);
    for free in 0..8 {
        assert_eq!(histogram(&source, free), histogram(&result, free));
    }
}
#[test]
fn interrupted_block_work_never_exposes_a_partial_change() {
    let source = correlated_blocks();
    let mut completed = source.clone();
    let mut work = WORK_CELLS;
    assert_eq!(compact(&mut completed, &mut work), Some(true));
    let used = WORK_CELLS - work;
    let mut changed = 0;
    for limit in (0..=used + 8).step_by(7) {
        let mut result = source.clone();
        let status = compact(&mut result, &mut { limit });
        assert_eq!(result.paths, source.paths);
        assert_eq!(result.constraints, source.constraints);
        assert_eq!(result.coefficient, source.coefficient);
        if status == Some(true) {
            changed += 1;
            for free in 0..8 {
                assert_eq!(histogram(&source, free), histogram(&result, free));
            }
        } else {
            assert_eq!(result.phase, source.phase);
        }
    }
    assert!(changed > 0);
}
#[test]
fn free_coordinates_undeclared_binders_and_graph_only_fields_are_not_admitted() {
    let source = correlated_blocks();
    let mut changed = source.clone();
    changed.paths.insert(KernelVariable::InputKet(0));
    let before = changed.phase.clone();
    assert_eq!(compact(&mut changed, &mut WORK_CELLS.clone()), Some(false));
    assert_eq!(changed.phase, before);
    changed = source.clone();
    changed
        .paths
        .remove(&KernelVariable::PathBra { term: 1, path: 0 });
    assert_eq!(compact(&mut changed, &mut WORK_CELLS.clone()), Some(false));
    assert_eq!(changed.phase, source.phase);
    let a = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0)).as_graph();
    let b = KernelBooleanPolynomial::variable(KernelVariable::InputBra(0)).as_graph();
    let c = KernelBooleanPolynomial::variable(KernelVariable::ClassicalOutput(0)).as_graph();
    let graph = KernelBooleanPolynomial::from_graph(a.and(&b.xor(&c)));
    assert!(!graph.is_algebraic());
    for field in 0..2 {
        let mut changed = source.clone();
        if field == 0 {
            changed.constraints.push(graph.clone());
        } else {
            changed
                .phase
                .add_boolean(&graph, PhaseCoefficient::rational(ratio(1, 4)));
        }
        let before = changed.phase.clone();
        assert_eq!(compact(&mut changed, &mut WORK_CELLS.clone()), Some(false));
        assert_eq!(changed.phase, before);
    }
}
use super::super::scalar::{integer, ratio};
use super::super::{KernelBooleanPolynomial, KernelScalar, KernelVariable};
use num_rational::BigRational;
use std::collections::BTreeSet;
const WORK_CELLS: usize = 1_000_000;

/// Full, integer-only transvection, including every unaffected mask. A proposal
/// may temporarily have at most three times the old entries (and <=256 masks).
fn transform(source: &MaskPhase, x: u16, y: u16, work: &mut usize) -> Option<MaskPhase> {
    if x == y || x.count_ones() != 1 || y.count_ones() != 1 {
        return None;
    }
    let mut result = MaskPhase::new();
    for (&mask, coefficient) in source {
        charge(work, 6 * (1 + mask.count_ones() as usize))?;
        let value = coefficient.as_rational()?;
        if value.numer().bits() > 256 || value.denom().bits() > 256 {
            return None;
        }
        if mask & x == 0 {
            insert(&mut result, mask, coefficient.clone());
        } else if mask & y != 0 {
            // (x XOR y)*y = y - x*y in the Boolean integer quotient.
            insert(&mut result, mask & !x, coefficient.clone());
            insert(&mut result, mask, coefficient.scaled(BigInt::from(-1)));
        } else {
            insert(&mut result, mask, coefficient.clone());
            insert(&mut result, (mask & !x) | y, coefficient.clone());
            insert(&mut result, mask | y, coefficient.scaled(BigInt::from(-2)));
        }
    }
    Some(result)
}

#[test]
fn wide_sparse_masks_preserve_all_nine_bit_phase_sums_and_refuse_dense_support() {
    let paths = (0..9)
        .map(|path| KernelVariable::PathKet { term: 0, path })
        .collect::<Vec<_>>();
    let free = KernelVariable::InputKet(0);
    let mut source = WorkingTerm {
        paths: paths.iter().cloned().collect(),
        constraints: Vec::new(),
        coefficient: KernelScalar::Rational(integer(3)),
        phase: KernelPhasePolynomial::default(),
    };
    for v in &paths[2..] {
        for (ends, coefficient) in [
            (vec![paths[0].clone()], ratio(1, 8)),
            (vec![paths[1].clone()], ratio(1, 8)),
            (paths[..2].to_vec(), ratio(-1, 4)),
        ] {
            source.phase.add_term(
                KernelMonomial::from_variables(ends.into_iter().chain([v.clone(), free.clone()])),
                PhaseCoefficient::rational(coefficient),
            );
        }
    }
    let mut result = source.clone();
    assert_eq!(compact(&mut result, &mut WORK_CELLS.clone()), Some(true));
    assert_eq!(result.paths, source.paths);
    assert_eq!(result.constraints, source.constraints);
    assert_eq!(result.coefficient, source.coefficient);
    for input in [false, true] {
        let histogram = |phase: &KernelPhasePolynomial| {
            let mut sum = BTreeMap::<BigRational, usize>::new();
            for bits in 0..512 {
                let mut point = BTreeMap::from([(free.clone(), input)]);
                point.extend(
                    paths
                        .iter()
                        .enumerate()
                        .map(|(i, v)| (v.clone(), bits & (1 << i) != 0)),
                );
                let turns = phase
                    .terms()
                    .filter(|(m, _)| m.variables().all(|v| point[v]))
                    .map(|(_, c)| c.as_rational().unwrap())
                    .sum::<BigRational>();
                let turns = (turns % integer(1) + integer(1)) % integer(1);
                *sum.entry(turns).or_default() += 1;
            }
            sum
        };
        assert_eq!(histogram(&source.phase), histogram(&result.phase));
    }
    let mut guarded = source.clone();
    guarded
        .constraints
        .push(KernelBooleanPolynomial::variable(paths[0].clone()));
    assert_eq!(compact(&mut guarded, &mut WORK_CELLS.clone()), Some(false));
    assert_eq!(guarded.phase, source.phase);
    let mut no_work = source.clone();
    assert_eq!(compact(&mut no_work, &mut 0), None);
    assert_eq!(no_work.phase, source.phase);
    let mut dense = source;
    dense.phase = KernelPhasePolynomial::default();
    for mask in 1..=257 {
        dense.phase.add_term(
            KernelMonomial::from_variables(
                paths
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| mask & (1 << i) != 0)
                    .map(|(_, v)| v.clone()),
            ),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    let before = dense.phase.clone();
    assert_eq!(compact(&mut dense, &mut WORK_CELLS.clone()), Some(false));
    assert_eq!(dense.phase, before);
    let mut full = (0..256)
        .map(|mask| (mask, PhaseCoefficient::rational(ratio(1, 8))))
        .collect::<MaskPhase>();
    assert!(insert_bounded(&mut full, 256, PhaseCoefficient::rational(ratio(1, 8))).is_none());
    assert_eq!(full.len(), 256);
    assert!(insert_bounded(&mut full, 256, PhaseCoefficient::default()).is_some());
    assert_eq!(full.len(), 256);
    let high = BTreeMap::from([(1 << 15, PhaseCoefficient::rational(ratio(1, 8)))]);
    let shifted = delta(&high, 1 << 15, 1 << 14, &mut WORK_CELLS.clone()).unwrap();
    assert_eq!(shifted[&(1 << 14)], PhaseCoefficient::rational(ratio(1, 8)));
    assert_eq!(
        shifted[&((1 << 15) | (1 << 14))],
        PhaseCoefficient::rational(ratio(-1, 4))
    );
}

#[test]
fn sparse_block_limits_check_counterparts_and_outside_delta_keys() {
    let oversized = PhaseCoefficient::rational(BigRational::new(1.into(), BigInt::from(1) << 300));
    let small = PhaseCoefficient::rational(ratio(1, 8));
    let source = BTreeMap::from([(1, small.clone()), (3, oversized.clone())]);
    let mut work = WORK_CELLS;
    assert!(delta(&source, 1, 2, &mut work).is_none());
    let source = BTreeMap::from([(1, small), (2, oversized)]);
    let mut work = WORK_CELLS;
    let changes = delta(&source, 1, 2, &mut work).unwrap();
    let block = Block {
        free: vec![KernelMonomial::one()],
        free_cells: 1,
        phase: source.clone(),
    };
    assert!(delta_cost(&source, &changes, &block).is_none());
    let before = source.clone();
    assert!(delta(&source, 1, 2, &mut 0).is_none());
    assert_eq!(before, source);
}

#[test]
fn mask_changes_match_full_boolean_substitution_for_all_small_phases() {
    let paths = (0..3)
        .map(|path| KernelVariable::PathKet { term: 0, path })
        .collect::<Vec<_>>();
    let expand = |phase: &MaskPhase| {
        let mut result = KernelPhasePolynomial::default();
        for (&mask, coefficient) in phase {
            let mut m = KernelMonomial::one();
            for (i, v) in paths.iter().enumerate() {
                if mask & (1 << i) != 0 {
                    m = m.multiply(&KernelMonomial::variable(v.clone()));
                }
            }
            result.add_term(m, coefficient.clone());
        }
        result
    };
    for code in 0usize..256 {
        let mut source = MaskPhase::new();
        for mask in 0..8 {
            if code & (1 << mask) != 0 {
                insert(
                    &mut source,
                    mask,
                    PhaseCoefficient::rational(ratio(mask as i64 + 1, 24)),
                );
            }
        }
        for x in 0..3 {
            for y in 0..3 {
                if x == y {
                    continue;
                }
                let mut work = WORK_CELLS;
                let result = transform(&source, 1 << x, 1 << y, &mut work).unwrap();
                let change = delta(&source, 1 << x, 1 << y, &mut work).unwrap();
                let mut sparse = source.clone();
                for (mask, coefficient) in change {
                    insert(&mut sparse, mask, coefficient);
                }
                assert_eq!(sparse, result);
                let mut reference = expand(&source);
                reference.substitute(
                    &paths[x],
                    &KernelBooleanPolynomial::variable(paths[x].clone())
                        .xor(&KernelBooleanPolynomial::variable(paths[y].clone())),
                );
                assert_eq!(expand(&result), reference);
            }
        }
        let mut work = WORK_CELLS;
        assert!(transform(&source, 1, 1, &mut work).is_none());
    }
}

#[test]
fn shared_blocks_preserve_every_free_entry_and_refuse_incomplete_work() {
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathBra { term: 1, path: 1 };
    let bit = |v: &KernelVariable| KernelBooleanPolynomial::variable(v.clone());
    let free = (0..4).map(KernelVariable::InputKet).collect::<Vec<_>>();
    let mut source = WorkingTerm {
        paths: BTreeSet::from([x.clone(), y.clone()]),
        constraints: vec![bit(&free[0]).xor(&bit(&free[1]))],
        coefficient: KernelScalar::Rational(ratio(-3, 8)),
        phase: KernelPhasePolynomial::default(),
    };
    for mask in 1..16 {
        let monomial = free
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .fold(KernelBooleanPolynomial::one(), |m, (_, v)| m.and(&bit(v)));
        source.phase.add_boolean(
            &bit(&x).xor(&bit(&y)).and(&monomial),
            PhaseCoefficient::rational(ratio(if mask % 3 == 0 { 3 } else { 1 }, 8)),
        );
    }
    let original = source.phase.clone();
    let mut reduced = source.clone();
    assert_eq!(
        compact(&mut reduced, &mut WORK_CELLS.to_owned()),
        Some(true)
    );
    assert_eq!(reduced.paths, source.paths);
    assert_eq!(reduced.constraints, source.constraints);
    assert_eq!(reduced.coefficient, source.coefficient);
    assert!(reduced.phase.term_count() < original.term_count());
    for input in 0..16 {
        let histogram = |phase: &KernelPhasePolynomial| {
            let mut sum = BTreeMap::<BigRational, usize>::new();
            for assignment in 0..4 {
                let mut point = BTreeMap::from([
                    (x.clone(), assignment & 1 != 0),
                    (y.clone(), assignment & 2 != 0),
                ]);
                point.extend(
                    free.iter()
                        .enumerate()
                        .map(|(i, v)| (v.clone(), input & (1 << i) != 0)),
                );
                let value = phase
                    .terms()
                    .filter(|(m, _)| m.variables().all(|v| point[v]))
                    .map(|(_, c)| c.as_rational().unwrap())
                    .sum::<BigRational>();
                let value = (value % integer(1) + integer(1)) % integer(1);
                *sum.entry(value).or_default() += 1;
            }
            sum
        };
        assert_eq!(histogram(&original), histogram(&reduced.phase));
    }
    let mut refused = source.clone();
    assert_eq!(compact(&mut refused, &mut 0), None);
    assert_eq!(refused.phase, original);
    refused.constraints.push(bit(&x));
    assert_eq!(
        compact(&mut refused, &mut WORK_CELLS.to_owned()),
        Some(false)
    );
    assert_eq!(refused.phase, original);
    let mut missing = source.clone();
    missing.paths.remove(&x);
    assert_eq!(
        compact(&mut missing, &mut WORK_CELLS.to_owned()),
        Some(false)
    );
    let mut scalar = source.clone();
    scalar.coefficient = KernelScalar::Select {
        condition: bit(&y),
        when_true: Box::new(KernelScalar::Rational(integer(1))),
        when_false: Box::new(KernelScalar::Rational(integer(0))),
    };
    assert_eq!(
        compact(&mut scalar, &mut WORK_CELLS.to_owned()),
        Some(false)
    );
}
