use super::*;

fn simple_term(paths: usize) -> WorkingTerm {
    WorkingTerm {
        paths: (0..paths)
            .map(|path| KernelVariable::PathKet { term: 0, path })
            .collect(),
        constraints: vec![],
        coefficient: KernelScalar::Rational(integer(3)),
        phase: KernelPhasePolynomial::default(),
    }
}

#[test]
fn unused_binders_contribute_multiplicity_without_summing_free_inputs() {
    let x = KernelVariable::InputKet(0);
    for paths in 1..=3 {
        let mut source = simple_term(paths);
        source
            .phase
            .add_boolean(&bit(&x), PhaseCoefficient::rational(ratio(1, 8)));
        let actual = sum(&source, &mut budget()).unwrap();
        assert_eq!(actual.len(), 1);
        assert_eq!(actual.values().next().unwrap().len(), 1);
        let (p, c) = actual.values().next().unwrap().first_key_value().unwrap();
        assert_eq!(p, &source.phase);
        assert_eq!(c, &KernelScalar::Rational(integer(3 * (1i64 << paths))));
        check_all_free(&source, &[x.clone()]);
    }
}

#[test]
fn a_difference_in_the_last_free_phase_block_prevents_leaf_merging() {
    let a = KernelVariable::PathKet { term: 0, path: 0 };
    let x = KernelVariable::InputKet(0);
    let z = KernelVariable::QuantumOutputBra(3);
    let mut source = simple_term(1);
    source
        .phase
        .add_boolean(&bit(&x), PhaseCoefficient::rational(ratio(1, 4)));
    source.phase.add_boolean(
        &bit(&z).and(&bit(&a)),
        PhaseCoefficient::rational(ratio(1, 4)),
    );
    check_all_free(&source, &[x, z]);
    assert_eq!(
        sum(&source, &mut budget())
            .unwrap()
            .values()
            .map(BTreeMap::len)
            .sum::<usize>(),
        2
    );
}

#[test]
fn nonzero_sums_refuse_every_incomplete_work_budget_and_share_split_budget() {
    let a = KernelVariable::PathKet { term: 0, path: 0 };
    let x = KernelVariable::InputKet(0);
    let mut source = simple_term(1);
    source.phase.add_boolean(
        &bit(&a).and(&bit(&x)),
        PhaseCoefficient::rational(ratio(1, 8)),
    );
    let mut measured = budget();
    let expected = sum(&source, &mut measured).unwrap();
    let used = MAX_FACTOR_PHASE_CELLS - measured.phase_cells;
    for cells in 0..used {
        let mut limited = budget();
        limited.phase_cells = cells;
        assert!(sum(&source, &mut limited).is_none());
    }
    let mut exact = budget();
    exact.phase_cells = used;
    assert_eq!(sum(&source, &mut exact).unwrap(), expected);
    let mut shared = budget();
    shared.splits = 1;
    assert_eq!(sum(&source, &mut shared).unwrap(), expected);
    assert!(sum(&source, &mut shared).is_none());
    check_all_free(&source, &[x]);
}

#[test]
fn undeclared_bound_variables_and_graph_only_fields_are_refused() {
    let a = KernelVariable::PathBra { term: 7, path: 0 };
    let mut source = simple_term(1);
    source
        .phase
        .add_boolean(&bit(&a), PhaseCoefficient::rational(ratio(1, 4)));
    assert!(!admitted(&source));
    assert!(sum(&source, &mut budget()).is_none());

    let x = bit(&KernelVariable::InputKet(0)).as_graph();
    let y = bit(&KernelVariable::InputKet(1)).as_graph();
    let z = bit(&KernelVariable::InputKet(2)).as_graph();
    let graph = KernelBooleanPolynomial::from_graph(x.and(&y.xor(&z)));
    assert!(!graph.is_algebraic());
    for field in 0..3 {
        let mut source = simple_term(1);
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
        assert!(sum(&source, &mut budget()).is_none());
    }
}

#[test]
fn scalar_add_mul_neg_and_select_are_preserved_pointwise() {
    let x = KernelVariable::InputBra(0);
    let a = KernelVariable::PathKet { term: 0, path: 0 };
    let mut source = simple_term(2);
    source.constraints = vec![bit(&x)];
    source.coefficient = KernelScalar::Mul(
        Box::new(KernelScalar::Neg(Box::new(KernelScalar::Rational(ratio(
            2, 3,
        ))))),
        Box::new(KernelScalar::Add(
            Box::new(KernelScalar::Rational(integer(5))),
            Box::new(KernelScalar::Select {
                condition: bit(&x),
                when_true: Box::new(KernelScalar::Rational(integer(-2))),
                when_false: Box::new(KernelScalar::Rational(integer(3))),
            }),
        )),
    );
    source
        .phase
        .add_boolean(&bit(&a), PhaseCoefficient::rational(ratio(1, 8)));
    check_all_free(&source, &[x.clone()]);
    source.constraints.clear();
    check_all_free(&source, &[x]);
}
use super::super::KernelBooleanPolynomial;
use num_bigint::BigInt;
use num_rational::BigRational;
const MAX_FACTOR_PHASE_CELLS: usize = 250_000;
struct TestBudget {
    splits: usize,
    phase_cells: usize,
}
fn sum(source: &WorkingTerm, budget: &mut TestBudget) -> Option<ExactAggregate> {
    super::sum(source, &mut budget.splits, &mut budget.phase_cells)
}

fn budget() -> TestBudget {
    TestBudget {
        splits: 4095,
        phase_cells: MAX_FACTOR_PHASE_CELLS,
    }
}

fn bit(v: &KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v.clone())
}

fn boolean(p: &KernelBooleanPolynomial, values: &BTreeMap<KernelVariable, bool>) -> bool {
    p.terms()
        .filter(|m| m.variables().all(|v| values[v]))
        .count()
        % 2
        != 0
}

fn scalar(s: &KernelScalar, values: &BTreeMap<KernelVariable, bool>) -> BigRational {
    match s {
        KernelScalar::Rational(r) => r.clone(),
        KernelScalar::Neg(a) => -scalar(a, values),
        KernelScalar::Add(a, b) => scalar(a, values) + scalar(b, values),
        KernelScalar::Mul(a, b) => scalar(a, values) * scalar(b, values),
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => scalar(
            if boolean(condition, values) {
                when_true
            } else {
                when_false
            },
            values,
        ),
        _ => panic!("fixture scalar outside rational grammar"),
    }
}

// Literal Q[z]/(z^4+1) accumulation, without production substitution,
// local reduction, leaf construction or the production field evaluator.
fn add_value(
    result: &mut [BigRational; 4],
    phase: &KernelPhasePolynomial,
    weight: BigRational,
    values: &BTreeMap<KernelVariable, bool>,
) {
    let turns: BigRational = phase
        .terms()
        .filter(|(m, _)| m.variables().all(|v| values[v]))
        .map(|(_, c)| c.as_rational().unwrap())
        .sum();
    let eighths = turns * integer(8);
    assert!(eighths.is_integer());
    let power: usize = (eighths.to_integer() % BigInt::from(8)).try_into().unwrap();
    result[power % 4] += if power < 4 { weight } else { -weight };
}

fn check_all_free(source: &WorkingTerm, free: &[KernelVariable]) {
    let actual = sum(source, &mut budget()).unwrap();
    for input in 0..(1 << free.len()) {
        let mut values = free
            .iter()
            .enumerate()
            .map(|(i, v)| (v.clone(), input & (1 << i) != 0))
            .collect::<BTreeMap<_, _>>();
        let mut expected = std::array::from_fn(|_| integer(0));
        for assignment in 0..(1 << source.paths.len()) {
            for (i, v) in source.paths.iter().enumerate() {
                values.insert(v.clone(), assignment & (1 << i) != 0);
            }
            if source.constraints.iter().all(|g| !boolean(g, &values)) {
                add_value(
                    &mut expected,
                    &source.phase,
                    scalar(&source.coefficient, &values),
                    &values,
                );
            }
        }
        let mut got = std::array::from_fn(|_| integer(0));
        for (entry, coefficients) in &actual {
            if entry.constraints.iter().all(|g| !boolean(g, &values)) {
                for (p, c) in coefficients {
                    assert!(!p.variables().iter().any(KernelVariable::is_bound_path));
                    add_value(&mut got, p, scalar(c, &values), &values);
                }
            }
        }
        assert_eq!(got, expected);
    }
}

#[test]
fn projected_free_keys_compare_complete_values_not_source_addresses() {
    let vars = [
        KernelVariable::InputKet(0),
        KernelVariable::QuantumOutputBra(0),
        KernelVariable::PathKet { term: 0, path: 0 },
        KernelVariable::PathBra { term: 1, path: 0 },
        KernelVariable::PathKet { term: 2, path: 1 },
    ];
    let monomials = (0..32)
        .map(|mask| {
            KernelMonomial::from_variables(
                vars.iter()
                    .enumerate()
                    .filter(|(i, _)| mask & (1 << i) != 0)
                    .map(|(_, v)| v.clone()),
            )
        })
        .collect::<Vec<_>>();
    for a in &monomials {
        for b in &monomials {
            let project = |m: &KernelMonomial| {
                KernelMonomial::from_variables(
                    m.variables().filter(|v| !v.is_bound_path()).cloned(),
                )
            };
            assert_eq!(FreeKey(a).cmp(&FreeKey(b)), project(a).cmp(&project(b)));
            assert_eq!(FreeKey(a) == FreeKey(b), project(a) == project(b));
        }
    }
}

#[test]
fn shared_small_sum_matches_complete_weighted_guarded_entries() {
    let x = KernelVariable::InputKet(0);
    let y = KernelVariable::QuantumOutputBra(0);
    let a = KernelVariable::PathKet { term: 0, path: 0 };
    let b = KernelVariable::PathBra { term: 1, path: 0 };
    let absent = KernelVariable::PathKet { term: 7, path: 0 };
    for table in 0..256 {
        let mut source = WorkingTerm {
            paths: BTreeSet::from([a.clone(), b.clone(), absent.clone()]),
            constraints: vec![
                bit(&x)
                    .and(&bit(&y))
                    .xor(&KernelBooleanPolynomial::from(table & 1 != 0)),
            ],
            coefficient: KernelScalar::Select {
                condition: bit(&y),
                when_true: Box::new(KernelScalar::Rational(integer(-3))),
                when_false: Box::new(KernelScalar::Rational(integer(5))),
            },
            phase: KernelPhasePolynomial::default(),
        };
        // Repeated COMPLETE mask patterns for x and y, with every two-bit
        // pattern over eighth-turn coefficients in {0,1,2,3}/8.
        for f in [&x, &y] {
            for mask in 0..4 {
                let mut variables = vec![f.clone()];
                if mask & 1 != 0 {
                    variables.push(a.clone());
                }
                if mask & 2 != 0 {
                    variables.push(b.clone());
                }
                source.phase.add_term(
                    KernelMonomial::from_variables(variables),
                    PhaseCoefficient::rational(ratio(((table >> (2 * mask)) & 3) as i64, 8)),
                );
            }
        }
        source.phase.add_boolean(
            &bit(&a).and(&bit(&b)),
            PhaseCoefficient::rational(ratio(1, 2)),
        );
        source.phase.add_boolean(
            &KernelBooleanPolynomial::one(),
            PhaseCoefficient::rational(ratio(3, 4)),
        );
        check_all_free(&source, &[x.clone(), y.clone()]);
        // Almost identical patterns must not share the wrong leaf table.
        source.phase.add_boolean(
            &bit(&y).and(&bit(&a)),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
        check_all_free(&source, &[x.clone(), y.clone()]);
        // Also exercise all three genuinely active bound coordinates,
        // not only the duplicate leaves induced by the absent binder.
        source.phase.add_boolean(
            &bit(&absent).and(&bit(&a)).and(&bit(&x)),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
        check_all_free(&source, &[x.clone(), y.clone()]);
    }
}

#[test]
fn shared_small_sum_requires_all_binders_fields_and_work() {
    let a = KernelVariable::PathKet { term: 0, path: 0 };
    let x = KernelVariable::InputBra(0);
    let mut source = WorkingTerm {
        paths: BTreeSet::from([a.clone()]),
        constraints: vec![bit(&x)],
        coefficient: KernelScalar::Rational(integer(3)),
        phase: KernelPhasePolynomial::default(),
    };
    source
        .phase
        .add_boolean(&bit(&a), PhaseCoefficient::rational(ratio(1, 2)));
    assert!(sum(&source, &mut budget()).unwrap().is_empty());
    let mut changed = source.clone();
    changed
        .phase
        .add_boolean(&bit(&a), PhaseCoefficient::rational(ratio(1, 4)));
    assert!(!sum(&changed, &mut budget()).unwrap().is_empty());
    let mut changed = source.clone();
    changed.paths.clear();
    assert!(sum(&changed, &mut budget()).is_none());
    let mut changed = source.clone();
    changed.paths.insert(x.clone());
    assert!(sum(&changed, &mut budget()).is_none());
    let mut changed = source.clone();
    changed.constraints.push(bit(&a));
    assert!(sum(&changed, &mut budget()).is_none());
    let mut changed = source.clone();
    changed.coefficient = KernelScalar::Select {
        condition: bit(&x),
        when_true: Box::new(KernelScalar::Rational(integer(1))),
        when_false: Box::new(KernelScalar::Select {
            condition: bit(&a),
            when_true: Box::new(KernelScalar::Rational(integer(2))),
            when_false: Box::new(KernelScalar::Rational(integer(3))),
        }),
    };
    assert!(sum(&changed, &mut budget()).is_none());
    for path in 1..4 {
        changed
            .paths
            .insert(KernelVariable::PathBra { term: 1, path });
    }
    assert!(sum(&changed, &mut budget()).is_none());
    let mut changed = source.clone();
    changed.phase.add_boolean(
        &bit(&x),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(1) << 257)),
    );
    assert!(sum(&changed, &mut budget()).is_none());
    let mut measured = budget();
    sum(&source, &mut measured).unwrap();
    let used = MAX_FACTOR_PHASE_CELLS - measured.phase_cells;
    for cells in 0..used {
        let mut limited = budget();
        limited.phase_cells = cells;
        assert!(sum(&source, &mut limited).is_none());
        assert!(limited.phase_cells <= cells);
    }
    let mut exact = budget();
    exact.phase_cells = used;
    assert!(sum(&source, &mut exact).unwrap().is_empty());
    let mut limited = budget();
    limited.splits = 0;
    assert!(sum(&source, &mut limited).is_none());
    check_all_free(&source, &[x]);
}
