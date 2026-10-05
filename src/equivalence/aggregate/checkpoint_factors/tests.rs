use super::super::scalar::ratio;
use super::*;
const WORK_CELLS: usize = 1_000_000;

fn bit(v: &KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v.clone())
}

fn allowance() -> usize {
    WORK_CELLS
}

fn histogram(
    term: &WorkingTerm,
    free: &BTreeMap<KernelVariable, bool>,
) -> BTreeMap<BigRational, BigRational> {
    let paths = term.paths.iter().collect::<Vec<_>>();
    assert!(paths.len() <= 12);
    let KernelScalar::Rational(weight) = &term.coefficient else {
        panic!("rational fixture")
    };
    let mut out = BTreeMap::new();
    for bits in 0..1usize << paths.len() {
        let mut point = free.clone();
        for (i, v) in paths.iter().enumerate() {
            point.insert((*v).clone(), bits & (1 << i) != 0);
        }
        if term.constraints.iter().any(|row| {
            row.terms()
                .filter(|m| m.variables().all(|v| point[v]))
                .count()
                % 2
                != 0
        }) {
            continue;
        }
        let mut phase = integer(0);
        for (m, c) in term.phase.terms() {
            if m.variables().all(|v| point[v]) {
                phase += c.as_rational().unwrap();
            }
        }
        phase = (phase % integer(1) + integer(1)) % integer(1);
        *out.entry(phase).or_insert_with(|| integer(0)) += weight;
    }
    out.retain(|_, v| *v != integer(0));
    out
}

#[test]
fn complete_checkpoint_components_preserve_weighted_all_entry_sums() {
    let [a, b, c, d] = [0, 1, 2, 3].map(|path| KernelVariable::PathKet { term: 3, path });
    let [u, v] = [0, 1].map(KernelVariable::InputBra);
    for code in 0..64usize {
        let mut source = WorkingTerm {
            paths: BTreeSet::from([a.clone(), b.clone(), c.clone(), d.clone()]),
            constraints: vec![bit(&a).xor(&bit(&b)).xor(&bit(&u)), bit(&u).and(&bit(&v))],
            coefficient: KernelScalar::Rational(ratio(code as i64 - 31, 8)),
            phase: KernelPhasePolynomial::default(),
        };
        for (i, p) in [
            bit(&a),
            bit(&b).and(&bit(&u)),
            bit(&c),
            bit(&c).and(&bit(&v)),
            bit(&u),
            KernelBooleanPolynomial::one(),
        ]
        .into_iter()
        .enumerate()
        {
            if code & (1 << i) != 0 {
                source.phase.add_boolean(
                    &p,
                    crate::symbolic::PhaseCoefficient::rational(ratio(i as i64 + 1, 8)),
                );
            }
        }
        let factors = components(&source, &mut allowance()).unwrap();
        for free_bits in 0..4 {
            let free = BTreeMap::from([
                (u.clone(), free_bits & 1 != 0),
                (v.clone(), free_bits & 2 != 0),
            ]);
            let mut product = BTreeMap::from([(integer(0), integer(1))]);
            for factor in factors.iter() {
                let mut next = BTreeMap::new();
                for (p, a) in &product {
                    for (q, b) in histogram(factor, &free) {
                        let r = (p + q) % integer(1);
                        *next.entry(r).or_insert_with(|| integer(0)) += a * b;
                    }
                }
                next.retain(|_, v| *v != integer(0));
                product = next;
            }
            assert_eq!(
                histogram(&source, &free),
                product,
                "code={code} free={free_bits}"
            );
        }
    }
}

#[test]
fn checkpoint_component_premises_budget_and_later_dependencies_are_complete() {
    let paths = (0..520)
        .map(|path| KernelVariable::PathBra { term: 2, path })
        .collect::<Vec<_>>();
    let mut source = WorkingTerm {
        paths: paths.iter().cloned().collect(),
        constraints: vec![bit(&paths[519])],
        coefficient: KernelScalar::Rational(ratio(-3, 8)),
        phase: KernelPhasePolynomial::default(),
    };
    source.phase.add_boolean(
        &bit(&paths[0]),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    let mut work = WORK_CELLS;
    let factors = components(&source, &mut work).unwrap();
    assert_eq!(factors.len(), 3);
    assert_eq!(
        factors[0].coefficient,
        KernelScalar::Rational(ratio(-3, 8) * BigRational::from_integer(BigInt::from(1) << 518))
    );
    assert_eq!(
        factors
            .iter()
            .flat_map(|f| f.paths.iter().cloned())
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([paths[0].clone(), paths[519].clone()])
    );
    assert!(components(&source, &mut (WORK_CELLS - work - 1)).is_none());
    assert_eq!(source.paths.len(), 520);
    assert_eq!(source.constraints, vec![bit(&paths[519])]);
    assert_eq!(source.coefficient, KernelScalar::Rational(ratio(-3, 8)));
    let mut bad = source.clone();
    bad.coefficient = KernelScalar::Select {
        condition: KernelBooleanPolynomial::one(),
        when_true: Box::new(KernelScalar::Rational(integer(1))),
        when_false: Box::new(KernelScalar::Select {
            condition: bit(&paths[519]),
            when_true: Box::new(KernelScalar::Rational(integer(1))),
            when_false: Box::new(KernelScalar::Rational(integer(2))),
        }),
    };
    assert!(connectivity(&bad).is_none());
    bad = source.clone();
    bad.paths.remove(&paths[519]);
    assert!(components(&bad, &mut allowance()).is_none());
    bad = source.clone();
    bad.constraints = vec![KernelBooleanPolynomial::from_monomial(
        KernelMonomial::from_variables(paths[..33].iter().cloned()),
    )];
    assert!(components(&bad, &mut allowance()).is_none());
    bad = source.clone();
    bad.constraints.clear();
    for path in &paths[1..129] {
        bad.phase.add_boolean(
            &bit(path),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    assert!(components(&bad, &mut allowance()).is_none());
    bad = source;
    bad.coefficient = KernelScalar::Rational(BigRational::from_integer(BigInt::from(1) << 32768));
    assert!(components(&bad, &mut allowance()).is_none());
}

#[test]
fn complete_connectivity_joins_whole_guards_but_not_shared_free_variables() {
    let [a, b, c, d] = [0, 1, 2, 3].map(|path| KernelVariable::PathKet { term: 0, path });
    let u = KernelVariable::QuantumOutputKet(0);
    let bit = |v: &KernelVariable| KernelBooleanPolynomial::variable(v.clone());
    let mut source = WorkingTerm {
        paths: BTreeSet::from([a.clone(), b.clone(), c.clone(), d.clone()]),
        constraints: vec![bit(&a).xor(&bit(&b))],
        coefficient: KernelScalar::Rational(integer(3)),
        phase: KernelPhasePolynomial::default(),
    };
    for v in [&a, &c] {
        source.phase.add_boolean(
            &bit(v).and(&bit(&u)),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    let result = connectivity(&source).unwrap();
    assert_eq!(result.vacuous, 1);
    assert_eq!(result.groups.len(), 2);
    assert_eq!(
        result.owners[result.positions[&a]],
        result.owners[result.positions[&b]]
    );
    assert_ne!(
        result.owners[result.positions[&a]],
        result.owners[result.positions[&c]]
    );
    source.paths.remove(&b);
    assert!(connectivity(&source).is_none());
}

fn chained_source(groups: usize) -> WorkingTerm {
    let free = KernelVariable::InputKet(0);
    let mut source = WorkingTerm {
        paths: BTreeSet::new(),
        constraints: vec![bit(&KernelVariable::InputBra(0))],
        coefficient: KernelScalar::Rational(ratio(-3, 8)),
        phase: KernelPhasePolynomial::default(),
    };
    for group in 0..groups {
        let paths: Vec<_> = (0..9)
            .map(|path| KernelVariable::PathKet { term: group, path })
            .collect();
        source.constraints.push(bit(&paths[0]).xor(&bit(&free)));
        for pair in paths.windows(2) {
            source.constraints.push(bit(&pair[0]).xor(&bit(&pair[1])));
        }
        source.phase.add_boolean(
            &bit(&paths[8]),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        source.paths.extend(paths);
    }
    source
}

// Use the already-audited unique-solution substitution. Unlike a branch sum,
// this removes one determined binder without changing its weight.
fn reduce_aliases(mut term: WorkingTerm) -> Option<WorkingTerm> {
    while let Some((path, replacement)) = term.best_constraint_pivot() {
        term.substitute(&path, &replacement);
        term.paths.remove(&path);
    }
    Some(term)
}

fn product_histogram(
    factors: &[WorkingTerm],
    free: &BTreeMap<KernelVariable, bool>,
) -> BTreeMap<BigRational, BigRational> {
    let mut product = BTreeMap::from([(integer(0), integer(1))]);
    for factor in factors {
        let mut next = BTreeMap::new();
        for (p, a) in &product {
            for (q, b) in histogram(factor, free) {
                *next
                    .entry((p + q) % integer(1))
                    .or_insert_with(|| integer(0)) += a * b;
            }
        }
        next.retain(|_, v| *v != integer(0));
        product = next;
    }
    product
}

#[test]
fn local_substitution_preserves_the_complete_product_at_every_free_input() {
    let mut source = chained_source(1);
    // One absent path contributes two, once in the common coefficient.
    source
        .paths
        .insert(KernelVariable::PathBra { term: 4, path: 0 });
    let small = KernelVariable::PathBra { term: 4, path: 1 };
    source.paths.insert(small.clone());
    source.phase.add_boolean(
        &bit(&small).and(&bit(&KernelVariable::InputKet(0))),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 4)),
    );
    let factors = components(&source, &mut allowance()).unwrap();
    let result = reduce_components(factors, &mut allowance(), reduce_aliases).unwrap();
    for bits in 0..4 {
        let free = BTreeMap::from([
            (KernelVariable::InputKet(0), bits & 1 != 0),
            (KernelVariable::InputBra(0), bits & 2 != 0),
        ]);
        assert_eq!(histogram(&source, &free), product_histogram(&result, &free));
    }
}

#[test]
fn late_refusal_never_returns_the_successfully_reduced_prefix() {
    let source = chained_source(2);
    let factors = components(&source, &mut allowance()).unwrap();
    let mut calls = 0;
    assert!(
        reduce_components(factors, &mut allowance(), |factor| {
            calls += 1;
            if calls == 1 {
                reduce_aliases(factor)
            } else {
                None
            }
        })
        .is_none()
    );
    assert_eq!(calls, 2);
    // A complete result which remains too wide is not a successful reduction.
    let factors = components(&source, &mut allowance()).unwrap();
    assert!(reduce_components(factors, &mut allowance(), Some).is_none());
}

#[test]
fn work_exhaustion_returns_no_partial_factor_list() {
    let source = chained_source(2);
    let mut work = allowance();
    let factors = components(&source, &mut work).unwrap();
    let mut reduce_work = allowance();
    let expected = reduce_components(factors.clone(), &mut reduce_work, reduce_aliases).unwrap();
    let required = allowance() - reduce_work;
    assert!(required > 1);
    for mut budget in 0..required {
        assert!(reduce_components(factors.clone(), &mut budget, reduce_aliases).is_none());
    }
    let mut exact_budget = required;
    let result = reduce_components(factors, &mut exact_budget, reduce_aliases).unwrap();
    assert_eq!(result.len(), expected.len());
    let mut zero = 0;
    assert!(components(&source, &mut zero).is_none());
}

#[test]
fn graph_only_fields_and_unowned_paths_refuse_the_entire_plan() {
    let source = chained_source(1);
    let graph = KernelBooleanPolynomial::from_graph(
        bit(&KernelVariable::InputKet(0)).as_graph().and(
            &bit(source.paths.iter().next().unwrap())
                .as_graph()
                .xor(&bit(&KernelVariable::InputBra(0)).as_graph()),
        ),
    );
    assert!(!graph.is_algebraic());
    let mut bad = source.clone();
    bad.constraints.push(graph.clone());
    assert!(components(&bad, &mut allowance()).is_none());
    bad = source.clone();
    bad.phase.add_boolean(
        &graph,
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    assert!(components(&bad, &mut allowance()).is_none());
    bad = source;
    bad.paths.insert(KernelVariable::InputKet(8));
    assert!(components(&bad, &mut allowance()).is_none());
}
use crate::equivalence::kernel::KernelBooleanPolynomial;
