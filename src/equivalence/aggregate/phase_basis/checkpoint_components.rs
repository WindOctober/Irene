//! Complete component checkpoints without reconstructing an oversized monolith.
use super::*;

#[derive(Default, Debug, PartialEq, Eq)]
struct Shape {
    paths: usize,
    rows: usize,
    phase_terms: usize,
    cells: usize,
}

struct Connectivity<'a> {
    positions: BTreeMap<&'a KernelVariable, usize>,
    owners: Vec<usize>,
    groups: BTreeMap<usize, Shape>,
    common: Shape,
    vacuous: usize,
}

fn root(parents: &mut [usize], mut index: usize) -> usize {
    while parents[index] != index {
        parents[index] = parents[parents[index]];
        index = parents[index];
    }
    index
}

fn connectivity(source: &WorkingTerm) -> Option<Connectivity<'_>> {
    if !checkpoint_admitted(source)
        || !scalar_conditions_within_budget(&source.coefficient, |row| {
            row.terms()
                .flat_map(KernelMonomial::variables)
                .all(|v| !v.is_bound_path())
        })
    {
        return None;
    }
    let positions = source
        .paths
        .iter()
        .enumerate()
        .map(|(i, v)| (v, i))
        .collect::<BTreeMap<_, _>>();
    let mut parents = (0..positions.len()).collect::<Vec<_>>();
    let mut active = BTreeSet::new();
    let mut connect = |variables: Vec<&KernelVariable>| {
        let mut first = None;
        for v in variables {
            let Some(&position) = positions.get(v) else {
                continue;
            };
            active.insert(position);
            let current = root(&mut parents, position);
            if let Some(previous) = first {
                let previous = root(&mut parents, previous);
                parents[current] = previous;
            } else {
                first = Some(current);
            }
        }
    };
    // A whole XOR guard is ONE hyperedge, never separate monomial guards.
    for row in &source.constraints {
        connect(row.terms().flat_map(KernelMonomial::variables).collect());
    }
    for (m, _) in source.phase.terms() {
        connect(m.variables().collect());
    }
    let owners = (0..positions.len())
        .map(|i| root(&mut parents, i))
        .collect::<Vec<_>>();
    let mut groups = BTreeMap::<usize, Shape>::new();
    for &i in &active {
        let shape = groups.entry(owners[i]).or_default();
        shape.paths += 1;
        shape.cells += 1;
    }
    let mut common = Shape::default();
    for row in &source.constraints {
        let owner = row
            .terms()
            .flat_map(KernelMonomial::variables)
            .find_map(|v| positions.get(v))
            .map(|&i| owners[i]);
        let shape = match owner {
            Some(i) => groups.get_mut(&i)?,
            None => &mut common,
        };
        shape.rows += 1;
        shape.cells += row
            .terms()
            .map(|m| 1 + m.variables().count())
            .sum::<usize>();
    }
    for (m, _) in source.phase.terms() {
        let owner = m
            .variables()
            .find_map(|v| positions.get(v))
            .map(|&i| owners[i]);
        let shape = match owner {
            Some(i) => groups.get_mut(&i)?,
            None => &mut common,
        };
        shape.phase_terms += 1;
        shape.cells += 1 + m.variables().count();
    }
    Some(Connectivity {
        positions,
        owners,
        groups,
        common,
        vacuous: source.paths.len() - active.len(),
    })
}

pub(super) fn matches(left: &WorkingTerm, right: &WorkingTerm) -> bool {
    if !crate::ablation::permit(crate::ablation::Group::PathSumPlanning) {
        return false;
    }
    let mut work = WORK_CELLS;
    let result = (|| {
        let left = components(left, &mut work)?;
        let right = components(right, &mut work)?;
        let left = reduce_components(left, &mut work)?;
        let right = reduce_components(right, &mut work)?;
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "aggregate checkpoint components complete: left={} right={} work={work}",
                left.len(),
                right.len()
            );
        }
        Some(factored::matches_components_refined(left, right, true))
    })();
    if result != Some(true) && std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!("aggregate checkpoint components proof refused: work={work}");
    }
    result == Some(true)
}

fn local_cells(term: &WorkingTerm) -> Option<usize> {
    let mut cells = term.paths.len();
    let mut inspect = |m: &KernelMonomial| {
        cells += 1 + m.variables().count();
        cells <= 32768
    };
    (term.constraints.iter().all(|r| r.terms().all(&mut inspect))
        && term.phase.terms().all(|(m, _)| inspect(m))
        && scalar_conditions_within_budget(&term.coefficient, |r| r.terms().all(&mut inspect)))
    .then_some(cells)
}

/// Every local reduction must finish: never salvage a Residual or discard a
/// later factor. Ordinary reduction retains its original rewrite preflights.
/// Each source has <=32binders/32768cells, so local elimination has at most
///32 binder-removing rounds plus the existing finite recovery probes.
fn reduce_components(factors: Components, work: &mut usize) -> Option<Vec<WorkingTerm>> {
    let mut result = Vec::with_capacity(factors.len());
    for factor in factors.0 {
        if factor.paths.len() <= MAX_SPLIT_DEPTH {
            result.push(factor);
            continue;
        }
        // The private constructor already validated and charged the COMPLETE
        // input syntax. Consume that admission without rescanning its keys.
        // The local reducer still has all its own rewrite/preflight limits.
        charge(work, 1)?;
        let before = (
            factor.paths.len(),
            factor.constraints.len(),
            factor.phase.term_count(),
        );
        let mut factor = match reduce_working_term(factor) {
            Reduction::Sum(term) => *term,
            Reduction::Exact(term) => WorkingTerm {
                paths: BTreeSet::new(),
                constraints: term.constraints,
                coefficient: term.coefficient,
                phase: term.phase,
            },
            // Even an exact zero is conservatively refused here; the existing
            // product path remains the sole owner of zero-product handling.
            Reduction::Zero | Reduction::Residual => return None,
        };
        if local_cells(&factor).is_none() && factor.paths.len() == 4 {
            // A COMPLETE local result, never Residual/prefix recovery. Reuse
            // the remaining compaction allowance for a full four-bit period
            // certificate; every original scalar/guard and later factor stays.
            let compacted = pair_period::compact_four(&mut factor, work);
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "aggregate checkpoint four-bit period: result={compacted:?} paths={} terms={} work={work}",
                    factor.paths.len(),
                    factor.phase.term_count()
                );
            }
            if compacted != Some(true) {
                return None;
            }
        }
        charge(work, local_cells(&factor)?)?;
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "aggregate checkpoint component reduction: before={before:?} after={:?} work={work}",
                (
                    factor.paths.len(),
                    factor.constraints.len(),
                    factor.phase.term_count()
                )
            );
        }
        if factor.paths.len() > MAX_SPLIT_DEPTH {
            return None;
        }
        result.push(factor);
    }
    Some(result)
}

/// Complete bounded construction from the borrowed plan. No absent-binder
/// dummy factors and no intermediate whole-phase reconstruction.
#[derive(Clone)]
struct Components(Vec<WorkingTerm>);

impl std::ops::Deref for Components {
    type Target = [WorkingTerm];
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

fn components(source: &WorkingTerm, work: &mut usize) -> Option<Components> {
    let plan = connectivity(source)?;
    let KernelScalar::Rational(weight) = &source.coefficient else {
        return None;
    };
    if weight.numer().bits() > 32768
        || weight.denom().bits() > 32768
        || plan.groups.len() > 128
        || plan.common.cells > 32768
        || plan
            .groups
            .values()
            .any(|s| s.paths > 32 || s.cells > 32768)
    {
        return None;
    }
    // Entire syntax to copy, path-reference plan, and exact multiplicity bits.
    // The separate read-only source admission is already bounded at750000.
    charge(
        work,
        plan.positions.len()
            + plan.common.cells
            + plan.groups.values().map(|s| s.cells).sum::<usize>()
            + plan.vacuous.div_ceil(64),
    )?;
    let unit = || WorkingTerm {
        paths: BTreeSet::new(),
        constraints: Vec::new(),
        coefficient: KernelScalar::Rational(integer(1)),
        phase: KernelPhasePolynomial::default(),
    };
    let mut groups = plan
        .groups
        .keys()
        .map(|&id| (id, unit()))
        .collect::<BTreeMap<_, _>>();
    for (v, &i) in &plan.positions {
        if let Some(group) = groups.get_mut(&plan.owners[i]) {
            group.paths.insert((*v).clone());
        }
    }
    let mut common = unit();
    common.coefficient =
        KernelScalar::Rational(weight * BigRational::from_integer(BigInt::from(1) << plan.vacuous));
    for row in &source.constraints {
        let owner = row
            .terms()
            .flat_map(KernelMonomial::variables)
            .find_map(|v| plan.positions.get(v))
            .map(|&i| plan.owners[i]);
        match owner {
            Some(id) => groups.get_mut(&id)?.constraints.push(row.clone()),
            None => common.constraints.push(row.clone()),
        }
    }
    for (m, c) in source.phase.terms() {
        let owner = m
            .variables()
            .find_map(|v| plan.positions.get(v))
            .map(|&i| plan.owners[i]);
        let target = match owner {
            Some(id) => &mut groups.get_mut(&id)?.phase,
            None => &mut common.phase,
        };
        target.add_term(m.clone(), c.clone());
    }
    Some(Components(
        std::iter::once(common)
            .chain(groups.into_values())
            .collect(),
    ))
}

#[cfg(test)]
mod tests {
    use super::*;

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
        assert!(paths.len() <= 8);
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
    fn complete_component_output_period_keeps_common_fields_and_refuses_a_late_factor() {
        use crate::symbolic::PhaseCoefficient;
        let [x, y, z, w] = [0, 1, 2, 3].map(|path| KernelVariable::PathKet { term: 7, path });
        let mut source = WorkingTerm {
            paths: BTreeSet::from([x.clone(), y.clone(), z.clone(), w.clone()]),
            constraints: vec![],
            coefficient: KernelScalar::Rational(integer(1)),
            phase: KernelPhasePolynomial::default(),
        };
        let mut expected = KernelPhasePolynomial::default();
        for (v, c) in [(&z, 1), (&w, 3)] {
            source
                .phase
                .add_boolean(&bit(v), PhaseCoefficient::rational(ratio(c, 8)));
            expected.add_boolean(&bit(v), PhaseCoefficient::rational(ratio(c, 8)));
        }
        for i in 0..24 {
            let alias = KernelVariable::PathBra { term: 7, path: i };
            let rhs = bit(&KernelVariable::InputKet(2 * i))
                .xor(&bit(&KernelVariable::InputKet(2 * i + 1)));
            source.paths.insert(alias.clone());
            source.constraints.push(bit(&alias).xor(&rhs));
            for j in 0..40 {
                let free = bit(&KernelVariable::InputBra(i * 40 + j));
                source.phase.add_boolean(
                    &bit(&alias).and(&bit(&x).xor(&bit(&y))).and(&free),
                    PhaseCoefficient::rational(ratio(1, 8)),
                );
                expected.add_boolean(
                    &rhs.and(&bit(&x)).and(&free),
                    PhaseCoefficient::rational(ratio(1, 8)),
                );
            }
        }
        assert!(local_cells(&source).is_some());
        let Reduction::Sum(reduced) = reduce_working_term(source.clone()) else {
            panic!("complete four-bit local sum");
        };
        assert_eq!(reduced.paths.len(), 4);
        assert!(local_cells(&reduced).is_none());
        let mut common = WorkingTerm {
            paths: BTreeSet::new(),
            constraints: vec![bit(&KernelVariable::ClassicalOutput(0))],
            coefficient: KernelScalar::Rational(integer(-3)),
            phase: KernelPhasePolynomial::default(),
        };
        common.phase.add_boolean(
            &bit(&KernelVariable::InputKet(9)),
            PhaseCoefficient::rational(ratio(3, 8)),
        );
        let result = reduce_components(
            Components(vec![common.clone(), source.clone()]),
            &mut allowance(),
        )
        .unwrap();
        assert_eq!(result.len(), 2);
        assert_eq!(result[0].paths, common.paths);
        assert_eq!(result[0].constraints, common.constraints);
        assert_eq!(result[0].coefficient, common.coefficient);
        assert_eq!(result[0].phase, common.phase);
        assert_eq!(result[1].paths, BTreeSet::from([x, z, w]));
        assert!(result[1].constraints.is_empty());
        assert_eq!(result[1].coefficient, KernelScalar::Rational(integer(2)));
        assert_eq!(result[1].phase, expected);
        let mut late = WorkingTerm {
            paths: BTreeSet::new(),
            constraints: vec![],
            coefficient: KernelScalar::Rational(integer(1)),
            phase: KernelPhasePolynomial::default(),
        };
        for path in 0..9 {
            let v = KernelVariable::PathBra { term: 99, path };
            late.paths.insert(v.clone());
            late.phase
                .add_boolean(&bit(&v), PhaseCoefficient::rational(ratio(1, 8)));
        }
        assert!(
            reduce_components(Components(vec![common, source, late]), &mut allowance()).is_none()
        );
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
            KernelScalar::Rational(
                ratio(-3, 8) * BigRational::from_integer(BigInt::from(1) << 518)
            )
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
        bad.coefficient =
            KernelScalar::Rational(BigRational::from_integer(BigInt::from(1) << 32768));
        assert!(components(&bad, &mut allowance()).is_none());
    }

    #[test]
    fn checkpoint_component_product_checks_every_factor_and_common_field() {
        let u = KernelVariable::InputKet(0);
        let mut left = WorkingTerm {
            paths: (0..530)
                .map(|path| KernelVariable::PathKet { term: 4, path })
                .collect(),
            constraints: vec![bit(&u)],
            coefficient: KernelScalar::Rational(BigRational::new(
                BigInt::from(1),
                BigInt::from(1) << 395,
            )),
            phase: KernelPhasePolynomial::default(),
        };
        //27 disconnected ten-bit chains, each exactly32, and260 absent bits.
        // Independent ALL1024 phase evaluations in Q[zeta8] establish32,
        // rather than asking the production local reducer to certify itself.
        let mut exact = [0i64; 4];
        for bits in 0..1024usize {
            let edges = (0..9).filter(|&i| bits & (3 << i) == 3 << i).count();
            let power = (4 * edges + usize::from(bits & 512 != 0)) % 8;
            exact[power % 4] += if power < 4 { 1 } else { -1 };
        }
        assert_eq!(exact, [32, 0, 0, 0]);
        for group in 0..27 {
            let paths = (0..10)
                .map(|i| KernelVariable::PathKet {
                    term: 4,
                    path: group * 10 + i,
                })
                .collect::<Vec<_>>();
            for pair in paths.windows(2) {
                left.phase.add_boolean(
                    &bit(&pair[0]).and(&bit(&pair[1])),
                    crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
                );
            }
            left.phase.add_boolean(
                &bit(&paths[9]),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        assert!(without_vacuous(&left).is_none()); //270ACTIVE, not merely names.
        let right = WorkingTerm {
            paths: BTreeSet::new(),
            constraints: vec![bit(&u)],
            coefficient: KernelScalar::Rational(integer(1)),
            phase: KernelPhasePolynomial::default(),
        };
        assert!(matches(&left, &right));
        assert!(matches_checkpoints(
            &Reduction::Residual,
            &Reduction::Sum(Box::new(right.clone())),
            Some(&left),
            None
        ));
        let mut bad = right.clone();
        bad.coefficient = KernelScalar::Rational(integer(2));
        assert!(!matches(&left, &bad));
        bad = right.clone();
        bad.constraints = vec![bit(&u).xor(&KernelBooleanPolynomial::one())];
        assert!(!matches(&left, &bad));
        bad = right;
        bad.phase.add_boolean(
            &bit(&KernelVariable::InputBra(1)),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        assert!(!matches(&left, &bad));
        let factors = components(&left, &mut allowance()).unwrap();
        assert!(reduce_components(factors.clone(), &mut 0).is_none());
        let mut bad_factors = factors;
        let last = bad_factors.0.last_mut().unwrap();
        //A last, valid nine-bit factor with no applicable exact local identity
        //must refuse the WHOLE new entrance, never accept earlier components.
        last.paths = (0..9)
            .map(|path| KernelVariable::PathBra { term: 7, path })
            .collect();
        last.phase = KernelPhasePolynomial::default();
        for p in &last.paths {
            last.phase.add_boolean(
                &bit(p),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        assert!(reduce_components(bad_factors, &mut allowance()).is_none());
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
}
