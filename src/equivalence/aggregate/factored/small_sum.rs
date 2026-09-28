//! Complete small-bound sums with borrowed free keys and shared coefficient maps.
//!
//! P(u,v) = sum_f f(u) P_f(v). For each of ALL 2^k assignments a, its
//! coefficient at f is sum_{mask subset a} P_f[mask]. Equal complete maps
//! share this calculation; free monomials are never identified or summed.

use super::*;
use crate::symbolic::PhaseCoefficient;

const MAX_SOURCE_CELLS: usize = 100_000;
const MAX_PATHS: usize = 3;

fn charge(budget: &mut ReductionBudget, amount: usize) -> Option<()> {
    budget.phase_cells = budget.phase_cells.checked_sub(amount)?;
    Some(())
}

// A deliberately small, total real scalar grammar. No new inverse/root or
// numeric-expression domain assumptions are introduced by this entrance.
fn scalar_cells(scalar: &KernelScalar, left: &mut usize) -> Option<usize> {
    *left = left.checked_sub(1)?;
    let mut cells = 1;
    match scalar {
        KernelScalar::Rational(r) => {
            if r.numer().bits() > 4096 || r.denom().bits() > 4096 {
                return None;
            }
        }
        KernelScalar::Neg(a) => cells += scalar_cells(a, left)?,
        KernelScalar::Add(a, b) | KernelScalar::Mul(a, b) => {
            cells += scalar_cells(a, left)? + scalar_cells(b, left)?;
        }
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => {
            for m in condition.terms() {
                let n = 1 + m.variables().count();
                *left = left.checked_sub(n)?;
                if m.variables().any(KernelVariable::is_bound_path) {
                    return None;
                }
                cells += n;
            }
            cells += scalar_cells(when_true, left)? + scalar_cells(when_false, left)?;
        }
        _ => return None,
    }
    Some(cells)
}

/// Read-only structural preflight. Larger source syntax is admitted ONLY to
/// this shared representation, never to the ordinary local reducer.
pub(super) fn admitted(source: &WorkingTerm) -> bool {
    geometry(source).is_some()
}

fn header_geometry(source: &WorkingTerm) -> Option<(usize, usize)> {
    if source.paths.is_empty()
        || source.paths.len() > MAX_PATHS
        || !source.paths.iter().all(KernelVariable::is_bound_path)
        || source.constraints.len() > 64
        || !source.within_budget()
    {
        return None;
    }
    let mut cells = source.paths.len();
    let mut retained = scalar_cells(&source.coefficient, &mut 256)?;
    for row in &source.constraints {
        for m in row.terms() {
            retained = retained.checked_add(1 + m.variables().count())?;
            if retained > MAX_SOURCE_CELLS || m.variables().any(KernelVariable::is_bound_path) {
                return None;
            }
        }
    }
    cells += retained;
    (cells <= MAX_SOURCE_CELLS).then_some((cells, retained))
}

fn phase_geometry(
    source: &WorkingTerm,
    m: &KernelMonomial,
    c: &PhaseCoefficient,
    cells: &mut usize,
) -> Option<usize> {
    let size = 1 + m.variables().count();
    *cells = cells.checked_add(size)?;
    if *cells > MAX_SOURCE_CELLS
        || m.variables()
            .any(|v| v.is_bound_path() && !source.paths.contains(v))
    {
        return None;
    }
    let rational = c.as_rational()?;
    if rational.numer().bits() > 256 || rational.denom().bits() > 256 {
        return None;
    }
    Some(size)
}

fn geometry(source: &WorkingTerm) -> Option<(usize, usize)> {
    let (mut cells, retained) = header_geometry(source)?;
    for (m, c) in source.phase.terms() {
        phase_geometry(source, m, c, &mut cells)?;
    }
    Some((cells, retained))
}

pub(super) fn sum(source: &WorkingTerm, budget: &mut ReductionBudget) -> Option<ExactAggregate> {
    let initial_work = budget.phase_cells;
    let (mut source_cells, retained_cells) = header_geometry(source)?;
    charge(budget, source_cells)?;
    let paths = source.paths.iter().collect::<Vec<_>>();
    let leaves = 1usize << paths.len();
    // Same bound-node allowance as a complete binary Shannon tree, shared
    // with every other factor. No new per-leaf or coefficient-work budget.
    budget.splits = budget.splits.checked_sub(leaves - 1)?;
    let mut groups: BTreeMap<FreeKey<'_>, BTreeMap<u8, &PhaseCoefficient>> = BTreeMap::new();
    for (m, c) in source.phase.terms() {
        // Fuse phase admission with grouping: inspect the complete source
        // once and allocate only a projected-key reference plus mask/value
        // records. No full pre-scan followed by free-vector copying remains.
        let size = phase_geometry(source, m, c, &mut source_cells)?;
        charge(budget, size + 3)?;
        let mut mask = 0u8;
        for v in m.variables() {
            if let Some(i) = paths.iter().position(|p| *p == v) {
                mask |= 1 << i;
            }
        }
        // The (free monomial, bound mask) split of a square-free monomial
        // is injective. All keys/coefficients borrow the immutable source.
        if groups
            .entry(FreeKey(m))
            .or_default()
            .insert(mask, c)
            .is_some()
        {
            return None;
        }
    }
    let mut shared: BTreeMap<&BTreeMap<u8, &PhaseCoefficient>, Vec<PhaseCoefficient>> =
        BTreeMap::new();
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate shared small sum grouped: source_cells={source_cells} groups={} remaining={}",
            groups.len(),
            budget.phase_cells
        );
    }
    let mut active_patterns = BTreeSet::new();
    let mut constant_pattern = None;
    for (free, pattern) in &groups {
        charge(budget, 1 + pattern.len())?;
        match shared.entry(pattern) {
            std::collections::btree_map::Entry::Occupied(_) => {}
            std::collections::btree_map::Entry::Vacant(entry) => {
                charge(budget, leaves)?;
                let mut values = vec![PhaseCoefficient::default(); leaves];
                // k<=3 and at most eight source coefficients of <=256 bits.
                // Temporary rational widths are bounded by eight operand
                // widths. A complete subset-sum transform replaces repeated
                // tests of every source mask at every assignment.
                for (&mask, &c) in pattern {
                    charge(budget, 1)?;
                    values[mask as usize] = c.clone();
                }
                for bit in 0..paths.len() {
                    for a in 0..leaves {
                        if a & (1 << bit) != 0 {
                            charge(budget, 2)?;
                            let lower = values[a ^ (1 << bit)].clone();
                            values[a].add_assign(lower);
                        }
                    }
                }
                entry.insert(values);
            }
        }
        charge(budget, 1)?;
        if free.variables().next().is_some() {
            active_patterns.insert(pattern);
        } else {
            constant_pattern = Some(pattern);
        }
    }
    // A vector of ALL nonconstant block values determines the full formal
    // free phase. Combine equal complete leaf signatures (with exact constant
    // half-turn signs) BEFORE any free phase is expanded. No prefix equality.
    type Signature<'a> = (Vec<&'a PhaseCoefficient>, PhaseCoefficient);
    let mut signatures = BTreeMap::<Signature<'_>, (usize, i64)>::new();
    for assignment in 0..(1u8 << paths.len()) {
        let a = usize::from(assignment);
        charge(budget, 2 + active_patterns.len())?;
        let signature = active_patterns
            .iter()
            .map(|p| &shared[p][a])
            .collect::<Vec<_>>();
        let mut constant = constant_pattern
            .map(|p| shared[p][a].clone())
            .unwrap_or_default();
        let sign = if constant.rational_part() >= ratio(1, 2) {
            constant.add_assign(PhaseCoefficient::rational(ratio(1, 2)));
            -1
        } else {
            1
        };
        signatures.entry((signature, constant)).or_insert((a, 0)).1 += sign;
    }
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        // Read-only bounded geometry for a possible phase-basis route. It
        // never changes the sum, budget, binder set or certificate decision.
        let periods = (shared.len() <= 256).then(|| {
            (1..leaves)
                .filter(|d| {
                    shared
                        .values()
                        .all(|values| (0..leaves).all(|a| values[a] == values[a ^ d]))
                })
                .collect::<Vec<_>>()
        });
        eprintln!(
            "aggregate shared small sum signatures: patterns={} signatures={} surviving={} remaining={} periods={periods:?} multiplicities={:?}",
            shared.len(),
            signatures.len(),
            signatures.values().filter(|(_, n)| *n != 0).count(),
            budget.phase_cells,
            signatures
                .values()
                .map(|(a, n)| (*a, *n))
                .collect::<Vec<_>>()
        );
    }
    let patterns = shared.len();
    let mut result = ExactAggregate::new();
    let mut atoms = 0;
    let mut leaf_cells = 0usize;
    for ((_, constant), (a, multiplicity)) in signatures {
        if multiplicity == 0 {
            continue;
        }
        let mut phase = KernelPhasePolynomial::default();
        for (free, pattern) in &groups {
            charge(budget, 1)?;
            let value = &shared[pattern][a];
            if value.is_zero() || free.variables().next().is_none() {
                continue;
            }
            // Only surviving coefficients allocate owned free monomials.
            // add_term moves this unique key, without generic Boolean lifts
            // or growing-prefix phase copies.
            let cells = 1 + free.variables().count();
            charge(budget, cells)?;
            leaf_cells += cells;
            phase.add_term(
                KernelMonomial::from_variables(free.variables().cloned()),
                value.clone(),
            );
        }
        charge(budget, 3 + retained_cells)?;
        phase.add_term(KernelMonomial::one(), constant);
        accumulate_exact_term(
            ExactTerm {
                constraints: source.constraints.clone(),
                coefficient: normalize_scalar(
                    source
                        .coefficient
                        .clone()
                        .multiply(KernelScalar::Rational(integer(multiplicity))),
                ),
                phase,
            },
            &mut result,
            &mut atoms,
        )?;
    }
    result.retain(|_, values| !values.is_empty());
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate shared small sum: paths={} source_cells={source_cells} groups={} patterns={patterns} leaf_cells={leaf_cells} atoms={atoms} charged={} remaining={}",
            paths.len(),
            groups.len(),
            initial_work - budget.phase_cells,
            budget.phase_cells
        );
    }
    Some(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn budget() -> ReductionBudget {
        ReductionBudget {
            splits: 4095,
            products: MAX_FACTOR_PRODUCTS,
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

    #[test]
    fn shared_small_sum_large_source_uses_complete_consuming_product_gate() {
        let a = KernelVariable::PathKet { term: 0, path: 0 };
        let b = KernelVariable::PathBra { term: 1, path: 0 };
        let mut common = WorkingTerm {
            constraints: vec![bit(&KernelVariable::ClassicalOutput(0))],
            paths: BTreeSet::new(),
            coefficient: KernelScalar::Rational(integer(1)),
            phase: KernelPhasePolynomial::default(),
        };
        let mut factor = WorkingTerm {
            constraints: Vec::new(),
            paths: BTreeSet::from([a.clone(), b.clone()]),
            coefficient: KernelScalar::Rational(integer(1)),
            phase: KernelPhasePolynomial::default(),
        };
        let mut small = factor.clone();
        small.paths.remove(&b);
        factor
            .phase
            .add_boolean(&bit(&a), PhaseCoefficient::rational(ratio(1, 2)));
        factor.phase.add_boolean(
            &bit(&a).and(&bit(&b)),
            PhaseCoefficient::rational(ratio(1, 2)),
        );
        for i in 0..10000 {
            let m = KernelMonomial::from_variables([
                KernelVariable::InputKet(i),
                KernelVariable::InputBra(i),
            ]);
            factor.phase.add_term(
                m.multiply(&KernelMonomial::variable(b.clone())),
                PhaseCoefficient::rational(ratio(1, 8)),
            );
            common
                .phase
                .add_term(m, PhaseCoefficient::rational(ratio(1, 8)));
        }
        let mut left_common = common.clone();
        left_common.phase = KernelPhasePolynomial::default();
        // Both products denote 2[c=0] exp(F): at b=0 the two a leaves
        // cancel, and at b=1 both a leaves contribute exp(F). Source phases and
        // scalar/selector cannot be discarded merely to reduce local syntax.
        assert!(matches_components(
            vec![left_common.clone(), factor.clone()],
            vec![common.clone(), small.clone()]
        ));
        let mut wrong = common.clone();
        wrong.coefficient = KernelScalar::Rational(integer(2));
        assert!(!matches_components(
            vec![left_common.clone(), factor.clone()],
            vec![wrong, small.clone()]
        ));
        let mut wrong = common.clone();
        wrong.constraints[0] = wrong.constraints[0].complement();
        assert!(!matches_components(
            vec![left_common.clone(), factor.clone()],
            vec![wrong, small.clone()]
        ));
        let mut wrong = common.clone();
        wrong.phase.add_boolean(
            &bit(&KernelVariable::InputKet(0)),
            PhaseCoefficient::rational(ratio(1, 4)),
        );
        assert!(!matches_components(
            vec![left_common, factor.clone()],
            vec![wrong, small]
        ));
        // A later refused factor may never be omitted after a successful sum.
        let mut undeclared = factor.clone();
        undeclared.paths.clear();
        assert!(!matches_components(
            vec![common.clone(), factor.clone(), undeclared],
            vec![common]
        ));
        for i in 10000..34000 {
            factor.phase.add_term(
                KernelMonomial::from_variables([
                    KernelVariable::InputKet(i),
                    KernelVariable::InputBra(i),
                ]),
                PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        assert!(!admitted(&factor));
    }
}
