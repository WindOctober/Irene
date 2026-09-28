//! Exact pair periods of COMPLETE small-bound phases, before product proof.
//! P=A+B*x+C*y+D*x*y with C=B and D=-2B is A+B*(x XOR y).
//! Summing two owned bits with independent guards/scalars thus equals twice
//! the sum with y=0. Other binders and every free coordinate remain intact.

use super::*;
use crate::symbolic::PhaseCoefficient;

const SOURCE_CELLS: usize = 100_000;

// Total bounded real grammar; inspect BOTH branches, including inactive ones.
fn scalar_cells(scalar: &KernelScalar, cells: &mut usize) -> Option<()> {
    charge(cells, 1)?;
    match scalar {
        KernelScalar::Rational(r) => {
            if r.numer().bits() > 4096 || r.denom().bits() > 4096 {
                return None;
            }
        }
        KernelScalar::Neg(a) => scalar_cells(a, cells)?,
        KernelScalar::Add(a, b) | KernelScalar::Mul(a, b) => {
            scalar_cells(a, cells)?;
            scalar_cells(b, cells)?;
        }
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => {
            for m in condition.terms() {
                charge(cells, 1 + m.variables().count())?;
                if m.variables().any(KernelVariable::is_bound_path) {
                    return None;
                }
            }
            scalar_cells(when_true, cells)?;
            scalar_cells(when_false, cells)?;
        }
        _ => return None,
    }
    Some(())
}

/// One bounded sweep: at most three pair candidates and ONE accepted period.
/// Refusal, including work exhaustion after grouping, never mutates source.
pub(super) fn compact(source: &mut WorkingTerm, work: &mut usize) -> Option<bool> {
    compact_bounded::<8>(source, work)
}

/// Distinct four-binder entrance; old <=3-binder schedules/storage stay intact.
pub(super) fn compact_four(source: &mut WorkingTerm, work: &mut usize) -> Option<bool> {
    if source.paths.len() != 4 {
        return Some(false);
    }
    compact_bounded::<16>(source, work)
}

fn compact_bounded<const MASKS: usize>(source: &mut WorkingTerm, work: &mut usize) -> Option<bool> {
    if !(2..=MASKS.ilog2() as usize).contains(&source.paths.len())
        || source.constraints.len() > 64
        || !source.paths.iter().all(KernelVariable::is_bound_path)
        || !source.within_budget()
    {
        return Some(false);
    }
    let mut scalar_left = 256;
    scalar_cells(&source.coefficient, &mut scalar_left)?;
    let scalar_size = 256 - scalar_left;
    let mut source_cells = source.paths.len() + scalar_size;
    charge(work, source_cells)?;
    for row in &source.constraints {
        for m in row.terms() {
            let n = 1 + m.variables().count();
            source_cells = source_cells.checked_add(n)?;
            if source_cells > SOURCE_CELLS || m.variables().any(KernelVariable::is_bound_path) {
                return None;
            }
            charge(work, n)?;
        }
    }
    let paths = source.paths.iter().collect::<Vec<_>>();
    let mut groups = BTreeMap::<FreeKey<'_>, [Option<&PhaseCoefficient>; MASKS]>::new();
    let mut phase_cells = 0;
    for (m, c) in source.phase.terms() {
        let n = 1 + m.variables().count();
        source_cells = source_cells.checked_add(n)?;
        if source_cells > SOURCE_CELLS {
            return None;
        }
        phase_cells += n;
        // One complete source scan, one borrowed key and MASKS coefficient
        // reference slots only when a new projected group is inserted.
        charge(work, n)?;
        let r = c.as_rational()?;
        if r.numer().bits() > 256 || r.denom().bits() > 256 {
            return None;
        }
        let mut mask = 0;
        for v in m.variables().filter(|v| v.is_bound_path()) {
            mask |= 1 << paths.iter().position(|p| *p == v)?;
        }
        let entry = match groups.entry(FreeKey(m)) {
            std::collections::btree_map::Entry::Occupied(e) => e.into_mut(),
            std::collections::btree_map::Entry::Vacant(e) => {
                charge(work, MASKS + 1)?;
                e.insert([None; MASKS])
            }
        };
        if entry[mask].replace(c).is_some() {
            return None;
        }
    }
    let zero = PhaseCoefficient::default();
    let mut accepted = None;
    'pairs: for x in 0..paths.len() {
        for y in x + 1..paths.len() {
            let xb = 1 << x;
            let yb = 1 << y;
            let mut valid = true;
            for pattern in groups.values() {
                // Check ALL coefficients on other bound coordinates too.
                for rest in (0..1usize << paths.len()).filter(|m| m & (xb | yb) == 0) {
                    charge(work, 4)?;
                    let b = pattern[rest | xb].unwrap_or(&zero);
                    let c = pattern[rest | yb].unwrap_or(&zero);
                    let d = pattern[rest | xb | yb].unwrap_or(&zero);
                    if b != c || &b.scaled(BigInt::from(-2)) != d {
                        valid = false;
                        break;
                    }
                }
                if !valid {
                    break;
                }
            }
            if valid {
                accepted = Some(paths[y].clone());
                break 'pairs;
            }
        }
    }
    let Some(y) = accepted else {
        return Some(false);
    };
    // Reserve deletion scan and bounded complete scalar reconstruction BEFORE
    // mutation. Dropping the old index and erased keys constructs no syntax.
    charge(work, phase_cells + 3 * scalar_size + 3)?;
    drop(groups);
    let old = source.phase.term_count();
    source.phase.restrict_zero(&y);
    source.paths.remove(&y);
    source.coefficient =
        normalize_scalar(KernelScalar::Rational(integer(2)).multiply(source.coefficient.clone()));
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate pair-period restricted: terms={old}->{} paths={} work={work}",
            source.phase.term_count(),
            source.paths.len()
        );
    }
    Some(true)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn variables() -> [KernelVariable; 5] {
        [
            KernelVariable::PathKet { term: 0, path: 0 },
            KernelVariable::PathBra { term: 0, path: 0 },
            KernelVariable::PathKet { term: 1, path: 0 },
            KernelVariable::InputKet(0),
            KernelVariable::InputBra(0),
        ]
    }
    fn fixture(coefficients: [i64; 4]) -> WorkingTerm {
        let [x, y, _, _, _] = variables();
        let mut phase = KernelPhasePolynomial::default();
        for (mask, coefficient) in coefficients.into_iter().enumerate() {
            let m = KernelMonomial::from_variables(
                [&x, &y]
                    .into_iter()
                    .enumerate()
                    .filter(|(i, _)| mask & (1 << i) != 0)
                    .map(|(_, v)| v.clone()),
            );
            phase.add_term(m, PhaseCoefficient::rational(ratio(coefficient, 8)));
        }
        WorkingTerm {
            paths: BTreeSet::from([x, y]),
            constraints: Vec::new(),
            coefficient: KernelScalar::Rational(integer(3)),
            phase,
        }
    }
    fn work_budget() -> usize {
        WORK_CELLS
    }
    fn row_value(row: &KernelBooleanPolynomial, point: &BTreeMap<KernelVariable, bool>) -> bool {
        row.terms()
            .filter(|m| m.variables().all(|v| point[v]))
            .count()
            % 2
            != 0
    }
    fn scalar_value(s: &KernelScalar, p: &BTreeMap<KernelVariable, bool>) -> BigRational {
        match s {
            KernelScalar::Rational(r) => r.clone(),
            KernelScalar::Add(a, b) => scalar_value(a, p) + scalar_value(b, p),
            KernelScalar::Mul(a, b) => scalar_value(a, p) * scalar_value(b, p),
            KernelScalar::Neg(a) => -scalar_value(a, p),
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => scalar_value(
                if row_value(condition, p) {
                    when_true
                } else {
                    when_false
                },
                p,
            ),
            _ => panic!("not a total test scalar"),
        }
    }
    // Independent literal finite weighted histogram; no phase reducer, sum
    // certificate or cyclotomic evaluator. Every bound point is included.
    fn histogram(t: &WorkingTerm, free_bits: usize) -> BTreeMap<BigRational, BigRational> {
        let v = variables();
        let mut result = BTreeMap::new();
        for bits in 0..1usize << t.paths.len() {
            let mut p = BTreeMap::from([
                (v[3].clone(), free_bits & 1 != 0),
                (v[4].clone(), free_bits & 2 != 0),
            ]);
            p.extend(
                t.paths
                    .iter()
                    .enumerate()
                    .map(|(i, v)| (v.clone(), bits & (1 << i) != 0)),
            );
            if t.constraints.iter().any(|g| row_value(g, &p)) {
                continue;
            }
            let phase = t
                .phase
                .terms()
                .filter(|(m, _)| m.variables().all(|v| p[v]))
                .map(|(_, c)| c.as_rational().unwrap())
                .sum::<BigRational>();
            let phase = (phase % integer(1) + integer(1)) % integer(1);
            *result.entry(phase).or_insert_with(|| integer(0)) += scalar_value(&t.coefficient, &p);
        }
        result.retain(|_, r| r != &integer(0));
        result
    }
    fn same(a: &WorkingTerm, b: &WorkingTerm) {
        assert_eq!(a.paths, b.paths);
        assert_eq!(a.constraints, b.constraints);
        assert_eq!(a.coefficient, b.coefficient);
        assert_eq!(a.phase, b.phase);
    }

    #[test]
    fn four_binder_period_checks_every_other_mask_and_keeps_all_weighted_entries() {
        let v = variables();
        let z = KernelVariable::PathBra { term: 1, path: 1 };
        for code in 0usize..64 {
            let mut t = fixture([3, 1, 1, 6]);
            t.paths.extend([v[2].clone(), z.clone()]);
            for (u, c) in [(&v[2], 3), (&z, 5)] {
                t.phase.add_term(
                    KernelMonomial::variable(u.clone()),
                    PhaseCoefficient::rational(ratio(c, 8)),
                );
            }
            let remaining = [&v[2], &z, &v[3], &v[4]];
            for mask in 1..16 {
                let rest = KernelMonomial::from_variables(
                    remaining
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| mask & (1 << i) != 0)
                        .map(|(_, v)| (*v).clone()),
                );
                let c = 1 + ((code >> (mask % 6)) % 8) as i64;
                for (bits, c) in [(1, c), (2, c), (3, -2 * c)] {
                    t.phase.add_term(
                        KernelMonomial::from_variables(
                            rest.variables().cloned().chain(
                                v[..2]
                                    .iter()
                                    .enumerate()
                                    .filter(|(i, _)| bits & (1 << i) != 0)
                                    .map(|(_, v)| v.clone()),
                            ),
                        ),
                        PhaseCoefficient::rational(ratio(c, 8)),
                    );
                }
            }
            t.constraints
                .push(KernelBooleanPolynomial::variable(v[3].clone()));
            t.coefficient = KernelScalar::Select {
                condition: KernelBooleanPolynomial::variable(v[4].clone()),
                when_true: Box::new(KernelScalar::Rational(ratio(-5, 8))),
                when_false: Box::new(KernelScalar::Rational(integer(3))),
            };
            let before = t.clone();
            assert_eq!(compact(&mut t, &mut work_budget()), Some(false));
            same(&t, &before); // The old entrance has NOT been widened.
            let mut work = work_budget();
            assert_eq!(compact_four(&mut t, &mut work), Some(true));
            assert_eq!(t.paths.len(), 3);
            for free in 0..4 {
                assert_eq!(histogram(&before, free), histogram(&t, free));
            }
            let cost = WORK_CELLS - work;
            let mut refused = before.clone();
            assert_eq!(compact_four(&mut refused, &mut { cost - 1 }), None);
            same(&refused, &before);
        }
    }

    #[test]
    fn four_binder_period_rejects_late_rest_coefficients_and_dependencies() {
        let v = variables();
        let z = KernelVariable::PathBra { term: 1, path: 1 };
        let mut t = fixture([3, 1, 1, 6]);
        t.paths.extend([v[2].clone(), z.clone()]);
        for (u, c) in [(&v[2], 3), (&z, 5)] {
            t.phase.add_term(
                KernelMonomial::variable(u.clone()),
                PhaseCoefficient::rational(ratio(c, 8)),
            );
        }
        let before = t.clone();
        assert_eq!(compact_four(&mut t.clone(), &mut work_budget()), Some(true));
        t.phase.add_term(
            KernelMonomial::from_variables([v[0].clone(), v[1].clone(), v[2].clone(), z.clone()]),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
        let corrupted = t.clone();
        assert_eq!(compact_four(&mut t, &mut work_budget()), Some(false));
        same(&t, &corrupted);
        for bound_guard in [true, false] {
            let mut bad = before.clone();
            if bound_guard {
                bad.constraints
                    .push(KernelBooleanPolynomial::variable(z.clone()));
            } else {
                bad.coefficient = KernelScalar::Select {
                    condition: KernelBooleanPolynomial::zero(),
                    when_true: Box::new(KernelScalar::Select {
                        condition: KernelBooleanPolynomial::variable(z.clone()),
                        when_true: Box::new(KernelScalar::Rational(integer(2))),
                        when_false: Box::new(KernelScalar::Rational(integer(3))),
                    }),
                    when_false: Box::new(KernelScalar::Rational(integer(1))),
                };
            }
            let saved = bad.clone();
            assert_eq!(compact_four(&mut bad, &mut work_budget()), None);
            same(&bad, &saved);
        }
        let mut missing = before;
        missing.paths.remove(&z);
        missing
            .paths
            .insert(KernelVariable::PathBra { term: 19, path: 5 });
        let saved = missing.clone();
        assert_eq!(compact_four(&mut missing, &mut work_budget()), None);
        same(&missing, &saved);
    }

    #[test]
    fn pair_period_all_eighth_turn_coefficients_check_full_constant_and_sign() {
        let mut accepted = 0;
        for code in 0..4096 {
            let coefficients = [code % 8, (code / 8) % 8, (code / 64) % 8, (code / 512) % 8];
            let mut t = fixture(coefficients);
            let before = t.clone();
            let changed = compact(&mut t, &mut work_budget()).unwrap();
            let expected = coefficients[1] == coefficients[2]
                && (coefficients[3] + 2 * coefficients[1]) % 8 == 0;
            assert_eq!(changed, expected);
            if changed {
                accepted += 1;
                assert_eq!(t.paths.len(), 1);
                assert_eq!(histogram(&before, 0), histogram(&t, 0));
            } else {
                same(&before, &t);
            }
        }
        assert_eq!(accepted, 64);
    }

    #[test]
    fn pair_period_keeps_other_binders_free_polynomials_guards_and_nested_weights() {
        let v = variables();
        for code in 0usize..64 {
            let mut t = fixture([3, 1, 1, 6]);
            t.paths.insert(v[2].clone());
            t.phase.add_term(
                KernelMonomial::variable(v[2].clone()),
                PhaseCoefficient::rational(ratio(3, 8)),
            );
            for mask in 1..8 {
                let rest = KernelMonomial::from_variables(
                    v[2..]
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| mask & (1 << i) != 0)
                        .map(|(_, v)| v.clone()),
                );
                let b = 1 + (code >> (mask % 6)) as i64 % 8;
                for (bits, c) in [(1, b), (2, b), (3, -2 * b)] {
                    let m = KernelMonomial::from_variables(
                        rest.variables().cloned().chain(
                            v[..2]
                                .iter()
                                .enumerate()
                                .filter(|(i, _)| bits & (1 << i) != 0)
                                .map(|(_, v)| v.clone()),
                        ),
                    );
                    t.phase.add_term(m, PhaseCoefficient::rational(ratio(c, 8)));
                }
            }
            t.constraints
                .push(KernelBooleanPolynomial::variable(v[3].clone()));
            t.coefficient = KernelScalar::Select {
                condition: KernelBooleanPolynomial::variable(v[4].clone()),
                when_true: Box::new(KernelScalar::Rational(ratio(-5, 8))),
                when_false: Box::new(KernelScalar::Add(
                    Box::new(KernelScalar::Rational(integer(0))),
                    Box::new(KernelScalar::Rational(integer(2))),
                )),
            };
            let before = t.clone();
            assert!(compact(&mut t, &mut work_budget()).unwrap());
            assert_eq!(t.paths.len(), 2);
            assert_eq!(t.constraints, before.constraints);
            for free in 0..4 {
                assert_eq!(histogram(&before, free), histogram(&t, free));
            }
        }
    }

    #[test]
    fn pair_period_refusals_preserve_complete_source_and_shared_allowance() {
        let v = variables();
        let t = fixture([1, 1, 1, 6]);
        let mut full = WORK_CELLS;
        assert!(compact(&mut t.clone(), &mut full).unwrap());
        let needed = WORK_CELLS - full;
        for amount in 0..needed {
            let mut source = t.clone();
            let mut work = amount;
            assert!(compact(&mut source, &mut work).is_none());
            same(&source, &t);
            assert!(work <= amount);
        }
        let mut bad = Vec::new();
        let mut b = t.clone();
        b.paths.remove(&v[0]);
        bad.push(b);
        let mut b = t.clone();
        b.paths.insert(v[3].clone());
        bad.push(b);
        let mut b = t.clone();
        b.constraints
            .push(KernelBooleanPolynomial::variable(v[1].clone()));
        bad.push(b);
        let mut b = t.clone();
        b.coefficient = KernelScalar::Select {
            condition: KernelBooleanPolynomial::zero(),
            when_true: Box::new(KernelScalar::Select {
                condition: KernelBooleanPolynomial::variable(v[0].clone()),
                when_true: Box::new(KernelScalar::Rational(integer(1))),
                when_false: Box::new(KernelScalar::Rational(integer(2))),
            }),
            when_false: Box::new(KernelScalar::Rational(integer(3))),
        };
        bad.push(b);
        let mut b = t.clone();
        b.phase.add_term(
            KernelMonomial::variable(v[2].clone()),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
        bad.push(b);
        let mut b = t.clone();
        b.phase.add_term(
            KernelMonomial::default(),
            PhaseCoefficient::rational(BigRational::new(1.into(), BigInt::from(1) << 300)),
        );
        bad.push(b);
        let mut b = t.clone();
        b.coefficient = KernelScalar::Rational(BigRational::from_integer(BigInt::from(1) << 4097));
        bad.push(b);
        let mut b = t.clone();
        b.constraints.resize(65, KernelBooleanPolynomial::zero());
        bad.push(b);
        for mut source in bad {
            let before = source.clone();
            assert!(!compact(&mut source, &mut work_budget()).is_some_and(|b| b));
            same(&source, &before);
        }
    }

    #[test]
    fn zero_restriction_matches_full_substitution_with_and_without_occurrence_index() {
        let v = variables();
        for code in 0usize..256 {
            let mut p = KernelPhasePolynomial::default();
            for mask in 0..8 {
                if code & (1 << mask) != 0 {
                    p.add_term(
                        KernelMonomial::from_variables(
                            v[..3]
                                .iter()
                                .enumerate()
                                .filter(|(i, _)| mask & (1 << i) != 0)
                                .map(|(_, v)| v.clone()),
                        ),
                        PhaseCoefficient::rational(ratio(1 + mask as i64, 16)),
                    );
                }
            }
            for variable in &v[..3] {
                for indexed in [false, true] {
                    let mut reference = p.clone();
                    reference.substitute(variable, &KernelBooleanPolynomial::zero());
                    let mut direct = p.clone();
                    if indexed {
                        direct.index_occurrences();
                    }
                    direct.restrict_zero(variable);
                    assert_eq!(direct, reference);
                    assert!(!direct.has_occurrence_index());
                    direct.index_occurrences();
                    for path in &v[..3] {
                        assert_eq!(
                            direct.occurrence_count(path),
                            reference.occurrence_count(path)
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn oversized_pair_period_enters_complete_product_with_all_common_fields() {
        let [x, y, z, free, _] = variables();
        let mut left = fixture([0, 0, 0, 0]);
        left.paths.insert(z.clone());
        left.constraints
            .push(KernelBooleanPolynomial::variable(free.clone()));
        for i in 1..=4000 {
            let f = KernelMonomial::variable(KernelVariable::InputKet(i));
            for (mask, c) in [(1, 1), (2, 1), (3, -2)] {
                let m = KernelMonomial::from_variables(
                    f.variables().cloned().chain(
                        [&x, &y]
                            .into_iter()
                            .enumerate()
                            .filter(|(j, _)| mask & (1 << j) != 0)
                            .map(|(_, v)| v.clone()),
                    ),
                );
                left.phase
                    .add_term(m, PhaseCoefficient::rational(ratio(c, 8)));
            }
        }
        left.phase.add_term(
            KernelMonomial::variable(z),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
        let mut right = left.clone();
        right.phase.substitute(&y, &KernelBooleanPolynomial::zero());
        right.paths.remove(&y);
        right.coefficient = KernelScalar::Rational(integer(6));
        let compare = |a: WorkingTerm, b: WorkingTerm| {
            matches_reduced_components(
                &Reduction::Sum(Box::new(a)),
                &Reduction::Sum(Box::new(b)),
                &mut work_budget(),
            )
        };
        assert!(compare(left.clone(), right.clone()));
        let mut changed = right.clone();
        changed.coefficient = KernelScalar::Rational(integer(3));
        assert!(!compare(left.clone(), changed));
        let mut changed = right.clone();
        changed.constraints[0] = changed.constraints[0].complement();
        assert!(!compare(left.clone(), changed));
        let mut changed = right;
        changed.phase.add_term(
            KernelMonomial::variable(free),
            PhaseCoefficient::rational(ratio(1, 4)),
        );
        // Use a distinct free coordinate, not one forced to zero by the guard.
        changed.phase.add_term(
            KernelMonomial::variable(KernelVariable::InputBra(0)),
            PhaseCoefficient::rational(ratio(1, 4)),
        );
        assert!(!compare(left, changed));
    }

    #[test]
    fn pair_period_checks_late_other_coordinate_coefficients_and_source_size() {
        let v = variables();
        let mut source = fixture([1, 1, 1, 6]);
        source.paths.insert(v[2].clone());
        source.phase.add_term(
            KernelMonomial::variable(v[2].clone()),
            PhaseCoefficient::rational(ratio(3, 8)),
        );
        let mut bad = source.clone();
        bad.phase.add_term(
            KernelMonomial::from_variables(v.iter().cloned()),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
        let before = bad.clone();
        assert!(!compact(&mut bad, &mut work_budget()).unwrap());
        same(&before, &bad);
        assert!(compact(&mut source, &mut work_budget()).unwrap());
        let mut large = fixture([0, 1, 1, 6]);
        for i in 1..=10001 {
            let variables = (0..9).map(|j| KernelVariable::InputKet(9 * i + j));
            large.phase.add_term(
                KernelMonomial::from_variables(variables),
                PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        let before = large.clone();
        assert!(compact(&mut large, &mut work_budget()).is_none());
        same(&before, &large);
    }
}
