//! Exact sharing of bound-mask coefficient polynomials across free monomials.
//! All masks in a component undergo the SAME reversible basis changes. Equal
//! coefficient maps are shared by exact ordered comparison, never by hashes.

use super::*;
use crate::symbolic::PhaseCoefficient;

// Sparse support remains capped at 256 entries, independently of the mask's
// sixteen-bit coordinate namespace. No 2^16 assignment table is constructed.
type MaskPhase = BTreeMap<u16, PhaseCoefficient>;

struct Block {
    free: Vec<KernelMonomial>,
    free_cells: usize,
    phase: MaskPhase,
}

fn insert(phase: &mut MaskPhase, mask: u16, coefficient: PhaseCoefficient) {
    let entry = phase.entry(mask).or_default();
    entry.add_assign(coefficient);
    if entry.is_zero() {
        phase.remove(&mask);
    }
}

fn insert_bounded(phase: &mut MaskPhase, mask: u16, coefficient: PhaseCoefficient) -> Option<()> {
    // Do not transiently allocate a 257th key even for a zero delta.
    if coefficient.is_zero() {
        return Some(());
    }
    if !phase.contains_key(&mask) && phase.len() >= 256 {
        return None;
    }
    insert(phase, mask, coefficient);
    Some(())
}

fn cost(phase: &MaskPhase, block: &Block) -> (usize, usize) {
    (
        phase.len() * block.free.len(),
        phase.len() * block.free_cells
            + block.free.len() * phase.keys().map(|m| m.count_ones() as usize).sum::<usize>(),
    )
}

/// Full, integer-only transvection, including every unaffected mask. A proposal
/// may temporarily have at most three times the old entries (and <=256 masks).
#[cfg(test)]
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

/// Sparse mask delta, with exactly the same block identity as the original
/// full-monomial transvection. Every changed key is checked against the entire
/// source, including keys without x. All block deltas must finish before commit.
fn delta(source: &MaskPhase, x: u16, y: u16, work: &mut usize) -> Option<MaskPhase> {
    if source.len() > 256 {
        return None;
    }
    let mut result = MaskPhase::new();
    for (&mask, coefficient) in source {
        charge(work, 1)?;
        if mask & x == 0 {
            continue;
        }
        if mask & y != 0 && source.contains_key(&(mask & !y)) {
            continue;
        }
        charge(work, 6 * (1 + mask.count_ones() as usize))?;
        let mut total = coefficient.clone();
        let other = if mask & y == 0 {
            source.get(&(mask | y)).cloned().unwrap_or_default()
        } else {
            PhaseCoefficient::default()
        };
        let value = other.as_rational()?;
        if value.numer().bits() > 256 || value.denom().bits() > 256 {
            return None;
        }
        if mask & y == 0 {
            total.add_assign(other);
        }
        for c in [coefficient, &total] {
            let v = c.as_rational()?;
            if v.numer().bits() > 256 || v.denom().bits() > 256 {
                return None;
            }
        }
        insert_bounded(&mut result, (mask & !x) | y, total.clone())?;
        insert_bounded(&mut result, mask | y, total.scaled(BigInt::from(-2)))?;
    }
    Some(result)
}

fn delta_cost(source: &MaskPhase, delta: &MaskPhase, block: &Block) -> Option<(usize, usize)> {
    let mut result = cost(source, block);
    let mut entries = source.len();
    for (&mask, coefficient) in delta {
        let before = source.get(&mask).cloned().unwrap_or_default();
        let value = before.as_rational()?;
        if value.numer().bits() > 256 || value.denom().bits() > 256 {
            return None;
        }
        let mut after = before.clone();
        after.add_assign(coefficient.clone());
        let cells = block.free_cells + block.free.len() * mask.count_ones() as usize;
        if !before.is_zero() {
            entries -= 1;
            result.0 -= block.free.len();
            result.1 -= cells;
        }
        if !after.is_zero() {
            entries += 1;
            result.0 += block.free.len();
            result.1 += cells;
        }
    }
    (entries <= 256).then_some(result)
}

pub(super) fn compact(factor: &mut WorkingTerm, work: &mut usize) -> Option<bool> {
    if !admitted(factor)
        || factor.paths.len() < 2
        || factor.paths.len() > 16
        || factor.phase.term_count() > MAX_LOCAL_TERMS
        || factor.paths.iter().any(|v| factor.occurs_outside_phase(v))
    {
        return Some(false);
    }
    let mut input_cells = 0usize;
    for (m, _) in factor.phase.terms() {
        input_cells = input_cells.checked_add(1 + m.variables().count())?;
        if input_cells > 32768 {
            return Some(false);
        }
    }
    // Reserve the complete final reconstruction before spending proposal work.
    // Every accepted move is non-growing, so this bound remains sufficient.
    // One monomial construction and one native insertion, without an occurrence
    // index or growing-prefix union copies. Reserve two original-cell passes.
    charge(work, input_cells.checked_mul(2)?)?;
    let paths = factor.paths.iter().cloned().collect::<Vec<_>>();
    let mut by_free = BTreeMap::<KernelMonomial, MaskPhase>::new();
    for (m, coefficient) in factor.phase.terms() {
        let value = coefficient.as_rational()?;
        if value.numer().bits() > 256 || value.denom().bits() > 256 {
            return Some(false);
        }
        charge(work, 2 * (1 + m.variables().count()))?;
        let mut mask = 0u16;
        let free = KernelMonomial::from_variables(m.variables().filter_map(|v| {
            if let Ok(i) = paths.binary_search(v) {
                mask |= 1 << i;
                None
            } else {
                Some(v.clone())
            }
        }));
        // The split is unique: no two original monomials have the same pair.
        let pattern = by_free.entry(free).or_default();
        if pattern.len() >= 256 {
            return Some(false);
        }
        pattern.insert(mask, coefficient.clone());
    }
    let mut shared = BTreeMap::<MaskPhase, Vec<KernelMonomial>>::new();
    for (free, phase) in by_free {
        charge(work, 1 + free.variables().count() + phase.len())?;
        shared.entry(phase).or_default().push(free);
    }
    let mut blocks = shared
        .into_iter()
        .map(|(phase, free)| Block {
            free_cells: free.iter().map(|m| 1 + m.variables().count()).sum(),
            free,
            phase,
        })
        .collect::<Vec<_>>();
    let original = blocks
        .iter()
        .map(|b| cost(&b.phase, b))
        .fold((0, 0), |a, b| (a.0 + b.0, a.1 + b.1));
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate shared-block geometry: patterns={} distinct_masks={} original_terms={} work={work}",
            blocks.len(),
            blocks.iter().map(|b| b.phase.len()).sum::<usize>(),
            original.0
        );
    }
    let mut current = original;
    let mut changed = false;
    'rounds: for _ in 0..8 {
        let mut pairs = BTreeMap::<(usize, usize), usize>::new();
        for block in &blocks {
            for &mask in block.phase.keys() {
                let active = (0..paths.len())
                    .filter(|i| mask & (1 << i) != 0)
                    .collect::<Vec<_>>();
                if charge(work, 1 + paths.len() + active.len() * active.len()).is_none() {
                    break 'rounds;
                }
                for &x in &active {
                    for &y in &active {
                        if x != y {
                            *pairs.entry((x, y)).or_default() += block.free.len();
                        }
                    }
                }
            }
        }
        let mut pairs = pairs.into_iter().collect::<Vec<_>>();
        pairs.sort_by_key(|(pair, count)| (std::cmp::Reverse(*count), *pair));
        let mut step = false;
        for ((x, y), _) in pairs.into_iter().take(8) {
            let mut proposed = Vec::new();
            let mut next = (0usize, 0usize);
            for block in &blocks {
                let Some(phase) = delta(&block.phase, 1 << x, 1 << y, work) else {
                    break 'rounds;
                };
                let Some(c) = delta_cost(&block.phase, &phase, block) else {
                    break 'rounds;
                };
                next.0 += c.0;
                next.1 += c.1;
                proposed.push(phase);
            }
            if next.0 <= current.0 && next.1 < current.1 {
                for (block, phase) in blocks.iter_mut().zip(proposed) {
                    if paths.len() <= 8 {
                        for (mask, coefficient) in phase {
                            insert(&mut block.phase, mask, coefficient);
                        }
                    } else {
                        // Cancel before adding keys so even a wide namespace
                        // cannot transiently grow the mask map beyond 256.
                        let mut updates = Vec::new();
                        for (mask, coefficient) in phase {
                            let mut after = block.phase.get(&mask).cloned().unwrap_or_default();
                            after.add_assign(coefficient);
                            if after.is_zero() {
                                block.phase.remove(&mask);
                            } else {
                                updates.push((mask, after));
                            }
                        }
                        for (mask, coefficient) in updates {
                            block.phase.insert(mask, coefficient);
                        }
                    }
                }
                current = next;
                changed = true;
                step = true;
                break;
            }
        }
        if !step {
            break;
        }
    }
    if !changed {
        return Some(false);
    }
    // Build every free block, including unchanged ones and the constant mask.
    // No collision can join different free monomials; masks are also unique.
    let mut result = KernelPhasePolynomial::default();
    for block in blocks {
        for free in block.free {
            for (&mask, coefficient) in &block.phase {
                let monomial = KernelMonomial::from_variables(
                    free.variables().cloned().chain(
                        paths
                            .iter()
                            .enumerate()
                            .filter(|(i, _)| mask & (1 << i) != 0)
                            .map(|(_, v)| v.clone()),
                    ),
                );
                result.add_term(monomial, coefficient.clone());
            }
        }
    }
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate shared-block move: terms={}->{} cells={}->{} work={work}",
            original.0, current.0, original.1, current.1
        );
    }
    factor.phase = result;
    Some(true)
}

#[cfg(test)]
mod tests {
    use super::*;

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
                    KernelMonomial::from_variables(
                        ends.into_iter().chain([v.clone(), free.clone()]),
                    ),
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
        let oversized =
            PhaseCoefficient::rational(BigRational::new(1.into(), BigInt::from(1) << 300));
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
        let compare = |left: WorkingTerm, right: WorkingTerm| {
            matches_using(
                &Reduction::Sum(Box::new(left)),
                &Reduction::Sum(Box::new(right)),
                true,
                8,
            )
        };
        // Add another disconnected component, required by full factorization.
        let z = KernelVariable::PathKet { term: 4, path: 0 };
        for term in [&mut source, &mut reduced] {
            term.paths.insert(z.clone());
            term.phase
                .add_boolean(&bit(&z), PhaseCoefficient::rational(ratio(1, 8)));
        }
        assert!(compare(source.clone(), reduced.clone()));
        let mut wrong = reduced.clone();
        wrong.coefficient = KernelScalar::Rational(integer(1));
        assert!(!compare(source.clone(), wrong));
        let mut wrong = reduced.clone();
        wrong.constraints.clear();
        assert!(!compare(source.clone(), wrong));
        let mut wrong = reduced.clone();
        wrong
            .phase
            .add_boolean(&bit(&free[3]), PhaseCoefficient::rational(ratio(1, 4)));
        assert!(!compare(source.clone(), wrong));
        let absent = reduced
            .paths
            .iter()
            .find(|v| !reduced.phase.variables().contains(*v))
            .unwrap()
            .clone();
        reduced.paths.remove(&absent);
        assert!(!compare(source, reduced));
    }
}
