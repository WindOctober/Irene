//! Optional exact phase compaction by reversible bound XOR coordinates.
//!
//! In a factor whose guard/scalar are independent of x, replacing the bound
//! x by x XOR y is a bijection for every value of y. Both binders remain.
//! Only a complete, smaller exact phase is committed; subsequent equality
//! still needs the ordinary complete product certificate. No NEQ is inferred.

use super::*;

mod blocks;
mod checkpoint_components;
mod pair_period;

const INPUT_CELLS: usize = 750_000;
const WORK_CELLS: usize = 1_000_000;
const MAX_LOCAL_TERMS: usize = 8192;

fn charge(cells: &mut usize, amount: usize) -> Option<()> {
    *cells = cells.checked_sub(amount)?;
    Some(())
}

fn admitted(term: &WorkingTerm) -> bool {
    admitted_with_paths(term, 256)
}

pub(super) fn checkpoint_admitted(term: &WorkingTerm) -> bool {
    admitted_with_paths(term, 32768)
}

fn admitted_with_paths(term: &WorkingTerm, max_paths: usize) -> bool {
    if term.paths.len() > max_paths
        || term.constraints.len() > 64
        || !term.paths.iter().all(KernelVariable::is_bound_path)
        || !term.within_budget()
    {
        return false;
    }
    let mut cells = INPUT_CELLS - term.paths.len();
    let mut inspect = |m: &KernelMonomial| {
        charge(&mut cells, 1 + m.variables().count()).is_some()
            && m.variables()
                .all(|v| !v.is_bound_path() || term.paths.contains(v))
    };
    term.constraints
        .iter()
        .all(|row| row.terms().all(&mut inspect))
        && term.phase.terms().all(|(m, _)| inspect(m))
        && scalar_conditions_within_budget(&term.coefficient, |row| row.terms().all(&mut inspect))
}

/// Count only binders absent from EVERY field, including nested conditions.
/// This preserves sum_v 1 = 2 for each omitted Boolean binder. The scan and
/// copies have their own finite input bound; no original expression cap grows.
fn without_vacuous(source: &WorkingTerm) -> Option<WorkingTerm> {
    if !checkpoint_admitted(source) {
        return None;
    }
    let mut active = BTreeSet::new();
    let mut inspect = |row: &KernelBooleanPolynomial| {
        for v in row.terms().flat_map(KernelMonomial::variables) {
            if source.paths.contains(v) {
                active.insert(v.clone());
            }
        }
        active.len() <= 256
    };
    if !source.constraints.iter().all(&mut inspect)
        || !scalar_conditions_within_budget(&source.coefficient, &mut inspect)
    {
        return None;
    }
    for (m, _) in source.phase.terms() {
        for v in m.variables() {
            if source.paths.contains(v) {
                active.insert(v.clone());
            }
        }
        if active.len() > 256 {
            return None;
        }
    }
    let vacuous = source.paths.len() - active.len();
    let mut result = source.clone();
    result.paths = active;
    if vacuous != 0 {
        // Bound the new exact integer and avoid amplifying an already huge
        // rational. Unsupported scalar domains remain ordinary fallbacks.
        result.coefficient = vacuous_weight(result.coefficient, vacuous)?;
    }
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate checkpoint active={} vacuous={vacuous}",
            result.paths.len()
        );
    }
    result.within_budget().then_some(result)
}

/// Multiplication by an exact integer, NOT cancellation of the original
/// possibly zero weight. Select conditions may contain active binders; the
/// caller already checked complete ownership/dependencies. Only total bounded
/// rational arithmetic is admitted, in both branches of every Select.
fn vacuous_weight(coefficient: KernelScalar, vacuous: usize) -> Option<KernelScalar> {
    if vacuous > 32768 {
        return None;
    }
    let mut pending = vec![&coefficient];
    let mut nodes = 0usize;
    while let Some(s) = pending.pop() {
        nodes += 1;
        if nodes > 32768 {
            return None;
        }
        match s {
            KernelScalar::Rational(r) => {
                if r.numer().bits() > 32768 || r.denom().bits() > 32768 {
                    return None;
                }
            }
            KernelScalar::Neg(a) => pending.push(a),
            KernelScalar::Add(a, b) | KernelScalar::Mul(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            KernelScalar::Select {
                when_true,
                when_false,
                ..
            } => {
                pending.push(when_true);
                pending.push(when_false);
            }
            _ => return None,
        }
    }
    Some(
        KernelScalar::Rational(BigRational::from_integer(BigInt::from(1) << vacuous))
            .multiply(coefficient),
    )
}

pub(super) fn matches_checkpoints(
    left: &Reduction,
    right: &Reduction,
    left_checkpoint: Option<&WorkingTerm>,
    right_checkpoint: Option<&WorkingTerm>,
) -> bool {
    if left_checkpoint.is_none() && right_checkpoint.is_none() {
        return false;
    }
    fn source<'a>(
        reduction: &'a Reduction,
        checkpoint: Option<&'a WorkingTerm>,
    ) -> Option<&'a WorkingTerm> {
        match reduction {
            Reduction::Sum(term) => Some(term.as_ref()),
            Reduction::Residual => checkpoint,
            _ => None,
        }
    }
    let (Some(left), Some(right)) = (
        source(left, left_checkpoint),
        source(right, right_checkpoint),
    ) else {
        return false;
    };
    let compacted = (without_vacuous(left), without_vacuous(right));
    let (Some(left), Some(right)) = compacted else {
        return checkpoint_components::matches(left, right);
    };
    // These are complete terms from the explicitly captured checkpoint, not
    // values recovered from Reduction::Residual or a partially accumulated sum.
    matches(
        &Reduction::Sum(Box::new(left)),
        &Reduction::Sum(Box::new(right)),
    )
}

pub(super) fn matches(left: &Reduction, right: &Reduction) -> bool {
    matches_using(left, right, false, 8)
        || matches_using(left, right, true, 8)
        || matches_using(left, right, true, 16)
}

fn matches_using(
    left: &Reduction,
    right: &Reduction,
    shared_blocks: bool,
    block_paths: usize,
) -> bool {
    let (Reduction::Sum(left), Reduction::Sum(right)) = (left, right) else {
        return false;
    };
    if !admitted(left) || !admitted(right) {
        return false;
    }
    let mut work = WORK_CELLS;
    if shared_blocks {
        let (source_left, source_right) = (left.as_ref(), right.as_ref());
        let Some((left, l_changed, l_wide)) = compact_block_factors(left, &mut work, block_paths)
        else {
            return false;
        };
        let Some((right, r_changed, r_wide)) = compact_block_factors(right, &mut work, block_paths)
        else {
            return false;
        };
        if !(l_changed || r_changed) || (block_paths > 8 && !(l_wide || r_wide)) {
            return false;
        }
        // Keep the proven monolithic normal-form route first. If it refuses,
        // reuse the already-complete components without rerunning compaction.
        let reconstruct = |source: &WorkingTerm, factors: &[WorkingTerm]| {
            let mut result = source.clone();
            result.phase = KernelPhasePolynomial::default();
            for factor in factors {
                for (m, c) in factor.phase.terms() {
                    result.phase.add_term(m.clone(), c.clone());
                }
            }
            result
        };
        return prove_terms(
            reconstruct(source_left, &left),
            reconstruct(source_right, &right),
            &mut work,
        ) || factored::matches_components(left, right);
    }
    let Some((left, l_changed)) = compact(left, &mut work) else {
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!("aggregate phase-basis refused: left work={work}");
        }
        return false;
    };
    let Some((right, r_changed)) = compact(right, &mut work) else {
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!("aggregate phase-basis refused: right work={work}");
        }
        return false;
    };
    if !(l_changed || r_changed) {
        return false;
    }
    prove_terms(left, right, &mut work)
}

fn prove_terms(left: WorkingTerm, right: WorkingTerm, work: &mut usize) -> bool {
    debug_term("phase-basis-left", &left);
    debug_term("phase-basis-right", &right);
    let left = reduce_working_term(left);
    let right = reduce_working_term(right);
    if factored::matches(&left, &right) {
        return true;
    }
    if matches_reduced_components(&left, &right, work) {
        return true;
    }
    let mut budget = ReductionBudget {
        splits: MAX_RESIDUAL_SPLITS,
        products: MAX_FACTOR_PRODUCTS,
        phase_cells: MAX_FACTOR_PHASE_CELLS,
    };
    let mut aggregate = |reduction| {
        let mut sum = ExactAggregate::new();
        accumulate_reduction(reduction, &mut sum, &mut 0, &mut budget, 0)?;
        sum.retain(|_, coefficient| !coefficient.is_empty());
        Some(sum)
    };
    let Some(left) = aggregate(left) else {
        return false;
    };
    let Some(right) = aggregate(right) else {
        return false;
    };
    let mut free = MAX_FREE_SPLITS;
    aggregate_difference(left, right).is_some_and(|d| zero_by_free_splitting(d, &mut free, 0))
}

/// Reuse the WHOLE completed local reductions. The monolithic product's
/// entrance may refuse their combined syntax even when the newly separated
/// components meet its unchanged small-factor bounds. Never recover a
/// Residual, rerun compaction, or omit the new common coefficient/guards/phase.
fn matches_reduced_components(left: &Reduction, right: &Reduction, work: &mut usize) -> bool {
    let (Reduction::Sum(left), Reduction::Sum(right)) = (left, right) else {
        return false;
    };
    if !admitted(left) || !admitted(right) {
        return false;
    }
    let (Some(mut left), Some(mut right)) = (
        factor_phase_sums_with_guard_cells(left, INPUT_CELLS),
        factor_phase_sums_with_guard_cells(right, INPUT_CELLS),
    ) else {
        return false;
    };
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!("aggregate reusing complete reduced components");
    }
    // Use remaining compaction work, never a fresh sum/proof allowance.
    // Only oversized small-bound components need this representation change;
    // every complete unchanged factor survives any read-only refusal.
    let mut period_changed = false;
    for factor in left.iter_mut().chain(&mut right) {
        if (2..=3).contains(&factor.paths.len())
            && factor
                .phase
                .terms()
                .map(|(m, _)| 1 + m.variables().count())
                .sum::<usize>()
                > 32768
        {
            period_changed |= pair_period::compact(factor, work).is_some_and(|changed| changed);
        }
    }
    factored::matches_components_refined(left, right, period_changed)
}

fn compact_block_factors(
    source: &WorkingTerm,
    work: &mut usize,
    block_paths: usize,
) -> Option<(Vec<WorkingTerm>, bool, bool)> {
    let mut factors = factor_phase_sums_with_guard_cells(source, INPUT_CELLS)?;
    // The common coefficient/guard remains first for the consuming proof.
    factors[1..].sort_by_key(|f| {
        // Only the wide alternative prioritizes components that cannot yet
        // enter the final eight-binder proof. Original successful scheduling
        // remains unchanged; every factor, including skipped ones, remains.
        let obstructing = block_paths > 8
            && (9..=block_paths).contains(&f.paths.len())
            && f.constraints.is_empty();
        (
            std::cmp::Reverse(obstructing),
            std::cmp::Reverse(f.phase.term_count()),
        )
    });
    let mut changed = false;
    let mut wide_changed = false;
    for factor in &mut factors {
        // In the wide fallback reserve existing work for complete post-local
        // period checks. Both earlier successful eight-bit schedules remain.
        if block_paths > 8 && factor.paths.len() <= 8 && *work < 250_000 {
            continue;
        }
        if factor.paths.len() < 2
            || factor.paths.len() > block_paths
            || factor.phase.term_count() > MAX_LOCAL_TERMS
            || factor.paths.iter().any(|v| factor.occurs_outside_phase(v))
        {
            continue;
        }
        match blocks::compact(factor, work) {
            Some(true) => {
                changed = true;
                wide_changed |= factor.paths.len() > 8;
            }
            Some(false) => {}
            None => break,
        }
    }
    Some((factors, changed, wide_changed))
}

fn compact(source: &WorkingTerm, work: &mut usize) -> Option<(WorkingTerm, bool)> {
    // Complete disconnected components are formed once. The input entrance
    // bounds their combined copied syntax, even when the old product entrance
    // cannot yet admit it. No aggregate or partial factor is accepted here.
    let mut factors = factor_phase_sums_with_guard_cells(source, INPUT_CELLS)?;
    factors.sort_by_key(|f| std::cmp::Reverse(f.phase.term_count()));
    let mut changed = false;
    'factors: for factor in &mut factors {
        if factor.paths.len() < 2
            || factor.paths.len() > 8
            || factor.phase.term_count() > MAX_LOCAL_TERMS
            || factor.paths.iter().any(|v| factor.occurs_outside_phase(v))
        {
            continue;
        }
        let mut local_cells = 32768usize;
        if factor
            .phase
            .terms()
            .any(|(m, _)| charge(&mut local_cells, 1 + m.variables().count()).is_none())
        {
            continue;
        }
        // A small complete factor fits the unchanged occurrence index cap.
        factor.phase.index_occurrences();
        // Finish compacting one component before the next. A breadth-first
        // trial saved more total syntax but regressed actual factor proofs;
        // retain that negative evidence instead of inferring benefit from size.
        for _ in 0..8 {
            let mut pairs = BTreeMap::<(KernelVariable, KernelVariable), usize>::new();
            for (m, _) in factor.phase.terms() {
                if charge(work, 1 + m.variables().count()).is_none() {
                    *work = 0;
                    break 'factors;
                }
                let paths = m
                    .variables()
                    .filter(|v| factor.paths.contains(*v))
                    .collect::<Vec<_>>();
                for x in &paths {
                    for y in &paths {
                        if charge(work, 1).is_none() {
                            *work = 0;
                            break 'factors;
                        }
                        if x != y {
                            *pairs.entry(((*x).clone(), (*y).clone())).or_default() += 1;
                        }
                    }
                }
            }
            let mut pairs = pairs.into_iter().collect::<Vec<_>>();
            pairs.sort_by_key(|(pair, count)| (std::cmp::Reverse(*count), pair.clone()));
            let mut step = false;
            for ((x, y), _) in pairs.into_iter().take(8) {
                let Some(improved) = transvection(&mut factor.phase, &x, &y, work) else {
                    *work = 0;
                    break 'factors;
                };
                if improved {
                    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                        eprintln!(
                            "aggregate phase-basis move: x={x:?} y={y:?} terms={} work={work}",
                            factor.phase.term_count()
                        );
                    }
                    changed = true;
                    step = true;
                    break;
                }
            }
            if !step {
                break;
            }
        }
    }
    if !changed {
        return Some((source.clone(), false));
    }
    let mut result = source.clone();
    result.phase = KernelPhasePolynomial::default();
    for factor in factors {
        for (m, c) in factor.phase.terms() {
            result.phase.add_term(m.clone(), c.clone());
        }
    }
    Some((result, true))
}

/// Build only the affected phase delta. Source keys unaffected by x can
/// still cancel with that delta and are included in the exact cost check.
/// Refusal never mutates the phase, including after partial work charging.
fn transvection(
    phase: &mut KernelPhasePolynomial,
    x: &KernelVariable,
    y: &KernelVariable,
    work: &mut usize,
) -> Option<bool> {
    if x == y {
        return Some(false);
    }
    let mut delta = Vec::new();
    let literal_y = KernelMonomial::variable(y.clone());
    for (m, c) in phase.terms_containing(x) {
        // P=A*x+B*x*y+C*y+D on each monomial of all other coordinates.
        // P[x <- x XOR y]-P = (A+B)*y - 2*(A+B)*x*y.
        // Only two changed keys are built; x-only keys remain untouched.
        // Six source-degree copies cover stripped/counterpart/result keys,
        // sparse delta storage and maintained-index commit, with no old/new
        // polynomial copies or generic XOR-lift maps.
        let copy_cells = 2 + m.variables().count();
        charge(work, 2 * copy_cells)?;
        let mut total = c.clone();
        let (other, y_key, xy_key) = if m.contains(y) {
            let counterpart = m.without(y);
            let other = phase.coefficient(&counterpart);
            if !other.is_zero() {
                continue;
            } // processed by the x-only key
            charge(work, 4 * copy_cells)?;
            (other, m.without(x), m.clone())
        } else {
            charge(work, 4 * copy_cells)?;
            let xy = m.multiply(&literal_y);
            (
                phase.coefficient(&xy),
                m.without(x).multiply(&literal_y),
                xy,
            )
        };
        for coefficient in [&total, &other] {
            let value = coefficient.as_rational()?;
            if value.numer().bits() > 256 || value.denom().bits() > 256 {
                return None;
            }
        }
        total.add_assign(other);
        if !total.is_zero() {
            delta.push((y_key, total.clone()));
            delta.push((xy_key, total.scaled(BigInt::from(-2))));
        }
    }
    let mut removed = 0usize;
    let mut added = 0usize;
    let mut removed_terms = 0usize;
    let mut added_terms = 0usize;
    let mut cancellations = Vec::new();
    let mut updates = Vec::new();
    for (m, c) in delta {
        let before = phase.coefficient(&m);
        let value = before.as_rational()?;
        if value.numer().bits() > 256 || value.denom().bits() > 256 {
            return None;
        }
        let mut after = before.clone();
        after.add_assign(c.clone());
        if !before.is_zero() {
            removed += 1 + m.variables().count();
            removed_terms += 1;
        }
        if !after.is_zero() {
            added += 1 + m.variables().count();
            added_terms += 1;
            updates.push((m, c));
        } else {
            cancellations.push((m, c));
        }
    }
    if added >= removed || added_terms > removed_terms {
        return Some(false);
    }
    // Erase vanishing keys before adding new ones, so neither phase term
    // count nor syntax cells exceed the admitted original during commit.
    // All work and exact after-values were checked before any mutation.
    for (m, c) in cancellations.into_iter().chain(updates) {
        phase.add_term(m, c);
    }
    Some(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::PhaseCoefficient;

    fn bit(v: &KernelVariable) -> KernelBooleanPolynomial {
        KernelBooleanPolynomial::variable(v.clone())
    }

    fn work_budget() -> usize {
        WORK_CELLS
    }

    fn evaluate(
        phase: &KernelPhasePolynomial,
        values: &BTreeMap<KernelVariable, bool>,
    ) -> BigRational {
        phase
            .terms()
            .filter(|(m, _)| m.variables().all(|v| values[v]))
            .map(|(_, c)| c.as_rational().unwrap())
            .sum()
    }

    #[test]
    fn completed_reduction_components_keep_common_weight_phase_guards_and_ownership() {
        let a = KernelVariable::PathKet { term: 0, path: 0 };
        let b = KernelVariable::PathBra { term: 1, path: 0 };
        let free = KernelVariable::InputBra(0);
        let mut source = WorkingTerm {
            paths: BTreeSet::from([a.clone(), b.clone()]),
            constraints: vec![bit(&KernelVariable::InputKet(0))],
            coefficient: KernelScalar::Rational(integer(3)),
            phase: KernelPhasePolynomial::default(),
        };
        for path in [&a, &b] {
            source.phase.add_boolean(
                &bit(path).and(&bit(&free)),
                PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        source
            .phase
            .add_boolean(&bit(&free), PhaseCoefficient::rational(ratio(1, 4)));
        let compare = |left: WorkingTerm, right: WorkingTerm| {
            matches_reduced_components(
                &Reduction::Sum(Box::new(left)),
                &Reduction::Sum(Box::new(right)),
                &mut 0,
            )
        };
        assert!(compare(source.clone(), source.clone()));
        let mut renamed = source.clone();
        let fresh = KernelVariable::PathKet { term: 12, path: 9 };
        renamed.paths.remove(&a);
        renamed.paths.insert(fresh.clone());
        renamed
            .phase
            .rename_variables(&BTreeMap::from([(a.clone(), fresh)]));
        assert!(compare(source.clone(), renamed));
        let mut changed = source.clone();
        changed.coefficient = KernelScalar::Rational(integer(4));
        assert!(!compare(source.clone(), changed));
        let mut changed = source.clone();
        changed.constraints[0] = changed.constraints[0].complement();
        assert!(!compare(source.clone(), changed));
        let mut changed = source.clone();
        changed
            .phase
            .add_boolean(&bit(&free), PhaseCoefficient::rational(ratio(1, 4)));
        assert!(!compare(source.clone(), changed));
        let mut malformed = source.clone();
        malformed.paths.remove(&a);
        assert!(!compare(source.clone(), malformed));
        assert!(!matches_reduced_components(
            &Reduction::Residual,
            &Reduction::Sum(Box::new(source)),
            &mut 0,
        ));
    }

    #[test]
    fn completed_reduction_factorization_keeps_the_eight_binder_local_gate() {
        let paths = (0..10)
            .map(|path| KernelVariable::PathKet { term: 0, path })
            .collect::<Vec<_>>();
        let mut source = WorkingTerm {
            paths: paths.iter().cloned().collect(),
            constraints: Vec::new(),
            coefficient: KernelScalar::Rational(integer(1)),
            phase: KernelPhasePolynomial::default(),
        };
        source.phase.add_term(
            KernelMonomial::from_variables(paths[..9].iter().cloned()),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
        source
            .phase
            .add_boolean(&bit(&paths[9]), PhaseCoefficient::rational(ratio(1, 8)));
        assert!(!matches_reduced_components(
            &Reduction::Sum(Box::new(source.clone())),
            &Reduction::Sum(Box::new(source)),
            &mut 0,
        ));
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
        assert!(!matches(
            &Reduction::Residual,
            &Reduction::Sum(Box::new(source))
        ));
    }

    #[test]
    fn complete_phase_basis_comparison_preserves_relative_weights_and_selectors() {
        let mut left = fixture();
        left.coefficient = KernelScalar::Rational(integer(1));
        let mut right = left.clone();
        let x = KernelVariable::PathKet { term: 0, path: 0 };
        let y = KernelVariable::PathBra { term: 0, path: 0 };
        right.phase.substitute(&x, &bit(&x).xor(&bit(&y)));
        let compare = |a: WorkingTerm, b: WorkingTerm| {
            matches(&Reduction::Sum(Box::new(a)), &Reduction::Sum(Box::new(b)))
        };
        assert!(compare(left.clone(), right.clone()));
        let mut wrong = right.clone();
        wrong.coefficient = KernelScalar::Rational(integer(2));
        assert!(!compare(left.clone(), wrong));
        let mut wrong = right.clone();
        wrong.constraints.clear();
        assert!(!compare(left.clone(), wrong));
        let mut wrong = right.clone();
        wrong.phase.add_boolean(
            &bit(&KernelVariable::InputBra(0)),
            PhaseCoefficient::rational(ratio(1, 4)),
        );
        assert!(!compare(left.clone(), wrong));
        // A removed, now-vacuous binder still carries a factor of two.
        right.paths.remove(&y);
        assert!(!compare(left, right));
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
            let result = without_vacuous(&source).unwrap();
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
        let result = without_vacuous(&nested).unwrap();
        assert_eq!(result.paths, nested.paths);
        assert_eq!(result.coefficient, nested.coefficient);
        nested.paths.remove(&y);
        assert!(without_vacuous(&nested).is_none());
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
                let result = without_vacuous(&source).unwrap();
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
                assert!(without_vacuous(&source).is_none());
                source = before;
                source.coefficient = KernelScalar::Select {
                    condition: bit(&free),
                    when_true: Box::new(KernelScalar::Rational(integer(0))),
                    when_false: Box::new(KernelScalar::Inverse(Box::new(KernelScalar::Rational(
                        integer(0),
                    )))),
                };
                assert!(without_vacuous(&source).is_none());
            }
        }
        assert!(vacuous_weight(KernelScalar::Rational(integer(1)), 32769).is_none());
        assert!(
            vacuous_weight(
                KernelScalar::Rational(BigRational::from_integer(BigInt::from(1) << 32768)),
                1
            )
            .is_none()
        );
    }

    #[test]
    fn checkpoint_capture_is_complete_and_does_not_change_ordinary_refusal() {
        let x = KernelVariable::PathKet { term: 0, path: 0 };
        let y = KernelVariable::PathKet { term: 0, path: 1 };
        let mut large = KernelBooleanPolynomial::zero();
        for i in 0..100 {
            large = large.xor(&bit(&KernelVariable::InputKet(i)));
        }
        let mut source = WorkingTerm {
            paths: BTreeSet::from([x.clone(), y.clone()]),
            constraints: vec![bit(&x).xor(&large)],
            coefficient: KernelScalar::Rational(integer(3)),
            phase: KernelPhasePolynomial::default(),
        };
        source
            .phase
            .add_boolean(&bit(&x), PhaseCoefficient::rational(ratio(1, 8)));
        let mut checkpoint = None;
        assert!(matches!(
            reduce_working_term_with_checkpoint(source.clone(), Some(&mut checkpoint)),
            Reduction::Residual
        ));
        let checkpoint = checkpoint.unwrap();
        // The ordinary reducer already counted the absent y before its next
        // refused pivot. Capture preserves that COMPLETE updated term.
        assert_eq!(checkpoint.paths, BTreeSet::from([x.clone()]));
        assert_eq!(checkpoint.constraints, source.constraints);
        assert_eq!(checkpoint.coefficient, KernelScalar::Rational(integer(6)));
        assert_eq!(checkpoint.phase, source.phase);
        assert!(matches!(reduce_working_term(source), Reduction::Residual));
        assert!(!matches_checkpoints(
            &Reduction::Residual,
            &Reduction::Residual,
            None,
            None
        ));
        let mut oversized = checkpoint.clone();
        oversized
            .paths
            .extend((0..32769).map(|path| KernelVariable::PathKet { term: 7, path }));
        assert!(!checkpoint_admitted(&oversized));
        assert!(without_vacuous(&oversized).is_none());
        let mut missing = checkpoint;
        missing.paths.remove(&x);
        assert!(!checkpoint_admitted(&missing));
    }
}
