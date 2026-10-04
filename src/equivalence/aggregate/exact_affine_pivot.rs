//! Transactional two-literal affine substitution after a loose phase bound fails.
//! A retained row v XOR a XOR b=0 uniquely determines the OWNED binder v.
//! Complete phase collisions, including unaffected keys, are computed before
//! commit. No global representation limit or ordinary pivot probe cap changes.
use super::*;
use crate::symbolic::PhaseCoefficient;

pub(super) const WORK_CELLS: usize = 1_000_000;
const SOURCE_CELLS: usize = 750_000;
const DELTA_TERMS: usize = 65536;

fn charge(work: &mut usize, n: usize) -> Option<()> {
    *work = work.checked_sub(n)?;
    Some(())
}

fn rational_small(c: &PhaseCoefficient) -> Option<()> {
    let r = c.as_rational()?;
    (r.numer().bits() <= 256 && r.denom().bits() <= 256).then_some(())
}

/// Exact Boolean idempotence BEFORE building phase keys. In M*(a XOR b),
/// a|M gives M-M*b, both a|M and b|M give zero; otherwise use a+b-2ab.
/// Empty literals are one. Each nonzero output key is constructed directly
/// from the borrowed source, avoiding the old stripped-base/intermediate keys.
fn phase_images(
    m: &KernelMonomial,
    c: &PhaseCoefficient,
    v: &KernelVariable,
    literals: &[&KernelMonomial],
    work: &mut usize,
) -> Option<Vec<(KernelMonomial, PhaseCoefficient)>> {
    rational_small(c)?;
    charge(work, 1)?;
    let present = |literal: &KernelMonomial| literal.variables().all(|w| m.contains(w));
    let images = match (present(literals[0]), present(literals[1])) {
        (true, true) => return Some(Vec::new()),
        (true, false) => vec![(1, c.clone()), (3, c.scaled(BigInt::from(-1)))],
        (false, true) => vec![(2, c.clone()), (3, c.scaled(BigInt::from(-1)))],
        (false, false) => vec![
            (1, c.clone()),
            (2, c.clone()),
            (3, c.scaled(BigInt::from(-2))),
        ],
    };
    let mut result = Vec::new();
    for (mask, value) in images {
        rational_small(&value)?;
        if value.is_zero() {
            continue;
        }
        let added = || {
            literals
                .iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .flat_map(|(_, literal)| literal.variables())
                .filter(|w| !m.contains(w))
        };
        // Removed v accounts for the node cell; append only genuinely NEW
        // variables, so this is precisely the constructed key's syntax size.
        charge(work, m.variables().count() + added().count())?;
        let key = KernelMonomial::from_variables(
            m.variables().filter(|w| *w != v).chain(added()).cloned(),
        );
        result.push((key, value));
    }
    Some(result)
}

/// Construct one changed Boolean row without stripped-base or insertion copies.
/// A containing monomial contributes BOTH literal products over GF(2).
fn guard_image(
    row: &KernelBooleanPolynomial,
    v: &KernelVariable,
    replacement: &KernelBooleanPolynomial,
    work: &mut usize,
) -> Option<KernelBooleanPolynomial> {
    if !boolean_substitution_within_budget(row, v, replacement) {
        return None;
    }
    let mut monomials = Vec::new();
    for m in row.terms() {
        if m.contains(v) {
            for literal in replacement.terms() {
                let added = || literal.variables().filter(|w| !m.contains(w));
                charge(work, m.variables().count() + added().count())?;
                monomials.push(KernelMonomial::from_variables(
                    m.variables().filter(|w| *w != v).chain(added()).cloned(),
                ));
            }
        } else {
            charge(work, 1 + m.variables().count())?;
            monomials.push(m.clone());
        }
    }
    Some(KernelBooleanPolynomial::from_monomials(monomials))
}

struct Plan {
    cancellations: Vec<KernelMonomial>,
    updates: KernelPhasePolynomial,
    guards: BTreeMap<usize, KernelBooleanPolynomial>,
    coefficient: KernelScalar,
    final_terms: usize,
    final_cells: usize,
    partner: Option<(KernelVariable, KernelBooleanPolynomial)>,
}

pub(super) fn scalar_cells(s: &KernelScalar, source: &WorkingTerm) -> Option<usize> {
    let mut pending = vec![s];
    let mut cells = 0usize;
    while let Some(s) = pending.pop() {
        cells = cells.checked_add(1)?;
        match s {
            KernelScalar::Rational(r) => {
                if r.numer().bits() > 32768 || r.denom().bits() > 32768 {
                    return None;
                }
            }
            KernelScalar::Add(a, b) | KernelScalar::Mul(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            KernelScalar::Neg(a) => pending.push(a),
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => {
                for m in condition.terms() {
                    cells = cells.checked_add(1 + m.variables().count())?;
                    if m.variables()
                        .any(|v| v.is_bound_path() && !source.paths.contains(v))
                    {
                        return None;
                    }
                }
                pending.push(when_true);
                pending.push(when_false);
            }
            _ => return None, // No new reasoning about partial scalar domains.
        }
        if cells > 32768 {
            return None;
        }
    }
    Some(cells)
}

/// Failure only spends the shared work allowance. Every source field remains.
fn plan(
    source: &WorkingTerm,
    v: &KernelVariable,
    replacement: &KernelBooleanPolynomial,
    work: &mut usize,
    stage: &mut &'static str,
) -> Option<Plan> {
    if source.paths.len() > 32768
        || source.constraints.len() > 32768
        || !source.within_budget()
        || !source.paths.contains(v)
        || !source.paths.iter().all(KernelVariable::is_bound_path)
        || replacement.term_count() != 2
        || replacement
            .terms()
            .any(|m| m.variables().count() > 1 || m.contains(v))
    {
        return None;
    }
    let definition = replacement.xor(&KernelBooleanPolynomial::variable(v.clone()));
    if !source.constraints.contains(&definition) {
        return None;
    }
    *stage = "source-scan";
    let mut input_cells = source.paths.len();
    let mut occurrences = BTreeMap::<&KernelVariable, usize>::new();
    let mut copresent = BTreeSet::new();
    for (m, _) in source.phase.terms() {
        let cells = 1 + m.variables().count();
        charge(work, cells)?;
        input_cells = input_cells.checked_add(cells)?;
        if input_cells > SOURCE_CELLS
            || m.variables()
                .any(|v| v.is_bound_path() && !source.paths.contains(v))
        {
            return None;
        }
        for w in m.variables().filter(|w| w.is_bound_path()) {
            *occurrences.entry(w).or_default() += 1;
            if m.contains(v) {
                copresent.insert(w);
            }
        }
    }
    let mut partner = None;
    let mut partner_occurrences = 0;
    for row in &source.constraints {
        let mut affine = row.term_count() == 3;
        for m in row.terms() {
            let degree = m.variables().count();
            charge(work, 1 + degree)?;
            input_cells = input_cells.checked_add(1 + degree)?;
            if input_cells > SOURCE_CELLS
                || m.variables()
                    .any(|w| w.is_bound_path() && !source.paths.contains(w))
            {
                return None;
            }
            affine &= degree <= 1 && !m.contains(v);
        }
        if affine {
            charge(work, 4)?; // Bounded three-literal proposal inspection.
            for w in row.terms().flat_map(KernelMonomial::variables) {
                let count = occurrences.get(w).copied().unwrap_or(0);
                if source.paths.contains(w)
                    && w != v
                    && !copresent.contains(w)
                    && !replacement.terms().any(|m| m.contains(w))
                    && count > partner_occurrences
                {
                    partner = Some((w, row));
                    partner_occurrences = count;
                }
            }
        }
    }
    let partner = if let Some((w, row)) = partner {
        charge(work, 8)?;
        Some((
            w.clone(),
            row.xor(&KernelBooleanPolynomial::variable(w.clone())),
        ))
    } else {
        None
    };
    *stage = "scalar-admission";
    let scalar_size = scalar_cells(&source.coefficient, source)?;
    charge(work, scalar_size.checked_mul(4)?)?;
    if input_cells.checked_add(scalar_size)? > SOURCE_CELLS {
        return None;
    }
    *stage = "guard-preflight";
    if !source
        .constraints
        .iter()
        .all(|row| boolean_substitution_within_budget(row, v, replacement))
        || !scalar_substitution_within_budget(&source.coefficient, v, replacement)
    {
        return None;
    }
    // Changed rows are constructed once and moved at commit. Unchanged rows
    // remain in place; every row's substitution has already been preflighted.
    *stage = "guard-images";
    let mut guards = BTreeMap::new();
    for (index, row) in source.constraints.iter().enumerate() {
        if row.terms().any(|m| m.contains(v)) {
            guards.insert(index, guard_image(row, v, replacement, work)?);
        }
    }
    let literals = replacement.terms().collect::<Vec<_>>();
    let mut delta = KernelPhasePolynomial::default();
    let phase_work_start = *work;
    *stage = "phase-delta";
    for (m, c) in source.phase.terms_containing(v) {
        for (key, value) in phase_images(m, c, v, &literals, work)? {
            if delta.coefficient(&key).is_zero()
                && !value.is_zero()
                && delta.term_count() >= DELTA_TERMS
            {
                return None;
            }
            let mut after = delta.coefficient(&key);
            rational_small(&after)?;
            after.add_assign(value.clone());
            rational_small(&after)?;
            delta.add_term(key, value);
        }
    }
    let affected = source.phase.occurrence_count(v);
    let mut final_terms = source.phase.term_count().checked_sub(affected)?;
    let mut final_cells = source
        .phase
        .terms()
        .filter(|(m, _)| !m.contains(v))
        .map(|(m, _)| 1 + m.variables().count())
        .sum::<usize>();
    // Fold ALL unaffected source collisions into final replacement coefficients.
    // Zero entries disappear from this plan, but must still be erased at commit.
    let delta_terms = delta.term_count();
    let mut updates = KernelPhasePolynomial::default();
    let mut cancellations = Vec::new();
    *stage = "phase-collisions";
    for (m, c) in delta.into_terms() {
        charge(work, 1 + m.variables().count())?;
        let before = source.phase.coefficient(&m);
        rational_small(&before)?;
        let mut after = before.clone();
        after.add_assign(c);
        rational_small(&after)?;
        let cells = 1 + m.variables().count();
        if !before.is_zero() {
            final_terms -= 1;
            final_cells -= cells;
        }
        if !after.is_zero() {
            final_terms += 1;
            final_cells += cells;
        }
        if after.is_zero() {
            cancellations.push(m);
        } else {
            updates.add_term(m, after);
        }
    }
    // Return the complete deletion keys AND complete after coefficients.
    // The commit removes all old keys before inserting any new key.
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate exact affine pivot plan: old={} affected={affected} delta={} final={final_terms} final_cells={final_cells} source_cells={input_cells} phase_work_start={phase_work_start} work={work}",
            source.phase.term_count(),
            delta_terms
        );
    }
    *stage = "output-cap";
    if final_terms > MAX_PHASE_TERMS || final_cells > SOURCE_CELLS {
        return None;
    }
    Some(Plan {
        cancellations,
        updates,
        guards,
        coefficient: source.coefficient.substitute(v, replacement),
        final_terms,
        final_cells,
        partner,
    })
}

/// Extend ONE fully checked primary plan using the SAME original admission.
/// The selected definitions are independent and have disjoint SOURCE phase
/// support. All second output collisions are nevertheless checked against the
/// primary after-map, not merely against the original phase. Failure leaves
/// the complete primary plan usable and never resets the work allowance.
fn extend_pair(
    source: &WorkingTerm,
    plan: &mut Plan,
    w: &KernelVariable,
    replacement: &KernelBooleanPolynomial,
    work: &mut usize,
    stage: &mut &'static str,
) -> Option<()> {
    *stage = "pair-scalar";
    charge(
        work,
        scalar_cells(&plan.coefficient, source)?.checked_mul(4)?,
    )?;
    if !scalar_substitution_within_budget(&plan.coefficient, w, replacement) {
        return None;
    }
    *stage = "pair-guards";
    let mut guards = BTreeMap::new();
    for (index, original) in source.constraints.iter().enumerate() {
        let row = plan.guards.get(&index).unwrap_or(original);
        if !boolean_substitution_within_budget(row, w, replacement) {
            return None;
        }
        if row.terms().any(|m| m.contains(w)) {
            guards.insert(index, guard_image(row, w, replacement, work)?);
        }
    }
    let coefficient = plan.coefficient.substitute(w, replacement);
    *stage = "pair-phase-delta";
    let literals = replacement.terms().collect::<Vec<_>>();
    // Reserve the PRIMARY retained keys before building a secondary delta;
    // checking only after construction would permit a transient double cap.
    let delta_limit = DELTA_TERMS
        .checked_sub(plan.updates.term_count())?
        .checked_sub(plan.cancellations.len())?;
    let mut delta = KernelPhasePolynomial::default();
    let mut final_terms = plan.final_terms;
    let mut final_cells = plan.final_cells;
    for (m, c) in source.phase.terms_containing(w) {
        final_terms = final_terms.checked_sub(1)?;
        final_cells = final_cells.checked_sub(1 + m.variables().count())?;
        for (key, value) in phase_images(m, c, w, &literals, work)? {
            if delta.coefficient(&key).is_zero() && delta.term_count() >= delta_limit {
                return None;
            }
            let mut after = delta.coefficient(&key);
            rational_small(&after)?;
            after.add_assign(value.clone());
            rational_small(&after)?;
            delta.add_term(key, value);
        }
    }
    *stage = "pair-phase-collisions";
    let mut updates = KernelPhasePolynomial::default();
    let mut cancellations = Vec::new();
    for (m, c) in delta.into_terms() {
        let cells = 1 + m.variables().count();
        charge(work, cells)?;
        let primary = plan.updates.coefficient(&m);
        let before = if !primary.is_zero() {
            primary
        } else if plan.cancellations.binary_search(&m).is_ok() {
            PhaseCoefficient::default()
        } else {
            source.phase.coefficient(&m)
        };
        rational_small(&before)?;
        let mut after = before.clone();
        after.add_assign(c);
        rational_small(&after)?;
        if !before.is_zero() {
            final_terms = final_terms.checked_sub(1)?;
            final_cells = final_cells.checked_sub(cells)?;
        }
        if after.is_zero() {
            cancellations.push(m);
        } else {
            final_terms += 1;
            final_cells += cells;
            updates.add_term(m, after);
        }
    }
    *stage = "pair-output-cap";
    if final_terms > MAX_PHASE_TERMS || final_cells > SOURCE_CELLS {
        return None;
    }
    // No fallible step remains. Merge complete second AFTER values, including
    // deletion of primary-created keys canceled by the second contribution.
    for m in &cancellations {
        plan.updates.remove_term(m);
    }
    for (m, _) in updates.terms() {
        plan.updates.remove_term(m);
    }
    for (m, c) in updates.into_terms() {
        plan.updates.add_term(m, c);
    }
    plan.cancellations.extend(cancellations);
    plan.guards.extend(guards);
    plan.coefficient = coefficient;
    plan.final_terms = final_terms;
    plan.final_cells = final_cells;
    Some(())
}

pub(super) fn apply(
    source: &mut WorkingTerm,
    v: &KernelVariable,
    replacement: &KernelBooleanPolynomial,
    work: &mut usize,
) -> bool {
    let before_work = *work;
    let mut stage = "entrance";
    let Some(mut planned) = plan(source, v, replacement, work, &mut stage) else {
        if before_work > 0
            && stage != "entrance"
            && std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some()
        {
            eprintln!(
                "aggregate exact affine pivot refused: stage={stage} old={} work_before={before_work} work_left={work}",
                source.phase.term_count()
            );
        }
        return false;
    };
    let mut second = None;
    if let Some((w, rhs)) = planned.partner.take() {
        if extend_pair(source, &mut planned, &w, &rhs, work, &mut stage).is_some() {
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "aggregate exact affine pair: second={w:?} final={} final_cells={} work={work}",
                    planned.final_terms, planned.final_cells
                );
            }
            second = Some(w);
        } else if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "aggregate exact affine pair refused: stage={stage} work={work}; complete primary retained"
            );
        }
    }
    let Plan {
        cancellations,
        updates,
        guards,
        coefficient,
        ..
    } = planned;
    // No fallible step follows. Other fields undergo the SAME unique-value
    // substitution, and the entire defining selector (now zero) remains.
    for (index, row) in guards {
        source.constraints[index] = row;
    }
    source.coefficient = coefficient;
    source.phase.restrict_zero(v);
    if let Some(w) = &second {
        source.phase.restrict_zero(w);
        source.paths.remove(w);
    }
    // Erase every delta key, including the cancelled keys absent from updates.
    // Thus peak phase storage never exceeds max(original, final) syntax.
    for m in &cancellations {
        source.phase.remove_term(m);
    }
    for (m, _) in updates.terms() {
        source.phase.remove_term(m);
    }
    for (m, c) in updates.into_terms() {
        source.phase.add_term(m, c);
    }
    source.paths.remove(v);
    true
}

#[cfg(test)]
mod tests;
