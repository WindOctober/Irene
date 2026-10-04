//! Complete Boolean-ring substitution when a product-size upper bound refuses.
//! Only an owned, uniquely defined binder absent from phase and ALL scalar
//! branches is eliminated. Every other whole guard becomes H XOR D*F, with
//! Boolean-idempotent duplicate keys toggled before checking its actual size.
//! A failure changes no source field. Work is shared with exact affine pivots.
use super::*;
mod diagram;

const SOURCE_CELLS: usize = 750_000;

fn charge(work: &mut usize, amount: usize) -> Option<()> {
    *work = work.checked_sub(amount)?;
    Some(())
}

#[cfg(test)]
fn image(
    row: &KernelBooleanPolynomial,
    v: &KernelVariable,
    rhs: &KernelBooleanPolynomial,
    work: &mut usize,
) -> Option<KernelBooleanPolynomial> {
    let mut terms = BTreeSet::new();
    let mut stored = 0usize;
    let mut toggle = |m: KernelMonomial| -> Option<()> {
        let cells = 1 + m.variables().count();
        if terms.remove(&m) {
            stored -= cells;
        } else {
            // Reserve before inserting, including all transient uncanceled keys.
            if terms.len() >= MAX_BOOLEAN_TERMS || stored.checked_add(cells)? > SOURCE_CELLS {
                return None;
            }
            stored += cells;
            terms.insert(m);
        }
        Some(())
    };
    // H first allows product collisions to cancel directly against old keys.
    for m in row.terms().filter(|m| !m.contains(v)) {
        charge(work, 1 + m.variables().count())?;
        toggle(m.clone())?;
    }
    for m in row.terms().filter(|m| m.contains(v)) {
        for f in rhs.terms() {
            let added = || f.variables().filter(|w| !m.contains(w));
            charge(work, m.variables().count() + added().count())?;
            toggle(KernelMonomial::from_variables(
                m.variables().filter(|w| *w != v).chain(added()).cloned(),
            ))?;
        }
    }
    // Moving the complete set into the canonical collector still visits keys.
    charge(work, stored)?;
    Some(KernelBooleanPolynomial::from_monomials(terms))
}

fn admit(
    source: &WorkingTerm,
    v: &KernelVariable,
    rhs: &KernelBooleanPolynomial,
    work: &mut usize,
    stage: &mut &'static str,
) -> Option<()> {
    if *work == 0
        || source.paths.len() > 32768
        || source.constraints.len() > 32768
        || rhs.term_count() > MAX_BOOLEAN_TERMS
        || !source.paths.contains(v)
        || !source.paths.iter().all(KernelVariable::is_bound_path)
        || !source.within_budget()
        || source.phase.occurrence_count(v) != 0
    {
        return None;
    }
    *stage = "source";
    let mut cells = source.paths.len();
    charge(work, cells)?;
    for m in source
        .constraints
        .iter()
        .flat_map(KernelBooleanPolynomial::terms)
        .chain(source.phase.terms().map(|(m, _)| m))
        .chain(rhs.terms())
    {
        let n = 1 + m.variables().count();
        charge(work, n)?;
        cells = cells.checked_add(n)?;
        if cells > SOURCE_CELLS
            || m.variables()
                .any(|w| w.is_bound_path() && !source.paths.contains(w))
        {
            return None;
        }
    }
    // Total bounded scalar grammar, including every inactive Select branch.
    let scalar_cells = exact_affine_pivot::scalar_cells(&source.coefficient, source)?;
    charge(work, scalar_cells)?;
    if cells.checked_add(scalar_cells)? > SOURCE_CELLS
        || !scalar_conditions_within_budget(&source.coefficient, |p| {
            p.terms().all(|m| !m.contains(v))
        })
        || rhs.terms().any(|m| m.contains(v))
    {
        return None;
    }
    charge(
        work,
        rhs.terms()
            .map(|m| 1 + m.variables().count())
            .sum::<usize>()
            + 2,
    )?;
    let definition = rhs.xor(&KernelBooleanPolynomial::variable(v.clone()));
    if !source.constraints.contains(&definition) {
        return None;
    }
    Some(())
}

fn plan(
    source: &WorkingTerm,
    v: &KernelVariable,
    rhs: &KernelBooleanPolynomial,
    work: &mut usize,
    stage: &mut &'static str,
) -> Option<BTreeMap<usize, KernelBooleanPolynomial>> {
    admit(source, v, rhs, work, stage)?;
    *stage = "images";
    let mut updates = BTreeMap::new();
    let mut output_cells = 0usize;
    let mut arena = diagram::Arena::default();
    let rhs_id = arena.import(rhs.terms(), None, work)?;
    for (index, row) in source.constraints.iter().enumerate() {
        if row.terms().any(|m| m.contains(v)) {
            let before = *work;
            let result = arena.image(row, v, rhs_id, work);
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "aggregate exact guard image: row={index} old={} derivative={} new={:?} work_before={before} work_left={work} diagram={:?}",
                    row.term_count(),
                    row.terms().filter(|m| m.contains(v)).count(),
                    result.as_ref().map(KernelBooleanPolynomial::term_count),
                    arena.geometry()
                );
            }
            let updated = result?;
            let size = updated
                .terms()
                .map(|m| 1 + m.variables().count())
                .sum::<usize>();
            output_cells = output_cells.checked_add(size)?;
            if output_cells > SOURCE_CELLS {
                return None;
            }
            updates.insert(index, updated);
        }
    }
    Some(updates)
}

pub(super) fn apply(
    source: &mut WorkingTerm,
    v: &KernelVariable,
    rhs: &KernelBooleanPolynomial,
    work: &mut usize,
) -> bool {
    let before = *work;
    let mut stage = "entrance";
    let result = plan(source, v, rhs, work, &mut stage);
    if stage != "entrance" && std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate exact guard pivot: success={} stage={stage} rhs={} work_before={before} work_left={work}",
            result.is_some(),
            rhs.term_count()
        );
    }
    let Some(updates) = result else {
        return false;
    };
    // No fallible step remains; guards are complete, phase/scalar independent.
    for (index, row) in updates {
        source.constraints[index] = row;
    }
    source.paths.remove(v);
    true
}

#[cfg(test)]
mod tests;
