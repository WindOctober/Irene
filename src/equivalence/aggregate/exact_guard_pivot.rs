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
mod tests {
    use super::*;

    fn bit(v: &KernelVariable) -> KernelBooleanPolynomial {
        KernelBooleanPolynomial::variable(v.clone())
    }

    fn eval(p: &KernelBooleanPolynomial, values: &BTreeMap<KernelVariable, bool>) -> bool {
        p.terms()
            .fold(false, |a, m| a ^ m.variables().all(|v| values[v]))
    }

    fn assert_unchanged(a: &WorkingTerm, b: &WorkingTerm) {
        assert_eq!(a.paths, b.paths);
        assert_eq!(a.constraints, b.constraints);
        assert_eq!(a.coefficient, b.coefficient);
        assert_eq!(a.phase, b.phase);
    }

    #[test]
    fn complete_boolean_images_and_weighted_sums() {
        let v = KernelVariable::PathKet { term: 3, path: 1 };
        let b = KernelVariable::PathBra { term: 3, path: 1 };
        let x = KernelVariable::InputKet(7);
        let y = KernelVariable::ClassicalOutput(2);
        let variables = [b.clone(), x.clone(), y.clone()];
        for mask in 0..256 {
            let rhs = KernelBooleanPolynomial::from_monomials(
                (0..8).filter(|i| mask & (1 << i) != 0).map(|i| {
                    KernelMonomial::from_variables(
                        variables
                            .iter()
                            .enumerate()
                            .filter(|(j, _)| i & (1 << j) != 0)
                            .map(|(_, w)| w.clone()),
                    )
                }),
            );
            let row = bit(&v).and(&rhs).xor(&rhs).xor(&bit(&y));
            let mut source = WorkingTerm {
                paths: BTreeSet::from([v.clone(), b.clone()]),
                constraints: vec![bit(&v).xor(&rhs), row],
                coefficient: KernelScalar::Select {
                    condition: bit(&b),
                    when_true: Box::new(KernelScalar::Rational(ratio(3, 2))),
                    when_false: Box::new(KernelScalar::Rational(ratio(-1, 3))),
                },
                phase: KernelPhasePolynomial::default(),
            };
            source.phase.add_boolean(
                &bit(&b).and(&bit(&x)),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
            );
            let before = source.clone();
            let mut work = exact_affine_pivot::WORK_CELLS;
            assert!(apply(&mut source, &v, &rhs, &mut work));
            for free in 0..4 {
                let mut point =
                    BTreeMap::from([(x.clone(), free & 1 != 0), (y.clone(), free & 2 != 0)]);
                // Complete weighted finite phase histogram, not sampled equality.
                let mut old = [integer(0), integer(0)];
                let mut new = [integer(0), integer(0)];
                for bound in 0..2 {
                    point.insert(b.clone(), bound != 0);
                    let weight = if bound != 0 {
                        ratio(3, 2)
                    } else {
                        ratio(-1, 3)
                    };
                    let power = usize::from(bound != 0 && free & 1 != 0);
                    if source.constraints.iter().all(|p| !eval(p, &point)) {
                        new[power] += &weight;
                    }
                    for value in [false, true] {
                        point.insert(v.clone(), value);
                        if before.constraints.iter().all(|p| !eval(p, &point)) {
                            old[power] += &weight;
                        }
                    }
                }
                assert_eq!(old, new);
            }
            assert_eq!(source.coefficient, before.coefficient);
            assert_eq!(source.phase, before.phase);
            for (a, b) in before.constraints.iter().zip(&source.constraints) {
                assert_eq!(a.substitute(&v, &rhs), *b);
            }
            let required = exact_affine_pivot::WORK_CELLS - work;
            let mut refusal = before.clone();
            assert!(!apply(&mut refusal, &v, &rhs, &mut (required - 1)));
            assert_unchanged(&before, &refusal);
        }
    }

    #[test]
    fn collisions_avoid_false_product_cap_but_live_scratch_stays_bounded() {
        let v = KernelVariable::PathKet { term: 0, path: 0 };
        let rhs = KernelBooleanPolynomial::from_monomials(
            (0..400).map(|i| KernelMonomial::variable(KernelVariable::InputKet(i))),
        );
        let row = bit(&v).and(&rhs).xor(&rhs);
        assert!(!boolean_substitution_within_budget(&row, &v, &rhs));
        // F*F=F in the Boolean ring, hence vF XOR F vanishes under v=F.
        let mut work = exact_affine_pivot::WORK_CELLS;
        assert!(image(&row, &v, &rhs, &mut work).unwrap().is_zero());
        let disjoint = KernelBooleanPolynomial::from_monomials(
            (400..800).map(|i| KernelMonomial::variable(KernelVariable::InputKet(i))),
        );
        let mut work = exact_affine_pivot::WORK_CELLS;
        assert!(image(&bit(&v).and(&disjoint), &v, &rhs, &mut work).is_none());
    }

    #[test]
    fn complete_large_diagram_pivot_avoids_a_million_expanded_products() {
        let v = KernelVariable::PathKet { term: 8, path: 9 };
        // ALL 1024 monomials: F=product_i(1 XOR x_i), not sampled support.
        let rhs = KernelBooleanPolynomial::from_monomials((0..1024).map(|mask| {
            KernelMonomial::from_variables(
                (0..10)
                    .filter(|i| mask & (1 << i) != 0)
                    .map(KernelVariable::InputKet),
            )
        }));
        let row = bit(&v).and(&rhs).xor(&rhs);
        let mut source = WorkingTerm {
            paths: BTreeSet::from([v.clone()]),
            constraints: vec![bit(&v).xor(&rhs), row],
            coefficient: KernelScalar::Rational(ratio(3, 2)),
            phase: KernelPhasePolynomial::default(),
        };
        assert!(!source.substitution_within_budget(&v, &rhs));
        let before = source.clone();
        let mut work = exact_affine_pivot::WORK_CELLS;
        assert!(apply(&mut source, &v, &rhs, &mut work));
        assert!(source.paths.is_empty());
        assert!(
            source
                .constraints
                .iter()
                .all(KernelBooleanPolynomial::is_zero)
        );
        assert_eq!(source.coefficient, before.coefficient);
        assert!(work > 0);
        for free in 0..1024 {
            let mut point = (0..10)
                .map(|i| (KernelVariable::InputKet(i), free & (1 << i) != 0))
                .collect::<BTreeMap<_, _>>();
            let count = [false, true]
                .into_iter()
                .filter(|value| {
                    point.insert(v.clone(), *value);
                    before.constraints.iter().all(|r| !eval(r, &point))
                })
                .count();
            assert_eq!(count, 1);
        }
        // Failure after earlier images still cannot commit the first guard.
        let spent = exact_affine_pivot::WORK_CELLS - work;
        let mut refused = before.clone();
        assert!(!apply(&mut refused, &v, &rhs, &mut (spent - 1)));
        assert_unchanged(&before, &refused);
    }

    #[test]
    fn late_domains_ownership_and_nonunique_or_dependent_pivots_refuse() {
        let v = KernelVariable::PathKet { term: 0, path: 0 };
        let x = KernelVariable::InputKet(0);
        let rhs = bit(&x);
        let original = WorkingTerm {
            paths: BTreeSet::from([v.clone()]),
            constraints: vec![bit(&v).xor(&rhs)],
            coefficient: KernelScalar::Rational(integer(1)),
            phase: KernelPhasePolynomial::default(),
        };
        let mut invalid = Vec::new();
        let mut a = original.clone();
        a.paths.clear();
        invalid.push(a);
        let mut a = original.clone();
        a.constraints[0] = bit(&v).and(&rhs);
        invalid.push(a);
        let mut a = original.clone();
        a.phase.add_boolean(
            &bit(&v),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 4)),
        );
        invalid.push(a);
        let mut a = original.clone();
        a.coefficient = KernelScalar::Select {
            condition: bit(&v),
            when_true: Box::new(KernelScalar::Rational(integer(1))),
            when_false: Box::new(KernelScalar::Rational(integer(2))),
        };
        invalid.push(a);
        let mut a = original.clone();
        a.coefficient = KernelScalar::Select {
            condition: KernelBooleanPolynomial::zero(),
            when_true: Box::new(KernelScalar::Inverse(Box::new(KernelScalar::Rational(
                integer(0),
            )))),
            when_false: Box::new(KernelScalar::Rational(integer(1))),
        };
        invalid.push(a);
        let mut a = original.clone();
        a.constraints
            .push(bit(&KernelVariable::PathBra { term: 9, path: 9 }));
        invalid.push(a);
        for mut bad in invalid {
            let before = bad.clone();
            let mut work = exact_affine_pivot::WORK_CELLS;
            assert!(!apply(&mut bad, &v, &rhs, &mut work));
            assert_unchanged(&before, &bad);
        }
        let mut a = original.clone();
        let mut work = exact_affine_pivot::WORK_CELLS;
        assert!(!apply(&mut a, &v, &bit(&v), &mut work));
        assert_unchanged(&a, &original);
    }
}
