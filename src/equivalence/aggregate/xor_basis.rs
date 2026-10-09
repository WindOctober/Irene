//! Reversible XOR changes of bound coordinates in exact phase sums.
//! Only complete, smaller phase rewrites are committed. Both binders remain;
//! a later sum reducer may remove a newly unused binder with its factor of two.
//! This transforms a single side and does not itself prove two sides equal.
use super::scalar::{scalar_conditions_within_budget, scalar_within_budget};
use super::{
    KernelMonomial, KernelPhasePolynomial, KernelVariable, MAX_BOOLEAN_TERMS, MAX_PHASE_TERMS,
    WorkingTerm,
};
use num_bigint::BigInt;
use std::collections::BTreeMap;

const INPUT_CELLS: usize = 750_000;
const MAX_LOCAL_TERMS: usize = 8192;
fn charge(cells: &mut usize, amount: usize) -> Option<()> {
    *cells = cells.checked_sub(amount)?;
    Some(())
}

pub(super) fn admitted(term: &WorkingTerm) -> bool {
    if term.paths.len() > 256
        || term.constraints.len() > 64
        || !term.paths.iter().all(KernelVariable::is_bound_path)
        || !term.phase.is_algebraic()
        || term.phase.term_count() > MAX_PHASE_TERMS
        || !term
            .constraints
            .iter()
            .all(|row| row.is_algebraic() && row.term_count() <= MAX_BOOLEAN_TERMS)
        || !scalar_within_budget(&term.coefficient)
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
        && scalar_conditions_within_budget(&term.coefficient, |row| {
            row.is_algebraic() && row.terms().all(&mut inspect)
        })
}

pub(super) fn compact(source: &WorkingTerm, work: &mut usize) -> Option<(WorkingTerm, bool)> {
    // Complete disconnected components are formed once. The input entrance
    // bounds their combined copied syntax, even when the old product entrance
    // cannot yet admit it. No aggregate or partial factor is accepted here.
    if !admitted(source) {
        return None;
    }
    let mut factors = super::factorization::factor(source, INPUT_CELLS)?;
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
        // Finish each factor before proceeding to the next; all factors,
        // including those skipped or left unchanged, remain in the result.
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
pub(super) fn transvection(
    phase: &mut KernelPhasePolynomial,
    x: &KernelVariable,
    y: &KernelVariable,
    work: &mut usize,
) -> Option<bool> {
    if !x.is_bound_path() || !y.is_bound_path() || !phase.is_algebraic() {
        return None;
    }
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
