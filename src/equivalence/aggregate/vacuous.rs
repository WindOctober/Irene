//! Remove unused bound coordinates while retaining their exact sum multiplicity.
//! Every guard, phase monomial and nested scalar condition participates in
//! dependency checks. Free coordinates are never removed or summed.
use super::scalar::{scalar_conditions_within_budget, scalar_within_budget};
use super::{
    KernelBooleanPolynomial, KernelMonomial, KernelScalar, KernelVariable, MAX_BOOLEAN_TERMS,
    MAX_CONSTRAINTS, MAX_PHASE_TERMS, WorkingTerm,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::collections::BTreeSet;

const INPUT_CELLS: usize = 750_000;
fn charge(cells: &mut usize, amount: usize) -> Option<()> {
    *cells = cells.checked_sub(amount)?;
    Some(())
}
fn within_budget(term: &WorkingTerm) -> bool {
    term.constraints.len() <= MAX_CONSTRAINTS
        && term
            .constraints
            .iter()
            .all(|row| row.term_count() <= MAX_BOOLEAN_TERMS)
        && term.phase.term_count() <= MAX_PHASE_TERMS
        && scalar_within_budget(&term.coefficient)
}

pub(super) fn admitted(term: &WorkingTerm) -> bool {
    if term.paths.len() > 32768
        || term.constraints.len() > 64
        || !term.paths.iter().all(KernelVariable::is_bound_path)
        || !term.phase.is_algebraic()
        || !within_budget(term)
        || term.constraints.iter().any(|row| !row.is_algebraic())
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

/// Count only binders absent from EVERY field, including nested conditions.
/// This preserves sum_v 1 = 2 for each omitted Boolean binder. The scan and
/// copies have their own finite input bound; no original expression cap grows.
pub(super) fn remove(source: &WorkingTerm) -> Option<WorkingTerm> {
    if !admitted(source) {
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
        result.coefficient = weight(result.coefficient, vacuous)?;
    }
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate checkpoint active={} vacuous={vacuous}",
            result.paths.len()
        );
    }
    within_budget(&result).then_some(result)
}

/// Multiplication by an exact integer, NOT cancellation of the original
/// possibly zero weight. Select conditions may contain active binders; the
/// caller already checked complete ownership/dependencies. Only total bounded
/// rational arithmetic is admitted, in both branches of every Select.
fn weight(coefficient: KernelScalar, vacuous: usize) -> Option<KernelScalar> {
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
