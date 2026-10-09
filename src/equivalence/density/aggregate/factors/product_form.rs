//! Assemble complete exact factor sums into a common term and residual factors.
use super::factor_normalize::normalize as normalize_factor;
use super::factor_relation::add_phase;
use crate::equivalence::density::aggregate::collection::{
    ExactAggregate, ExactTerm, accumulate_exact_term,
};
use crate::equivalence::density::aggregate::phase::phase_unit::charge_cells;
use crate::equivalence::density::aggregate::scalar::{
    integer, normalize_scalar, scalar_conditions_within_budget, scalar_within_budget,
};
use crate::equivalence::density::aggregate::{
    KernelMonomial, KernelPhasePolynomial, KernelScalar, WorkingTerm,
};
use std::collections::{BTreeMap, BTreeSet};

const MAX_FACTORS: usize = 128;
const MAX_FACTOR_ATOMS: usize = 256;
const MAX_STORED_ATOMS: usize = 4096;
const MAX_FACTOR_PHASE_CELLS: usize = 250_000;
const MAX_SPLIT_DEPTH: usize = 8;

#[derive(Clone)]
pub(in crate::equivalence::density::aggregate) struct Product {
    pub(in crate::equivalence::density::aggregate) common: ExactAggregate,
    pub(in crate::equivalence::density::aggregate) factors: Vec<ExactAggregate>,
}

/// Every returned value covers its WHOLE operand. All methods share the
/// backend's proof budget; refusal is None, never a successful prefix.
/// Refinement returns a complete equivalent product (empty means identity).
pub(in crate::equivalence::density::aggregate) trait Reduction {
    fn exact(&mut self, term: WorkingTerm) -> Option<ExactTerm>;
    fn sum(&mut self, term: WorkingTerm, shared_small: bool) -> Option<(ExactAggregate, usize)>;
    fn refine(&mut self, sum: ExactAggregate, rectangles: bool) -> Option<Vec<ExactAggregate>>;
    fn finish(&mut self, term: WorkingTerm) -> Option<ExactAggregate>;
}

/// The first factor is the common term. Every later factor is retained or
/// absorbed with ALL of its selector, weight and phase. None discards the
/// entire construction, including common contributions already accumulated.
pub(in crate::equivalence::density::aggregate) fn build(
    factors: Vec<WorkingTerm>,
    backend: &mut impl Reduction,
    shared_small: bool,
    prefer_rectangles: bool,
) -> Option<Product> {
    if factors.len() > MAX_FACTORS + 1 {
        return None;
    }
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate factored groups: {:?}",
            factors
                .iter()
                .map(|factor| factor.paths.len())
                .collect::<Vec<_>>()
        );
    }
    // Keep all previously admitted component proofs on their old schedule.
    // This extra representation is relevant only to the new large-input route.
    let rectangles = prefer_rectangles
        || shared_small
            && factors.iter().any(|f| {
                f.phase
                    .terms()
                    .map(|(m, _)| 1 + m.variables().count())
                    .sum::<usize>()
                    > 32768
            });
    let mut factors = factors.into_iter();
    let mut common = backend.exact(factors.next()?)?;
    let selector = common.constraints.clone();
    let mut unit = ExactAggregate::new();
    let mut unit_atoms = 0;
    accumulate_exact_term(
        ExactTerm {
            constraints: selector.clone(),
            coefficient: KernelScalar::Rational(integer(1)),
            phase: KernelPhasePolynomial::default(),
        },
        &mut unit,
        &mut unit_atoms,
    )?;
    let mut normalized = Vec::new();
    let mut stored_atoms = 0usize;
    let mut cells_remaining = MAX_FACTOR_PHASE_CELLS;
    for mut factor in factors {
        if factor.paths.len() > MAX_SPLIT_DEPTH {
            return None;
        }
        let mut cells = 0usize;
        let large = shared_small && {
            let mut inspect = |m: &KernelMonomial| {
                cells = cells.saturating_add(1 + m.variables().count());
                true
            };
            factor
                .constraints
                .iter()
                .all(|r| r.terms().all(&mut inspect));
            factor.phase.terms().all(|(m, _)| inspect(m));
            scalar_conditions_within_budget(&factor.coefficient, |r| r.terms().all(&mut inspect));
            cells > 32768
        };
        // Duplicating the same indicator is exact: [G]^k=[G]. This lets
        // each factor use G without dropping G from the final product.
        // Select the representation BEFORE adding these common guards so
        // every previously admitted small factor retains its old scheduler.
        factor.constraints.extend(selector.iter().cloned());
        let (sum, atoms) = backend.sum(factor, large)?;
        if atoms > MAX_FACTOR_ATOMS {
            return None;
        }
        // Charge retained selectors and phase syntax before normalizing and
        // replaying a factor. Atom count alone does not bound their storage.
        charge_cells(&sum, &mut cells_remaining)?;
        let refined = backend.refine(sum, rectangles)?;
        for sum in refined {
            let (sum, scalar, phase) = normalize_factor(sum)?;
            common.coefficient =
                normalize_scalar(common.coefficient.multiply(KernelScalar::Rational(scalar)));
            add_phase(&mut common.phase, &phase)?;
            if !scalar_within_budget(&common.coefficient) {
                return None;
            }
            stored_atoms =
                stored_atoms.checked_add(sum.values().map(BTreeMap::len).sum::<usize>())?;
            if stored_atoms > MAX_STORED_ATOMS {
                return None;
            }
            charge_cells(&sum, &mut cells_remaining)?;
            if sum == unit {
                continue;
            }
            if sum.values().map(BTreeMap::len).sum::<usize>() == 1 {
                // A one-atom factor belongs in the common term, including
                // its OWN selector (which may be stronger than the original
                // common selector after reducing a guarded bound factor).
                let (entry, values) = sum.into_iter().next()?;
                let (phase, scalar) = values.into_iter().next()?;
                common.constraints.extend(entry.constraints);
                common.coefficient = normalize_scalar(common.coefficient.multiply(scalar));
                add_phase(&mut common.phase, &phase)?;
                continue;
            }
            normalized.push(sum);
            if normalized.len() > MAX_FACTORS {
                return None;
            }
        }
    }
    let common = WorkingTerm {
        paths: BTreeSet::new(),
        constraints: common.constraints,
        coefficient: common.coefficient,
        phase: common.phase,
    };
    let aggregate = backend.finish(common)?;
    Some(Product {
        common: aggregate,
        factors: normalized,
    })
}
