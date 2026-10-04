//! Exact kernel constraint preparation and unique bound-path substitution.
use super::kernel::{
    KernelBooleanPolynomial, KernelMonomial, KernelPhasePolynomial, KernelScalar, KernelTerm,
    KernelVariable,
};
use std::collections::{BTreeMap, BTreeSet};
use num_bigint::BigInt;
use num_rational::BigRational;
use scalar::{scalar_conditions_within_budget, scalar_within_budget};
#[cfg(test)]
use scalar::{integer, ratio};

mod checkpoint;
mod checkpoint_factors;
mod collection;
mod constraint_rows;
mod constraints;
mod exact_trig;
mod exact_affine_pivot;
mod factor_match;
mod factor_normalize;
mod factor_rectangle;
mod factor_refine;
mod factor_relation;
mod factorization;
mod free_split;
mod pair_period;
mod factor_pair;
mod path_sum;
mod phase_schedule;
mod phase_unit;
mod product_cases;
mod product_form;
mod scalar;
mod shannon;
mod small_sum;
mod vacuous;
mod witness;
mod xor_basis;
mod xor_blocks;
mod zero_product;

mod exact_smt;

/// Exact squared modulus in the power basis of Q(zeta_(2^62)).
/// The empty vector is zero; all exponents are below 2^61.
pub(super) fn closed_trace_norm(c: &crate::symbolic::Component) -> Option<Vec<(u64, BigRational)>> {
    let (paths, constraints, coefficient, phase) = super::kernel::closed_scalar_parts(c)?;
    exact_smt::closed_norm(WorkingTerm {
        paths,
        constraints,
        coefficient,
        phase,
    })
}

pub(super) fn frontier_trace_norm(circuit: &crate::ir::Program) -> Option<Vec<(u64, BigRational)>> {
    exact_smt::frontier_norm(circuit)
}

pub(super) fn prefer_frontier_trace(circuit: &crate::ir::Program, paths: usize) -> bool {
    exact_smt::prefer_frontier(circuit, paths)
}

const MAX_BOOLEAN_TERMS: usize = 100_000;
const MAX_CONSTRAINTS: usize = 100_000;
const MAX_AFFINE_MATRIX_CELLS: usize = 10_000_000;
const MAX_PHASE_TERMS: usize = 100_000;

#[derive(Clone)]
struct WorkingTerm {
    constraints: Vec<KernelBooleanPolynomial>,
    paths: BTreeSet<KernelVariable>,
    coefficient: KernelScalar,
    phase: KernelPhasePolynomial,
}

enum ConstraintNormalization {
    Normalized,
    Contradiction,
    BudgetExceeded,
}

/// Canonicalizes the GF(2) linear span of complete ANF equations.
///
/// Monomials are formal columns, not independent Boolean inputs. An elementary
/// XOR row operation preserves simultaneous zero evaluation at *every* actual
/// input assignment: `f=0 && g=0` iff `f=0 && (f xor g)=0`. Thus equal row
/// spaces certify equal selectors even for nonlinear equations. This does not
/// compute the Boolean ideal: multiplying equations by variables can yield
/// equivalent selectors with different spans, which remain inconclusive.
///
/// Run once after bound-path elimination; the inner reducer keeps its cheaper
/// affine normal form. Preflight bounds packed matrix storage; decoded rows
/// must also fit the sparse output budget. Both forms use bitgauss RREF.
fn normalize_constraint_span(
    constraints: &mut Vec<KernelBooleanPolynomial>,
) -> ConstraintNormalization {
    match constraint_rows::reduce(&constraints.iter().collect::<Vec<_>>()) {
        Ok(normalized) => {
            *constraints = normalized;
            ConstraintNormalization::Normalized
        }
        Err(status) => status,
    }
}

impl WorkingTerm {
    fn substitution_within_budget(
        &self,
        variable: &KernelVariable,
        replacement: &KernelBooleanPolynomial,
    ) -> bool {
        // Check indexed phase growth first: oversized parity lifts can be
        // rejected without repeatedly scanning every unrelated constraint.
        // These are read-only conjuncts of the same preflight predicate.
        let replacement_terms = replacement.term_count();
        let mut projected_terms = self.phase.term_count() - self.phase.occurrence_count(variable);
        for (_, coefficient) in self.phase.terms_containing(variable) {
            let Some(lifted_terms) = lifted_boolean_term_bound(replacement_terms, coefficient)
            else {
                return false;
            };
            let Some(projected) = projected_terms.checked_add(lifted_terms) else {
                return false;
            };
            projected_terms = projected;
            if projected_terms > MAX_PHASE_TERMS {
                return false;
            }
        }
        self.constraints
            .iter()
            .all(|value| boolean_substitution_within_budget(value, variable, replacement))
            && scalar_substitution_within_budget(&self.coefficient, variable, replacement)
    }

    fn within_budget(&self) -> bool {
        self.constraints.len() <= MAX_CONSTRAINTS
            && self
                .constraints
                .iter()
                .all(|value| value.term_count() <= MAX_BOOLEAN_TERMS)
            && self.phase.term_count() <= MAX_PHASE_TERMS
            && scalar_within_budget(&self.coefficient)
    }
}

/// Bounds one direct ANF substitution without constructing its products.
///
/// A monomial without `variable` contributes at most one output term. A
/// monomial containing it contributes at most one copy of every replacement
/// term after multiplication by the remaining variables. XOR collisions can
/// only decrease that count.
fn boolean_substitution_within_budget(
    polynomial: &KernelBooleanPolynomial,
    variable: &KernelVariable,
    replacement: &KernelBooleanPolynomial,
) -> bool {
    if polynomial.term_count() > MAX_BOOLEAN_TERMS || replacement.term_count() > MAX_BOOLEAN_TERMS {
        return false;
    }

    let replacement_terms = replacement.term_count();
    // A read-only sufficient bound: every old monomial contributes at most
    // max(1, replacement_terms) terms, regardless of whether it contains v.
    // For the usual small constraints, avoid visiting all their monomials on
    // every pivot. If this loose bound fails, retain the exact old preflight.
    if polynomial
        .term_count()
        .checked_mul(replacement_terms.max(1))
        .is_some_and(|bound| bound <= MAX_BOOLEAN_TERMS)
    {
        return true;
    }
    let mut projected_terms = 0usize;
    for monomial in polynomial.terms() {
        let contribution = if monomial.contains(variable) {
            replacement_terms
        } else {
            1
        };
        let Some(projected) = projected_terms.checked_add(contribution) else {
            return false;
        };
        projected_terms = projected;
        if projected_terms > MAX_BOOLEAN_TERMS {
            return false;
        }
    }
    true
}

/// Bounds scalar cloning and every Boolean condition rewritten inside it.
/// Scalar substitution never duplicates an arithmetic node: an undecided
/// select retains both branches and a decided select drops one. The Boolean
/// conditions are the only scalar children whose ANF can expand.
fn scalar_substitution_within_budget(
    scalar: &KernelScalar,
    variable: &KernelVariable,
    replacement: &KernelBooleanPolynomial,
) -> bool {
    scalar_conditions_within_budget(scalar, |condition| {
        boolean_substitution_within_budget(condition, variable, replacement)
    })
}

/// Upper-bounds the number of nonzero arithmetic monomials created by lifting
/// an ANF XOR into a phase. For a rational coefficient with denominator
/// `2^e`, products above degree `e` have integral coefficients and disappear
/// modulo one. Other exact coefficients use the full `2^n - 1` bound.
fn lifted_boolean_term_bound(
    boolean_terms: usize,
    coefficient: &crate::symbolic::PhaseCoefficient,
) -> Option<usize> {
    if boolean_terms == 0 {
        return Some(0);
    }
    let maximum_degree = coefficient.as_rational().map_or(boolean_terms, |value| {
        let mut denominator = value.denom().clone();
        let two = BigInt::from(2);
        let mut exponent = 0usize;
        while &denominator % &two == BigInt::from(0) {
            denominator /= &two;
            exponent += 1;
        }
        if denominator == BigInt::from(1) {
            exponent.min(boolean_terms)
        } else {
            boolean_terms
        }
    });

    let mut total = 0usize;
    let mut binomial = 1usize;
    for degree in 1..=maximum_degree {
        binomial = binomial.checked_mul(boolean_terms + 1 - degree)? / degree;
        total = total.checked_add(binomial)?;
        if total > MAX_PHASE_TERMS {
            return None;
        }
    }
    Some(total)
}
