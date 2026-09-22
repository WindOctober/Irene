//! Exact kernel constraint preparation and unique bound-path substitution.
use super::kernel::{
    KernelBooleanPolynomial, KernelMonomial, KernelPhasePolynomial, KernelScalar, KernelTerm,
    KernelVariable,
};
use std::collections::BTreeSet;

mod checkpoint;
mod checkpoint_factors;
mod collection;
mod constraint_rows;
mod constraints;
mod exact_trig;
mod factor_normalize;
mod factor_rectangle;
mod factor_refine;
mod factor_relation;
mod factorization;
mod free_split;
mod pair_period;
mod path_sum;
mod phase_unit;
mod scalar;
mod shannon;
mod small_sum;
mod vacuous;
mod witness;
mod xor_basis;
mod xor_blocks;
mod zero_product;

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
