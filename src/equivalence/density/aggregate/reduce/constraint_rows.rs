//! Density-kernel adapter for the shared exact monomial row reducer.

use crate::equivalence::density::aggregate::*;
use crate::utils::constraint_rows::{self, Error, Limits};

pub(in crate::equivalence::density::aggregate) fn reduce(
    source: &[&KernelBooleanPolynomial],
) -> Result<Vec<KernelBooleanPolynomial>, ConstraintNormalization> {
    if source.len() > MAX_CONSTRAINTS || source.iter().any(|r| r.term_count() > MAX_BOOLEAN_TERMS) {
        return Err(ConstraintNormalization::BudgetExceeded);
    }
    let rows = source
        .iter()
        .map(|r| r.terms().collect())
        .collect::<Vec<_>>();
    let reduced = constraint_rows::reduce(
        &rows,
        &KernelMonomial::one(),
        Limits {
            rows: MAX_CONSTRAINTS,
            terms: MAX_BOOLEAN_TERMS,
            cells: MAX_AFFINE_MATRIX_CELLS,
        },
        Ord::cmp,
    )
    .map_err(|error| match error {
        Error::BudgetExceeded => ConstraintNormalization::BudgetExceeded,
        Error::Contradiction => ConstraintNormalization::Contradiction,
    })?;
    let mut result: Vec<_> = reduced
        .into_iter()
        .map(KernelBooleanPolynomial::from_monomials)
        .collect();
    result.sort();
    Ok(result)
}
