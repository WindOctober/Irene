//! Sufficient input-recovery certificates for Boolean output maps.
//! No solver calls and no equivalence verdicts: false only means no proof.
use crate::ir::Qubit;
use crate::symbolic::{BooleanPolynomial, Variable};
use bitgauss::BitMatrix;
use std::collections::{BTreeMap, BTreeSet};

/// A sufficient injectivity proof by recovering inputs from output values.
/// If an output is `x xor f(K)`, where every variable in K is already
/// recoverable, then x is recoverable too. Constants do not affect the rule.
/// Importantly, x must occur only as a singleton: `x xor x*y` is not a
/// recovery equation. Failure (including the work cap) is inconclusive, not non-injectivity.
pub(super) fn triangular_injectivity(
    outputs: &[BooleanPolynomial],
    inputs: &BTreeMap<Qubit, usize>,
) -> bool {
    with_budget(outputs, inputs, 1_000_000)
}

fn with_budget(
    outputs: &[BooleanPolynomial],
    inputs: &BTreeMap<Qubit, usize>,
    mut budget: usize,
) -> bool {
    let mut rows = Vec::new();
    for output in outputs {
        let Some(remaining) = budget.checked_sub(1) else {
            return false;
        };
        budget = remaining;
        let mut linear = BTreeSet::new();
        let mut nonlinear = BTreeSet::new();
        let factors = output.xor_terms();
        for factor in &factors {
            for variable in factor.variables() {
                let Some(remaining) = budget.checked_sub(1) else {
                    return false;
                };
                budget = remaining;
                let Variable::Input(input) = variable else {
                    return false;
                };
                if !inputs.contains_key(&input) {
                    return false;
                }
                if factor.as_variable().is_some() {
                    linear.insert(input.clone());
                } else {
                    nonlinear.insert(input.clone());
                }
            }
        }
        rows.push((linear, nonlinear));
    }
    let mut known = BTreeSet::new();
    loop {
        if known.len() == inputs.len() {
            return true;
        }
        let before = known.len();
        for (linear, nonlinear) in &rows {
            let Some(remaining) = budget.checked_sub(linear.len() + nonlinear.len() + 1) else {
                return false;
            };
            budget = remaining;
            if !nonlinear.is_subset(&known) {
                continue;
            }
            let mut unresolved = linear.difference(&known);
            if let Some(input) = unresolved.next()
                && unresolved.next().is_none()
            {
                known.insert(input.clone());
            }
        }
        if known.len() == before {
            // Known nonlinear contributions can be removed from each output
            // value. XOR combinations of the remaining linear forms are
            // therefore also recoverable. RREF may expose a singleton that
            // is not present in any original output (e.g. a linear mixer).
            let eligible = rows
                .iter()
                .filter(|(_, nonlinear)| nonlinear.is_subset(&known))
                .map(|(linear, _)| linear)
                .collect::<Vec<_>>();
            let columns = inputs
                .keys()
                .filter(|input| !known.contains(input))
                .collect::<Vec<_>>();
            let Some(remaining) = eligible
                .len()
                .checked_mul(columns.len())
                .and_then(|cells| budget.checked_sub(cells))
            else {
                return false;
            };
            budget = remaining;
            if eligible.is_empty() {
                return false;
            }
            let mut matrix = BitMatrix::build(eligible.len(), columns.len(), |row, column| {
                eligible[row].contains(columns[column])
            });
            matrix.gauss(true);
            for row in 0..eligible.len() {
                let mut nonzero = (0..columns.len()).filter(|column| matrix.bit(row, *column));
                if let Some(column) = nonzero.next()
                    && nonzero.next().is_none()
                {
                    known.insert(columns[column].clone());
                }
            }
            if known.len() == before {
                return false;
            }
        }
    }
}
