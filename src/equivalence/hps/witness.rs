//! Optional witnesses using the FSE-Ver parsing and reevaluation policy.
use super::phase::{RationalPhase, evaluate_phase};
use crate::equivalence::solver::smt::{PortfolioResult, SolverStatus};
use crate::ir::Qubit;
use crate::symbolic::{BooleanPolynomial, Variable};
use std::collections::BTreeMap;
fn parse_boolean_values(stdout: &str, width: usize, namespace: &str) -> Option<Vec<bool>> {
    if width == 0 {
        return Some(Vec::new());
    }
    let tokens = stdout
        .replace(['(', ')'], " ")
        .split_whitespace()
        .map(str::to_owned)
        .collect::<Vec<_>>();
    (0..width)
        .map(|index| {
            let name = format!("{namespace}{index}");
            let position = tokens.iter().position(|token| token == &name)?;
            match tokens.get(position + 1).map(String::as_str) {
                Some("true") => Some(true),
                Some("false") => Some(false),
                _ => None,
            }
        })
        .collect()
}
fn input_bindings(values: &[bool], positions: &BTreeMap<Qubit, usize>) -> BTreeMap<Variable, bool> {
    positions
        .iter()
        .map(|(qubit, position)| (Variable::Input(qubit.clone()), values[*position]))
        .collect()
}
pub(in crate::equivalence) fn evaluate_boolean(
    polynomial: &BooleanPolynomial,
    bindings: &BTreeMap<Variable, bool>,
) -> bool {
    polynomial
        .evaluate::<std::convert::Infallible>(|v| Ok(bindings.get(v).copied().unwrap_or(false)))
        .unwrap()
}
pub(in crate::equivalence) fn validated_model(
    portfolio: &PortfolioResult,
    differences: &[BooleanPolynomial],
    positions: &BTreeMap<Qubit, usize>,
    namespace: &str,
) -> Option<Vec<bool>> {
    portfolio
        .results
        .iter()
        .filter(|result| result.status == SolverStatus::Sat)
        .find_map(|result| {
            let values = parse_boolean_values(&result.stdout, positions.len(), namespace)?;
            let bindings = input_bindings(&values, positions);
            differences
                .iter()
                .any(|difference| evaluate_boolean(difference, &bindings))
                .then_some(values)
        })
}
pub(in crate::equivalence) fn validated_phase_model(
    portfolio: &PortfolioResult,
    phase: &RationalPhase,
    positions: &BTreeMap<Qubit, usize>,
) -> Option<(Vec<bool>, Vec<bool>)> {
    portfolio
        .results
        .iter()
        .filter(|result| result.status == SolverStatus::Sat)
        .find_map(|result| {
            let ket = parse_boolean_values(&result.stdout, positions.len(), "x")?;
            let bra = parse_boolean_values(&result.stdout, positions.len(), "z")?;
            let ket_value = evaluate_phase(phase, &input_bindings(&ket, positions));
            let bra_value = evaluate_phase(phase, &input_bindings(&bra, positions));
            (ket_value != bra_value).then_some((ket, bra))
        })
}
