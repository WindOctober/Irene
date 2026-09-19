//! Local density convergence, using exact changes of HPS summation coordinates.
//!
//! This is a sufficient semantic test, not a complete channel-equivalence oracle.
//! Normalize live output coordinates before hidden histories; remove phases
//! depending only on recorded history; then use the existing exact path rules.
//! No gate names, source patterns, or numerical input samples are inspected.

use std::collections::BTreeSet;

use crate::symbolic::{BooleanPolynomial, Component, HistoryEntry, PhasePolynomial, Variable};

use super::{reduce_path_sums, simplify::substitute_component};

/// Requires an isolated density sector: either a complete singleton state or
/// a local branch group proved orthogonal to every outside component. This is
/// the symbolic-history subroutine, NOT the multi-component join criterion.
///
/// All quantum/classical values here are live according to the backward slice.
/// A pivot visible there cannot subsequently be removed by the history rule.
/// Unknown comparisons and exhausted budgets leave the original untouched.
pub(crate) fn collapse_local_history(component: &mut Component) {
    if !local_history_has_work(component) {
        return;
    }
    let mut candidate = component.clone();
    normalize_coordinates_and_phase(&mut candidate);
    // This certifies that a removed history bit has no dependence in guard,
    // scalar, phase, or live outputs, and a full-rank hidden history pivot.
    // Its two outcomes are orthogonal copies of the SAME input-to-output map:
    // sum_h |A><A| = 2|A><A|, hence sqrt(2), NOT 2, in amplitude.
    if reduce_path_sums(&mut candidate, true)
        && (candidate.path_support.len() < component.path_support.len()
            || candidate.output.history.len() < component.output.history.len())
    {
        *component = candidate;
    }
}

/// Graph-native coordinate substitution does not need a path-count or stored
/// term-count admission limit. Actual expanding backends keep their own limits.
pub(crate) fn local_history_has_work(component: &Component) -> bool {
    // No owned history coordinate means this routine cannot remove a binder
    // or history entry. This is a semantic no-work test, not a size heuristic.
    !component.path_support.is_empty()
        && component.output.history.iter().any(|h| {
            HistoryEntry::value(h)
                .variables()
                .iter()
                .any(|v| matches!(v, Variable::Path(p) if component.path_support.contains(p)))
        })
}

fn normalize_coordinates_and_phase(candidate: &mut Component) {
    let mut fixed = BTreeSet::new();
    // Read each value AFTER preceding substitutions. Earlier visible values
    // are protected by fixing their path coordinates.
    let quantum: Vec<_> = candidate.output.quantum.keys().cloned().collect();
    for key in quantum {
        let value = candidate.output.quantum[&key].factored();
        candidate.output.quantum.insert(key.clone(), value.clone());
        coordinate(candidate, &value, &mut fixed);
    }
    let classical: Vec<_> = candidate.output.classical.keys().cloned().collect();
    for key in classical {
        let value = candidate.output.classical[&key].factored();
        candidate
            .output
            .classical
            .insert(key.clone(), value.clone());
        coordinate(candidate, &value, &mut fixed);
    }
    for index in 0..candidate.output.history.len() {
        let value = HistoryEntry::value(&candidate.output.history[index]).factored();
        match &mut candidate.output.history[index] {
            HistoryEntry::Write {
                value: original, ..
            }
            | HistoryEntry::Discard { value: original } => *original = value.clone(),
        }
        coordinate(candidate, &value, &mut fixed);
    }

    // A pure history coordinate is equal on ket and bra, even if it also
    // appears in live memory. Any real phase depending ONLY on such coordinates
    // cancels exactly. In particular, never discard a phase depending on input
    // x just because it is constant for each fixed computational-basis input.
    let recorded: BTreeSet<_> = candidate
        .output
        .history
        .iter()
        .filter_map(|entry| {
            let value = HistoryEntry::value(entry);
            let variables = value.variables();
            let variable = variables.first()?;
            (matches!(variable, Variable::Path(_))
                && *value == BooleanPolynomial::variable(variable.clone()))
            .then(|| variable.clone())
        })
        .collect();
    let mut phase = PhasePolynomial::zero();
    for (value, coefficient) in candidate.phase.selectors() {
        // Quotient only a function of recorded history: evaluate all other
        // variables at zero, then subtract that phase. This is exact on XAGs
        // and does not require distributing a mixed selector into monomials.
        let hidden = value.map_variables(|v| {
            if recorded.contains(v) {
                BooleanPolynomial::variable(v.clone())
            } else {
                BooleanPolynomial::zero()
            }
        });
        phase.add_boolean(&value, coefficient.clone());
        phase.add_boolean(&hidden, coefficient.scaled((-1).into()));
    }
    candidate.phase = phase;
}

/// For v = y XOR f, where f excludes y, replace old y by new y XOR f.
/// This is a bijection of the bound paths for EVERY fixed input, not a guard
/// assumption. Propagate it through every semantic field, INCLUDING history.
fn coordinate(
    component: &mut Component,
    value: &BooleanPolynomial,
    fixed: &mut BTreeSet<Variable>,
) {
    let variables = value.variables();
    let pivot = variables.iter().find(|v| {
        matches!(v, Variable::Path(p) if component.path_support.contains(p)) && !fixed.contains(*v)
    });
    if value.is_affine()
        && let Some(pivot) = pivot
    {
        if *value != BooleanPolynomial::variable(pivot.clone()) {
            // value itself is y XOR f. substitute_component removes a solved
            // path; restore it because this operation is a reindexing, NOT
            // summation or restriction to one value.
            substitute_component(component, pivot, value);
            if let Variable::Path(path) = pivot {
                component.path_support.insert(*path);
            }
        }
        fixed.insert(pivot.clone());
    } else {
        fixed.extend(variables);
    }
}

#[cfg(test)]
mod tests;
