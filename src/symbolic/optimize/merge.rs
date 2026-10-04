//! Coherent and density-level merging of aligned HPS components.
//!
//! This pass preserves the final density-operator semantics selected by
//! [`OutputSelection`](crate::symbolic::OutputSelection), not the complete HPS vector
//! map indexed by classical history. It may run at control-flow joins and
//! discard boundaries because subsequent program operations depend only on
//! the current quantum/classical state, not on hidden past history.

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::symbolic::{BooleanPolynomial, Component, HistoryEntry, PhaseCoefficient, Scalar};

use super::simplify_component;

#[cfg(test)]
pub(super) mod tests;

/// First combines amplitudes within each classical world, then combines
/// orthogonal worlds using density weight.
///
/// Components in the same history remain coherent. When their guard, support,
/// phase, and output agree, only their scalar amplitudes differ, so
/// linearity gives `(s1 + s2)|ψ⟩`.
///
/// Components with provably orthogonal histories contribute density weights,
/// not coherent amplitudes. Suppose two such components have the same visible
/// vector up to a constant phase, with real scalars `s1` and `s2`. Their
/// reduced density operator is
///
/// `s1²|ψ⟩⟨ψ| + s2²|ψ⟩⟨ψ| = |√(s1²+s2²) ψ⟩⟨√(s1²+s2²) ψ|`.
///
/// They can therefore become one component after history is hidden. Histories
/// whose overlap is symbolic are left separate.
///
/// The caller must supply the complete state, or certify a subgroup's
/// isolation from every outside component before and after merging. Partial
/// successors of an unfinished classical branch use coherent merging only.
pub(crate) fn merge_components(components: Vec<Component>) -> Vec<Component> {
    let components = merge_coherent_components(components);
    if !crate::ablation::permit(crate::ablation::Group::FeedbackSummary) {
        return components;
    }

    // Removing an orthogonality record from just one visible-output group can
    // make its representative interfere with representatives of other groups.
    // Density compression is therefore permitted only when *every* remaining
    // component denotes the same visible ray.  Otherwise the exact history
    // sectors are retained for density-kernel construction.
    let Some(first) = components.first() else {
        return components;
    };
    if components.len() < 2
        || components
            .iter()
            .skip(1)
            .any(|component| !same_visible_operator(first, component))
    {
        return components;
    }
    let Some(retained_history) = density_merge_history(&components) else {
        return components;
    };

    let common_scalar = components
        .iter()
        .all(|component| component.scalar == first.scalar);
    if !common_scalar
        && components
            .iter()
            .any(|component| !scalar_is_boolean_independent(&component.scalar))
    {
        // A path/input-dependent scalar is part of the amplitude function.
        // Taking sqrt(sum s_i^2) pointwise loses signs and creates ket/bra
        // cross-products that were absent between distinct histories.
        return components;
    }

    let mut component = first.clone();
    component.output.history = retained_history;
    component.phase.remove_global_phase();
    component.scalar = if common_scalar {
        // All history sectors contain the identical path-sum vector. Retain
        // that vector (including every Boolean-dependent sign) and scale its
        // amplitude by sqrt(n), so its density weight is multiplied by n.
        Scalar::sqrt(Scalar::rational(BigRational::from_integer(BigInt::from(
            components.len(),
        ))))
        .multiply(component.scalar)
    } else {
        // These are genuine global real scalar factors: no Select condition
        // can depend on a ket or bra path/input. Orthogonal sectors therefore
        // add the exact density weight sum_i s_i^2.
        let density_weight = components
            .iter()
            .map(|component| component.scalar.clone().multiply(component.scalar.clone()))
            .reduce(Scalar::sum)
            .expect("at least two components were checked above");
        Scalar::sqrt(density_weight)
    };
    simplify_component(&mut component);
    vec![component]
}

/// Adds amplitudes of components belonging to the same classical world.
///
/// The compared fields define the same path-sum basis vector pointwise. Only
/// under this exact alignment is replacing two components by one with scalar
/// `s1 + s2` valid. Different phases, guards, supports, or outputs are left to
/// future HPS rewrite rules.
pub(crate) fn merge_coherent_components(mut components: Vec<Component>) -> Vec<Component> {
    // Sorting replaces the former repeated scan over the remaining vector.
    // Components compare equal here exactly when their amplitudes may be
    // added: same guard, paths, phase, visible memory, and classical history.
    components.sort_unstable_by(compare_coherent_term);

    let mut merged = Vec::new();
    let mut components = components.into_iter().peekable();
    while let Some(mut component) = components.next() {
        while components
            .peek()
            .is_some_and(|next| same_coherent_term(&component, next))
        {
            let other = components.next().expect("peeked component exists");
            let scalar = std::mem::replace(&mut component.scalar, Scalar::zero());
            component.scalar = scalar.sum(other.scalar);
        }

        if simplify_component(&mut component) && component.scalar != Scalar::zero() {
            merged.push(component);
        }
    }
    merged
}

/// Total structural order for the fields that define one symbolic vector.
///
/// `Equal` is deliberately equivalent to `same_symbolic_vector`; AST IDs and
/// hidden history are absent from both relations.
fn compare_symbolic_vector(left: &Component, right: &Component) -> Ordering {
    left.guard
        .cmp(&right.guard)
        .then_with(|| left.path_support.cmp(&right.path_support))
        .then_with(|| left.phase.cmp(&right.phase))
        .then_with(|| left.output.quantum.cmp(&right.output.quantum))
        .then_with(|| left.output.classical.cmp(&right.output.classical))
}

/// Orders coherent terms while deliberately ignoring their scalar amplitude.
fn compare_coherent_term(left: &Component, right: &Component) -> Ordering {
    compare_symbolic_vector(left, right)
        .then_with(|| left.output.history.cmp(&right.output.history))
}

/// Whether two components are amplitudes of the same basis vector in the same
/// classical world. Scalar is omitted because it is the value being added.
fn same_coherent_term(left: &Component, right: &Component) -> bool {
    same_symbolic_vector(left, right) && left.output.history == right.output.history
}

/// Tests equality of everything retained by output slicing.
///
/// Full history is deliberately omitted: it distinguishes orthogonal worlds
/// before partial trace, while this pass asks whether those worlds contribute
/// the same operator to the final reduced density state.
fn same_visible_operator(left: &Component, right: &Component) -> bool {
    left.guard == right.guard
        && left.path_support == right.path_support
        && nonconstant_phase(left).eq(nonconstant_phase(right))
        && left.output.quantum == right.output.quantum
        && left.output.classical == right.output.classical
}

/// Whether a scalar is an overall real factor rather than a Boolean amplitude
/// profile. Numeric inputs may remain symbolic: unlike a `Select`, they do not
/// vary across the bound paths summed by one HPS invocation.
fn scalar_is_boolean_independent(scalar: &Scalar) -> bool {
    match scalar {
        Scalar::Rational(_) | Scalar::Sin(_) | Scalar::Cos(_) => true,
        Scalar::Sqrt(value) | Scalar::Neg(value) | Scalar::Inverse(value) => {
            scalar_is_boolean_independent(value)
        }
        Scalar::Add(left, right) | Scalar::Mul(left, right) => {
            scalar_is_boolean_independent(left) && scalar_is_boolean_independent(right)
        }
        Scalar::Select { .. } => false,
    }
}

/// Returns the phase terms that survive in a component's density operator.
fn nonconstant_phase(
    component: &Component,
) -> impl Iterator<Item = (BooleanPolynomial, &PhaseCoefficient)> {
    component
        .phase
        .selectors()
        .filter(|(value, _)| !value.is_one())
}

/// Proves that no coherent ket/bra cross term exists between two histories.
///
/// Different shapes cannot be paired by the density-kernel construction. For
/// equal shapes, one unequal pair of constant outcomes makes the conjunction
/// of history equalities false. Symbolic inequalities are deliberately not
/// guessed here.
///
/// Shape mismatch uses the HPS environment-label convention, not a general
/// orthogonality theorem for arbitrary sparse histories. Executor branches
/// retain their distinguishing measurement records, and history compression
/// must preserve isolation from all outside components. Do not independently
/// relabel histories of coherent summands and then apply this test.
pub(super) fn histories_are_orthogonal(left: &[HistoryEntry], right: &[HistoryEntry]) -> bool {
    if left.len() != right.len() {
        return true;
    }
    for (left, right) in left.iter().zip(right) {
        let same_shape = match (left, right) {
            (
                HistoryEntry::Write {
                    target: left_target,
                    ..
                },
                HistoryEntry::Write {
                    target: right_target,
                    ..
                },
            ) => left_target == right_target,
            (HistoryEntry::Discard { .. }, HistoryEntry::Discard { .. }) => true,
            _ => false,
        };
        if !same_shape {
            return true;
        }
        let left_value = HistoryEntry::value(left);
        let right_value = HistoryEntry::value(right);
        let constants = (left_value.is_zero() || left_value.is_one())
            && (right_value.is_zero() || right_value.is_one());
        if constants && left_value != right_value {
            return true;
        }
    }
    false
}

/// Returns the history constraints that remain after a density merge.
///
/// A differing constant outcome can establish orthogonality, but unrelated
/// symbolic history shared by every world must remain. For example,
/// `[y, 0]` and `[y, 1]` may merge along the second coordinate only; dropping
/// `y` as well would incorrectly restore coherence between `y=0` and `y=1`.
fn density_merge_history(group: &[Component]) -> Option<Vec<HistoryEntry>> {
    if group.len() < 2
        || !(0..group.len()).all(|left| {
            (left + 1..group.len()).all(|right| {
                histories_are_orthogonal(&group[left].output.history, &group[right].output.history)
            })
        })
    {
        return None;
    }

    let all_constant = group.iter().all(|component| {
        component.output.history.iter().all(|entry| {
            let value = HistoryEntry::value(entry);
            value.is_zero() || value.is_one()
        })
    });
    if all_constant {
        return Some(Vec::new());
    }

    let width = group[0].output.history.len();
    if group
        .iter()
        .any(|component| component.output.history.len() != width)
    {
        return None;
    }

    let mut retained = Vec::new();
    for position in 0..width {
        let first = &group[0].output.history[position];
        if group
            .iter()
            .all(|component| component.output.history[position] == *first)
        {
            let value = HistoryEntry::value(first);
            if !value.is_zero() && !value.is_one() {
                retained.push(first.clone());
            }
            continue;
        }

        // A varying symbolic coordinate cannot be erased merely because some
        // other constant coordinate proves the worlds orthogonal.
        let same_shape = group.iter().all(|component| {
            matches!(
                (first, &component.output.history[position]),
                (
                    HistoryEntry::Write {
                        target: left_target,
                        ..
                    },
                    HistoryEntry::Write {
                        target: right_target,
                        ..
                    }
                ) if left_target == right_target
            ) || matches!(
                (first, &component.output.history[position]),
                (HistoryEntry::Discard { .. }, HistoryEntry::Discard { .. })
            )
        });
        let all_values_constant = group.iter().all(|component| {
            let value = HistoryEntry::value(&component.output.history[position]);
            value.is_zero() || value.is_one()
        });
        if !same_shape || !all_values_constant {
            return None;
        }
    }
    Some(retained)
}

/// Fields defining the symbolic vector apart from its real scalar and hidden
/// classical history.
fn same_symbolic_vector(left: &Component, right: &Component) -> bool {
    left.guard == right.guard
        && left.path_support == right.path_support
        && left.phase == right.phase
        && left.output.quantum == right.output.quantum
        && left.output.classical == right.output.classical
}
