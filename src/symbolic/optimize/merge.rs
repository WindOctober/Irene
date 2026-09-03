//! Coherent and density-level merging of aligned HPS components.
//!
//! This pass preserves the final density-operator semantics selected by
//! [`OutputSelection`](crate::symbolic::OutputSelection), not the complete HPS vector
//! map indexed by classical history. It may run at control-flow joins and
//! discard boundaries because subsequent program operations depend only on
//! the current quantum/classical state, not on hidden past history.

use std::cmp::Ordering;
use std::collections::BTreeSet;

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::symbolic::{Component, HistoryEntry, Scalar};

use super::simplify_component;

/// Whether a history entry denotes one fully determined classical outcome.
///
/// Symbolic entries cannot be used as evidence that two components represent
/// disjoint worlds, because their possible valuations may overlap.
fn history_is_constant(entry: &HistoryEntry) -> bool {
    let value = match entry {
        HistoryEntry::Write { value, .. } | HistoryEntry::Discard { value } => value,
    };
    value.is_zero() || value.is_one()
}

/// First combines amplitudes within each classical world, then combines
/// orthogonal worlds using density weight.
///
/// Components in the same history remain coherent. When their guard, support,
/// phase, and output agree, only their scalar amplitudes differ, so
/// linearity gives `(s1 + s2)|ψ⟩`.
///
/// Components in different constant histories are mutually orthogonal.
/// Suppose two such components both have visible vector `s|ψ⟩`. Their reduced
/// density operator is
///
/// `|sψ⟩⟨sψ| + |sψ⟩⟨sψ| = |√2 s ψ⟩⟨√2 s ψ|`.
///
/// They can therefore become one component with scalar `√2 s` after history
/// is hidden. Distinct histories that remain symbolic or may overlap are left
/// separate by the density-level stage.
pub(crate) fn merge_components(components: Vec<Component>) -> Vec<Component> {
    let mut components = merge_coherent_components(components);
    // Exact structural ordering places every equal visible operator in one
    // contiguous range. This changes only traversal order: grouping still
    // uses the same complete symbolic fields as `same_visible_operator`.
    components.sort_unstable_by(compare_visible_operator);

    let mut merged = Vec::new();
    let mut components = components.into_iter().peekable();
    while let Some(component) = components.next() {
        let mut group = vec![component];
        while components
            .peek()
            .is_some_and(|next| same_visible_operator(&group[0], next))
        {
            group.push(components.next().expect("peeked component exists"));
        }

        // Pairwise-distinct constant histories are mutually exclusive worlds.
        // For non-constant histories, structural overlap would require a
        // symbolic disjointness proof, so this pass leaves them intact. The
        // ordered set detects duplicate histories in O(G log G), rather than
        // comparing all G² pairs in a visible-operator group.
        let mut histories = BTreeSet::new();
        let distinct_constant_worlds = group.len() > 1
            && group.iter().all(|component| {
                component.output.history.iter().all(history_is_constant)
                    && histories.insert(&component.output.history)
            });
        if distinct_constant_worlds {
            let mut component = group.swap_remove(0);
            component.output.history.clear();
            // Density weights add: n|s|² = |√n s|². One component has already
            // been removed from `group`, hence the original size is len + 1.
            let scale = Scalar::sqrt(Scalar::rational(BigRational::from_integer(BigInt::from(
                group.len() + 1,
            ))));
            component.scalar = scale.multiply(component.scalar);
            // Reduce exact scalar products such as √2 · 1/√2 after scaling.
            simplify_component(&mut component);
            merged.push(component);
        } else {
            merged.extend(group);
        }
    }
    merged
}

/// Adds amplitudes of components belonging to the same classical world.
///
/// The compared fields define the same path-sum basis vector pointwise. Only
/// under this exact alignment is replacing two components by one with scalar
/// `s1 + s2` valid. Different phases, guards, supports, or outputs are left to
/// future HPS rewrite rules.
fn merge_coherent_components(mut components: Vec<Component>) -> Vec<Component> {
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

/// Orders density-level candidates while deliberately ignoring hidden history.
fn compare_visible_operator(left: &Component, right: &Component) -> Ordering {
    compare_symbolic_vector(left, right).then_with(|| left.scalar.cmp(&right.scalar))
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
    same_symbolic_vector(left, right) && left.scalar == right.scalar
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
