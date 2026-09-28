//! Certified VF2 path matching for the equivalence checker's exact fast path.
//!
//! This module deliberately compares syntax, not arbitrary HPS semantics. In
//! particular, components are summands and must not be compared as a set.  A
//! successful [`exact_match`] is a sound equality certificate because every
//! common component is obtained only by a bijective renaming of its bound
//! path variables.  Failure to match is *not* evidence of inequivalence:
//! changes of variables, interference, and density-kernel aggregation can all
//! make structurally different HPS values denote the same channel.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};

use thiserror::Error;

mod colored_graph;

use crate::symbolic::{
    BooleanPolynomial, Component, HistoryEntry, HybridMemory, HybridPathSum, PhasePolynomial,
    Scalar, Variable,
};

/// Alpha-renamings for all summands into one common reconstructed HPS snapshot.
/// This is not an independently computed graph canonical form.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CanonicalizationCertificate {
    /// Entries are stored in common snapshot component order.
    pub(crate) components: Vec<ComponentAlphaRenaming>,
}

/// A bijection between one source summand's bound paths and its canonical names.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ComponentAlphaRenaming {
    pub(crate) source_component: usize,
    pub(crate) canonical_component: usize,
    pub(crate) forward: BTreeMap<usize, usize>,
    pub(crate) reverse: BTreeMap<usize, usize>,
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub(crate) enum CanonicalizationError {
    #[error("path variable y{path} occurs in the unbound HPS input signature")]
    PathInInput { path: usize },
    #[error("path variable y{path} occurs outside component {component}'s path support")]
    UnboundPath { component: usize, path: usize },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CanonicalSide {
    Left,
    Right,
}

/// Result of the structural exact fast path.
///
/// `NoMatch` means only that this sufficient proof rule did not apply.  It must
/// be mapped to `Unknown` (or followed by density-kernel reasoning), never to a
/// `NotEquivalent` verdict.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ExactMatch {
    Match {
        left: CanonicalizationCertificate,
        right: CanonicalizationCertificate,
    },
    NoMatch,
    Unknown {
        side: CanonicalSide,
        error: CanonicalizationError,
    },
}

/// Compares two complete, already interface-normalized HPS values.
///
/// This function must not be called on `PreparedSide::hps` by itself: interface
/// preparation stores selected observables in parallel terminal rows.  Such a
/// caller must rename/reorder and compare those rows using the returned
/// certificate as part of the same snapshot.
pub(crate) fn exact_match(left: &HybridPathSum, right: &HybridPathSum) -> ExactMatch {
    let started = std::time::Instant::now();
    let result = colored_graph::exact_match(left, right);
    if std::env::var_os("IRENE_ALPHA_STATS").is_some() {
        eprintln!(
            "alpha backend=vf2 paths={:?}/{:?} matched={} elapsed_us={}",
            component_path_counts(left),
            component_path_counts(right),
            matches!(result, ExactMatch::Match { .. }),
            started.elapsed().as_micros(),
        );
    }
    result
}

fn component_path_counts(value: &HybridPathSum) -> Vec<usize> {
    let mut counts = value
        .components
        .iter()
        .map(|component| component.path_support.len())
        .collect::<Vec<_>>();
    counts.sort_unstable();
    counts
}

fn validate(source: &HybridPathSum) -> Result<(), CanonicalizationError> {
    if let Some(path) = paths_in_memory(&source.input).into_iter().next() {
        return Err(CanonicalizationError::PathInInput { path });
    }
    for (component, value) in source.components.iter().enumerate() {
        if let Some(path) = paths_in_component(value)
            .difference(&value.path_support)
            .next()
        {
            return Err(CanonicalizationError::UnboundPath {
                component,
                path: *path,
            });
        }
    }
    Ok(())
}

impl CanonicalizationCertificate {
    /// Checks totality, injectivity, inverse consistency, component pairing,
    /// and exact reconstruction of the canonical snapshot.
    pub(crate) fn verify(&self, source: &HybridPathSum, canonical: &HybridPathSum) -> bool {
        if source.input != canonical.input
            || !paths_in_memory(&source.input).is_empty()
            || source.components.len() != canonical.components.len()
            || self.components.len() != source.components.len()
        {
            return false;
        }

        let mut source_indices = BTreeSet::new();
        let mut canonical_indices = BTreeSet::new();
        for entry in &self.components {
            if !source_indices.insert(entry.source_component)
                || !canonical_indices.insert(entry.canonical_component)
            {
                return false;
            }
            let Some(source_component) = source.components.get(entry.source_component) else {
                return false;
            };
            let Some(canonical_component) = canonical.components.get(entry.canonical_component)
            else {
                return false;
            };
            if !entry.verify(source_component, canonical_component) {
                return false;
            }
        }

        canonical
            .components
            .windows(2)
            .all(|pair| component_cmp(&pair[0], &pair[1]) != Ordering::Greater)
    }
}

impl ComponentAlphaRenaming {
    pub(crate) fn verify(&self, source: &Component, canonical: &Component) -> bool {
        let source_paths = self.forward.keys().copied().collect::<BTreeSet<_>>();
        let canonical_paths = self.forward.values().copied().collect::<BTreeSet<_>>();
        let expected_canonical_paths = (0..source.path_support.len()).collect::<BTreeSet<_>>();
        if source_paths != source.path_support
            || canonical_paths != canonical.path_support
            || canonical_paths != expected_canonical_paths
            || self.forward.len() != canonical_paths.len()
            || !paths_in_component(source).is_subset(&source.path_support)
            || !paths_in_component(canonical).is_subset(&canonical.path_support)
        {
            return false;
        }
        if self.forward.len() != self.reverse.len()
            || self.reverse.keys().copied().collect::<BTreeSet<_>>() != canonical_paths
            || self.reverse.values().copied().collect::<BTreeSet<_>>() != source_paths
            || self
                .forward
                .iter()
                .any(|(from, to)| self.reverse.get(to) != Some(from))
        {
            return false;
        }
        normalize_component(rename_component(source, &self.forward)) == *canonical
    }
}

fn normalize_component(mut component: Component) -> Component {
    component.guard.sort();
    component
}

fn rename_component(source: &Component, map: &BTreeMap<usize, usize>) -> Component {
    Component {
        guard: source
            .guard
            .iter()
            .map(|guard| rename_boolean(guard, map))
            .collect(),
        scalar: rename_scalar(&source.scalar, map),
        path_support: source
            .path_support
            .iter()
            .map(|path| map.get(path).copied().unwrap_or(*path))
            .collect(),
        phase: rename_phase(&source.phase, map),
        output: rename_memory(&source.output, map),
    }
}

fn rename_boolean(source: &BooleanPolynomial, map: &BTreeMap<usize, usize>) -> BooleanPolynomial {
    source.map_variables(|variable| {
        BooleanPolynomial::variable(match variable {
            Variable::Input(input) => Variable::Input(input.clone()),
            Variable::Path(path) => Variable::Path(map.get(path).copied().unwrap_or(*path)),
        })
    })
}

fn rename_phase(source: &PhasePolynomial, map: &BTreeMap<usize, usize>) -> PhasePolynomial {
    let mut renamed = PhasePolynomial::zero();
    for (value, coefficient) in source.selectors() {
        renamed.add_boolean(&rename_boolean(&value, map), coefficient.clone());
    }
    renamed
}

fn rename_scalar(source: &Scalar, map: &BTreeMap<usize, usize>) -> Scalar {
    match source {
        Scalar::Rational(value) => Scalar::Rational(value.clone()),
        Scalar::Sqrt(value) => Scalar::Sqrt(Box::new(rename_scalar(value, map))),
        Scalar::Sin(angle) => Scalar::Sin(angle.clone()),
        Scalar::Cos(angle) => Scalar::Cos(angle.clone()),
        Scalar::Add(left, right) => Scalar::Add(
            Box::new(rename_scalar(left, map)),
            Box::new(rename_scalar(right, map)),
        ),
        Scalar::Mul(left, right) => Scalar::Mul(
            Box::new(rename_scalar(left, map)),
            Box::new(rename_scalar(right, map)),
        ),
        Scalar::Neg(value) => Scalar::Neg(Box::new(rename_scalar(value, map))),
        Scalar::Inverse(value) => Scalar::Inverse(Box::new(rename_scalar(value, map))),
        Scalar::Select {
            condition,
            when_true,
            when_false,
        } => Scalar::Select {
            condition: rename_boolean(condition, map),
            when_true: Box::new(rename_scalar(when_true, map)),
            when_false: Box::new(rename_scalar(when_false, map)),
        },
    }
}

fn rename_memory(source: &HybridMemory, map: &BTreeMap<usize, usize>) -> HybridMemory {
    HybridMemory {
        quantum: source
            .quantum
            .iter()
            .map(|(wire, value)| (wire.clone(), rename_boolean(value, map)))
            .collect(),
        classical: source
            .classical
            .iter()
            .map(|(bit, value)| (bit.clone(), rename_boolean(value, map)))
            .collect(),
        history: source
            .history
            .iter()
            .map(|entry| match entry {
                HistoryEntry::Write { target, value } => HistoryEntry::Write {
                    target: target.clone(),
                    value: rename_boolean(value, map),
                },
                HistoryEntry::Discard { value } => HistoryEntry::Discard {
                    value: rename_boolean(value, map),
                },
            })
            .collect(),
    }
}

fn paths_in_component(component: &Component) -> BTreeSet<usize> {
    let mut paths = BTreeSet::new();
    for guard in &component.guard {
        collect_boolean_paths(guard, &mut paths);
    }
    collect_scalar_paths(&component.scalar, &mut paths);
    for variable in component.phase.variables() {
        if let Variable::Path(path) = variable {
            paths.insert(path);
        }
    }
    paths.extend(paths_in_memory(&component.output));
    paths
}

fn paths_in_memory(memory: &HybridMemory) -> BTreeSet<usize> {
    let mut paths = BTreeSet::new();
    for value in memory.quantum.values().chain(memory.classical.values()) {
        collect_boolean_paths(value, &mut paths);
    }
    for entry in &memory.history {
        let value = entry.value();
        collect_boolean_paths(value, &mut paths);
    }
    paths
}

fn collect_boolean_paths(polynomial: &BooleanPolynomial, paths: &mut BTreeSet<usize>) {
    for variable in polynomial.variables() {
        if let Variable::Path(path) = variable {
            paths.insert(path);
        }
    }
}

fn collect_scalar_paths(scalar: &Scalar, paths: &mut BTreeSet<usize>) {
    match scalar {
        Scalar::Rational(_) | Scalar::Sin(_) | Scalar::Cos(_) => {}
        Scalar::Sqrt(value) | Scalar::Neg(value) | Scalar::Inverse(value) => {
            collect_scalar_paths(value, paths);
        }
        Scalar::Add(left, right) | Scalar::Mul(left, right) => {
            collect_scalar_paths(left, paths);
            collect_scalar_paths(right, paths);
        }
        Scalar::Select {
            condition,
            when_true,
            when_false,
        } => {
            collect_boolean_paths(condition, paths);
            collect_scalar_paths(when_true, paths);
            collect_scalar_paths(when_false, paths);
        }
    }
}

fn memory_cmp(left: &HybridMemory, right: &HybridMemory) -> Ordering {
    left.quantum
        .cmp(&right.quantum)
        .then_with(|| left.classical.cmp(&right.classical))
        .then_with(|| left.history.cmp(&right.history))
}

fn component_cmp(left: &Component, right: &Component) -> Ordering {
    left.guard
        .cmp(&right.guard)
        .then_with(|| left.scalar.cmp(&right.scalar))
        .then_with(|| left.path_support.cmp(&right.path_support))
        .then_with(|| left.phase.cmp(&right.phase))
        .then_with(|| memory_cmp(&left.output, &right.output))
}

#[cfg(test)]
mod tests {
    use num_bigint::BigInt;
    use num_rational::BigRational;

    use super::*;
    use crate::ir::{ClassicalBit, Qubit, SymbolId};
    use crate::symbolic::PhaseCoefficient;

    pub(super) fn q(index: usize) -> Qubit {
        Qubit {
            register: SymbolId(0),
            index,
        }
    }

    pub(super) fn c(index: usize) -> ClassicalBit {
        ClassicalBit {
            register: SymbolId(1),
            index,
        }
    }

    pub(super) fn y(index: usize) -> BooleanPolynomial {
        BooleanPolynomial::variable(Variable::Path(index))
    }

    pub(super) fn x(index: usize) -> BooleanPolynomial {
        BooleanPolynomial::variable(Variable::Input(q(index)))
    }

    pub(super) fn component(paths: &[usize], output: BooleanPolynomial) -> Component {
        Component {
            guard: Vec::new(),
            scalar: Scalar::one(),
            path_support: paths.iter().copied().collect(),
            phase: PhasePolynomial::zero(),
            output: HybridMemory {
                quantum: BTreeMap::from([(q(0), output)]),
                classical: BTreeMap::new(),
                history: Vec::new(),
            },
        }
    }

    pub(super) fn hps(components: Vec<Component>) -> HybridPathSum {
        HybridPathSum {
            input: HybridMemory {
                quantum: BTreeMap::from([(q(0), x(0))]),
                classical: BTreeMap::new(),
                history: Vec::new(),
            },
            components,
        }
    }

    #[test]
    fn ablation_keeps_vf2_alpha_matching() {
        crate::ablation::run(
            crate::ablation::Config::without(crate::ablation::Group::ALL),
            || {
                matches_bijective_path_alpha_renaming_and_component_order();
            },
        );
    }

    #[test]
    fn matches_bijective_path_alpha_renaming_and_component_order() {
        let mut left_first = component(&[3, 8], y(3).xor(&y(8)));
        left_first.guard = vec![y(8).xor(&x(0)), y(3)];
        left_first.output.history = vec![HistoryEntry::Write {
            target: c(0),
            value: y(8),
        }];
        let left_second = component(&[21], y(21));

        let mut right_first = component(&[90, 11], y(90).xor(&y(11)));
        right_first.guard = vec![y(90), y(11).xor(&x(0))];
        right_first.output.history = vec![HistoryEntry::Write {
            target: c(0),
            value: y(11),
        }];
        let right_second = component(&[4], y(4));

        assert!(matches!(
            exact_match(
                &hps(vec![left_first, left_second]),
                &hps(vec![right_second, right_first]),
            ),
            ExactMatch::Match { .. }
        ));
    }

    #[test]
    fn preserves_and_renames_scalar_phase_and_hidden_history() {
        let mut left = component(&[7], y(7));
        left.scalar = Scalar::Select {
            condition: y(7),
            when_true: Box::new(Scalar::one()),
            when_false: Box::new(Scalar::zero()),
        };
        left.phase.add_boolean(
            &y(7),
            PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(8))),
        );
        left.output.history = vec![HistoryEntry::Discard { value: y(7) }];

        let mut right = component(&[42], y(42));
        right.scalar = Scalar::Select {
            condition: y(42),
            when_true: Box::new(Scalar::one()),
            when_false: Box::new(Scalar::zero()),
        };
        right.phase.add_boolean(
            &y(42),
            PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(8))),
        );
        right.output.history = vec![HistoryEntry::Discard { value: y(42) }];

        assert!(matches!(
            exact_match(&hps(vec![left]), &hps(vec![right])),
            ExactMatch::Match { .. }
        ));
    }

    #[test]
    fn rejects_different_path_counts_before_alpha_search() {
        let left = hps(vec![component(&[0, 1], y(0).xor(&y(1)))]);
        let right = hps(vec![component(&[2], y(2))]);

        assert_eq!(exact_match(&left, &right), ExactMatch::NoMatch);
    }
}
