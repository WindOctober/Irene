//! Stage 2: graph-native HPS certificates, before density-kernel lowering.
use crate::equivalence::*;
use crate::ir::{ClassicalBit, Qubit, SymbolId};
use crate::symbolic::{
    BooleanPolynomial, HistoryEntry, HybridPathSum, Monomial, PhasePolynomial, Scalar, Variable,
};
use canonical::{ExactMatch, exact_match};
use num_rational::BigRational;
use std::collections::{BTreeMap, BTreeSet};

mod boolean;
mod canonical;
mod deterministic;
mod injectivity;
mod pathwise;
mod phase;
mod support;
mod witness;

pub(super) fn compare(prepared: &PreparedComparison) -> Result<Option<Analysis>, InterfaceError> {
    // Graph-native certificates must run before the optional bounded
    // polynomial backend. No ANF expansion is needed for these proofs.
    let kernel_terms = (0, 0);

    // Terminal values are stored outside `PreparedSide::hps`. Reinsert them
    // under canonical keys before applying the exact HPS certificate; omitting
    // them here would prove equality of programs with different outputs.
    //
    // This certificate is deliberately limited to one component on each
    // side. A component is an amplitude summand, not an independently
    // normalized state: in a multi-component HPS, coherence between two
    // summands depends on their histories being positionally compatible.
    // `complete_snapshot` canonicalizes the self-pairing constraints that
    // remain for a single component, so applying it component-by-component
    // would erase precisely that cross-component information.
    let snapshots =
        if prepared.left.hps.components.len() == 1 && prepared.right.hps.components.len() == 1 {
            let left_snapshot = complete_snapshot(&prepared.left);
            let right_snapshot = complete_snapshot(&prepared.right);
            let exact = exact_match(&left_snapshot, &right_snapshot);
            if matches!(exact, ExactMatch::Match { .. }) {
                return Ok(Some(Analysis::new(
                    Verdict::Equivalent,
                    Evidence::ExactHps,
                    kernel_terms,
                )));
            }
            Some((left_snapshot, right_snapshot))
        } else {
            None
        };

    if let Some(analysis) = support::compare(prepared, kernel_terms) {
        return Ok(Some(analysis));
    }

    if let Some(analysis) = deterministic::compare(prepared, kernel_terms, snapshots) {
        return analysis.map(Some).map_err(InterfaceError::from);
    }

    if let Some(result) = pathwise::compare(prepared) {
        return result.map(Some).map_err(InterfaceError::from);
    }

    Ok(None)
}

/// Completes the exact fast-path snapshot with canonical visible outputs.
///
/// History targets are internal names; once current classical outputs are
/// stored separately, their ket/bra equality constraints determine coherence.
/// Classical terminal values impose their own equality constraints, including
/// the terminal Z observation required by mixed quantum/classical pairs.
fn complete_snapshot(side: &PreparedSide) -> HybridPathSum {
    let mut snapshot = side.hps.clone();
    debug_assert_eq!(snapshot.components.len(), 1);
    for (component, terminal) in snapshot.components.iter_mut().zip(&side.terminals) {
        // A constant term multiplies the complete HPS by one global phase.
        // It is irrelevant to the compared density operator even when bound
        // paths remain. The one-component precondition is essential: removing
        // constants separately from multiple components would erase their
        // observable relative phases.
        component.phase.remove_global_phase();
        let classical_outputs = terminal
            .outputs
            .iter()
            .filter(|output| output.kind == PreparedOutputKind::Classical)
            .map(|output| &output.value)
            .collect::<Vec<_>>();
        component.output.history = component
            .output
            .history
            .iter()
            .filter_map(|entry| {
                let value = entry.value().clone();
                // With one component, every kernel term pairs it only with
                // itself. Constant equalities are tautologies, while a
                // history equality repeated by a visible classical output is
                // an idempotent conjunct.
                (!value.is_zero() && !value.is_one() && !classical_outputs.contains(&&value))
                    .then_some(HistoryEntry::Discard { value })
            })
            .collect();
        // At the terminal density boundary, hidden history contributes only
        // the conjunction of ket/bra equalities. Conjunction is commutative
        // and idempotent, so independent measurements may be sorted and
        // duplicate dephasing constraints removed before exact comparison.
        component.output.history.sort();
        component.output.history.dedup();
        for (position, output) in terminal.outputs.iter().enumerate() {
            match output.kind {
                PreparedOutputKind::Quantum => {
                    component.output.quantum.insert(
                        Qubit {
                            register: SymbolId(0),
                            index: position,
                        },
                        output.value.clone(),
                    );
                }
                PreparedOutputKind::Classical => {
                    component.output.classical.insert(
                        ClassicalBit {
                            register: SymbolId(0),
                            index: position,
                        },
                        output.value.clone(),
                    );
                }
            }
        }
    }
    snapshot
}
