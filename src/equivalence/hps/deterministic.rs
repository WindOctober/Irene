//! Specialized path-free comparison; not a replacement for general kernel reasoning.
use super::boolean::{boolean_miter, injectivity_query};
use super::canonical::{ExactMatch, exact_match};
use super::injectivity::triangular_injectivity;
use super::phase::{phase_variation_query, rational_phase_difference};
use super::witness::{validated_model, validated_phase_model};
use super::*;
use crate::equivalence::solver::query::{run_graph_query, run_miter};
use crate::equivalence::solver::smt::{PortfolioConsensus, PortfolioResult, SolverDisagreement};

pub(in crate::equivalence) fn compare(
    prepared: &PreparedComparison,
    kernel_terms: (usize, usize),
    snapshots: Option<(HybridPathSum, HybridPathSum)>,
) -> Option<Result<Analysis, SolverDisagreement>> {
    compare_with(
        prepared,
        kernel_terms,
        snapshots,
        run_miter,
        run_graph_query,
    )
}

// This is an implementation shortcut, not the paper's HPS isomorphism rule.
// Keep output equality, hidden-history, injectivity and phase obligations distinct.
fn compare_with(
    prepared: &PreparedComparison,
    kernel_terms: (usize, usize),
    snapshots: Option<(HybridPathSum, HybridPathSum)>,
    mut run_miter: impl FnMut(&str, &[String]) -> Result<PortfolioResult, SolverDisagreement>,
    mut run_graph_query: impl FnMut(&str) -> Result<PortfolioResult, SolverDisagreement>,
) -> Option<Result<Analysis, SolverDisagreement>> {
    let left = prepared.left.hps.components.first()?;
    let right = prepared.right.hps.components.first()?;
    if prepared.left.hps.components.len() != 1
        || prepared.right.hps.components.len() != 1
        || !left.path_support.is_empty()
        || !right.path_support.is_empty()
        || !left.guard.is_empty()
        || !right.guard.is_empty()
        || left.scalar != Scalar::one()
        || right.scalar != Scalar::one()
    {
        return None;
    }

    let inputs: Vec<_> = prepared.left.hps.input.quantum.keys().cloned().collect();
    let positions = inputs
        .iter()
        .cloned()
        .enumerate()
        .map(|(position, qubit)| (qubit, position))
        .collect::<BTreeMap<_, _>>();
    let left_outputs = &prepared.left.terminals[0].outputs;
    let right_outputs = &prepared.right.terminals[0].outputs;
    let differences = left_outputs
        .iter()
        .zip(right_outputs)
        .map(|(left, right)| left.value.xor(&right.value))
        .filter(|difference| !difference.is_zero())
        .collect::<Vec<_>>();

    let mut solver_queries = Vec::new();
    if !differences.is_empty() {
        let query = boolean_miter(&differences, &positions, "x")?;
        let portfolio = match run_miter(&query, &variable_names(positions.len(), "x")) {
            Ok(result) => result,
            Err(error) => return Some(Err(error)),
        };
        match portfolio.consensus {
            PortfolioConsensus::Sat => {
                // This miter is an exact output-difference encoding. SAT is
                // the certificate; a checked concrete assignment is optional.
                let ket_inputs = validated_model(&portfolio, &differences, &positions, "x");
                let mut analysis = Analysis::new(
                    Verdict::NotEquivalent,
                    Evidence::OutputCounterexample,
                    kernel_terms,
                );
                analysis.counterexample = ket_inputs.map(|ket_inputs| Counterexample {
                    ket_inputs,
                    bra_inputs: None,
                });
                analysis.solver_queries.push(portfolio);
                return Some(Ok(analysis));
            }
            // Structural inequality of XAG roots is not semantic inequality.
            // The exact graph miter being UNSAT proves all outputs identical;
            // continue with the independent history/phase obligations.
            PortfolioConsensus::Unsat => {
                solver_queries.push(portfolio);
            }
            PortfolioConsensus::Inconclusive => {
                let mut analysis =
                    Analysis::new(Verdict::Unknown, Evidence::SolverInconclusive, kernel_terms);
                analysis.solver_queries.push(portfolio);
                return Some(Ok(analysis));
            }
        }
    }

    // TODO: Evaluate whether this deterministic-observation rule is redundant
    // and should be integrated into the exact HPS/isomorphism pipeline.
    // Preserve the admission conditions; phase erasure is not general.
    let all_classical = prepared
        .output_kinds
        .iter()
        .all(|kind| *kind == PreparedOutputKind::Classical);
    if all_classical {
        // TODO: Evaluate whether this rule is redundant and should be integrated
        // into the exact HPS/isomorphism pipeline as observation-aware normalization.
        // Preserve the admission conditions above; phase erasure is not general.
        // For a path-free basis transformer followed only by classical Z
        // observations, phase is unobservable.  Histories still matter: erase
        // only phase and require the complete canonical snapshots to match.
        // Reuse the complete snapshots already built by the structural proof.
        // Tests may call this rule directly without that preceding stage.
        let (mut left_snapshot, mut right_snapshot) = snapshots.unwrap_or_else(|| {
            (
                complete_snapshot(&prepared.left),
                complete_snapshot(&prepared.right),
            )
        });
        left_snapshot.components[0].phase = PhasePolynomial::zero();
        right_snapshot.components[0].phase = PhasePolynomial::zero();
        // Output equality was proved above, not merely guessed from syntax.
        // Align only those certified terminal fields; preserve every residual
        // history/dephasing constraint and all other snapshot fields.
        for (position, output) in left_outputs.iter().enumerate() {
            right_snapshot.components[0].output.classical.insert(
                ClassicalBit {
                    register: SymbolId(0),
                    index: position,
                },
                output.value.clone(),
            );
        }
        if !matches!(
            exact_match(&left_snapshot, &right_snapshot),
            ExactMatch::Match { .. }
        ) {
            return None;
        }
        let mut analysis = Analysis::new(
            Verdict::Equivalent,
            Evidence::DeterministicExact,
            kernel_terms,
        );
        analysis.solver_queries = solver_queries;
        return Some(Ok(analysis));
    }

    if !left.output.history.is_empty() || !right.output.history.is_empty() {
        return None;
    }
    if phases_equal_up_to_global(&left.phase, &right.phase) {
        let mut analysis = Analysis::new(
            Verdict::Equivalent,
            Evidence::DeterministicExact,
            kernel_terms,
        );
        analysis.solver_queries = solver_queries;
        return Some(Ok(analysis));
    }

    // Relative phase is observable only when the selected quantum output is a
    // one-to-one image of every input basis state.  The injectivity and phase
    // variation obligations are separate Boolean/bit-vector SMT queries.
    if prepared
        .output_kinds
        .contains(&PreparedOutputKind::Classical)
        || left_outputs.len() != inputs.len()
    {
        return None;
    }
    let output_values = left_outputs
        .iter()
        .map(|output| output.value.clone())
        .collect::<Vec<_>>();
    if !triangular_injectivity(&output_values, &positions) {
        let injectivity = injectivity_query(&output_values, &positions)?;
        let injectivity_result = match run_graph_query(&injectivity) {
            Ok(result) => result,
            Err(error) => return Some(Err(error)),
        };
        if injectivity_result.consensus != PortfolioConsensus::Unsat {
            let mut analysis =
                Analysis::new(Verdict::Unknown, Evidence::SolverInconclusive, kernel_terms);
            analysis.solver_queries = solver_queries;
            analysis.solver_queries.push(injectivity_result);
            return Some(Ok(analysis));
        }
        solver_queries.push(injectivity_result);
    }

    let delta = rational_phase_difference(&left.phase, &right.phase)?;
    let query = phase_variation_query(&delta, &positions)?;
    let names = variable_names(positions.len(), "x")
        .into_iter()
        .chain(variable_names(positions.len(), "z"))
        .collect::<Vec<_>>();
    let portfolio = match run_miter(&query, &names) {
        Ok(result) => result,
        Err(error) => return Some(Err(error)),
    };
    match portfolio.consensus {
        PortfolioConsensus::Sat => {
            // Injectivity and the exact rational phase encoding were checked
            // above, so model availability is not another proof obligation.
            let inputs = validated_phase_model(&portfolio, &delta, &positions);
            let mut analysis = Analysis::new(
                Verdict::NotEquivalent,
                Evidence::PhaseCounterexample,
                kernel_terms,
            );
            analysis.counterexample = inputs.map(|(ket_inputs, bra_inputs)| Counterexample {
                ket_inputs,
                bra_inputs: Some(bra_inputs),
            });
            analysis.solver_queries = solver_queries;
            analysis.solver_queries.push(portfolio);
            Some(Ok(analysis))
        }
        PortfolioConsensus::Unsat => {
            let mut analysis = Analysis::new(
                Verdict::Equivalent,
                Evidence::DeterministicExact,
                kernel_terms,
            );
            analysis.solver_queries = solver_queries;
            analysis.solver_queries.push(portfolio);
            Some(Ok(analysis))
        }
        PortfolioConsensus::Inconclusive => {
            let mut analysis =
                Analysis::new(Verdict::Unknown, Evidence::SolverInconclusive, kernel_terms);
            analysis.solver_queries = solver_queries;
            analysis.solver_queries.push(portfolio);
            Some(Ok(analysis))
        }
    }
}

fn phases_equal_up_to_global(left: &PhasePolynomial, right: &PhasePolynomial) -> bool {
    let nonconstant = |phase: &PhasePolynomial| {
        phase
            .selectors()
            .filter(|(value, _)| !value.is_one())
            .map(|(value, coefficient)| (value, coefficient.clone()))
            .collect::<Vec<_>>()
    };
    nonconstant(left) == nonconstant(right)
}

fn variable_names(width: usize, namespace: &str) -> Vec<String> {
    (0..width).map(|i| format!("{namespace}{i}")).collect()
}
