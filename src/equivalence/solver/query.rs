//! Execution policy for complete Boolean/bit-vector SMT obligations.
//! This layer returns solver evidence, not EQ/NEQ. Callers establish the
//! encoding's semantic premises and separately validate optional witnesses.
use super::smt::{
    self, PortfolioConsensus, PortfolioResult, Solver, SolverDisagreement, SolverResult,
    SolverStatus,
};

/// Ask for values only after SAT. Model retrieval is optional; a contradictory
/// answer to the same formula is an error, even from the same backend.
pub(in crate::equivalence) fn run_miter(
    query: &str,
    values: &[String],
) -> Result<PortfolioResult, SolverDisagreement> {
    run_miter_with(query, values, run_graph_query)
}

fn run_miter_with(
    query: &str,
    values: &[String],
    mut run: impl FnMut(&str) -> Result<PortfolioResult, SolverDisagreement>,
) -> Result<PortfolioResult, SolverDisagreement> {
    let proof = run(query)?;
    if proof.consensus != PortfolioConsensus::Sat || values.is_empty() {
        return Ok(proof);
    }
    let model = run(&format!("{query}(get-value ({}))\n", values.join(" ")))?;
    combine_same_query_results(proof, model)
}

fn combine_same_query_results(
    proof: PortfolioResult,
    mut model: PortfolioResult,
) -> Result<PortfolioResult, SolverDisagreement> {
    // Keep the definitive proof observation and model diagnostics, including
    // repeated invocations of the same backend. Never resolve by majority vote.
    model.results.extend(proof.results);
    model.consensus = smt::consensus(&model.results)?;
    Ok(model)
}

/// Prefer Bitwuzla; use the existing portfolio only after a non-answer.
pub(in crate::equivalence) fn run_graph_query(
    query: &str,
) -> Result<PortfolioResult, SolverDisagreement> {
    run_graph_query_with(query, smt::run_solver, smt::run_portfolio)
}

fn run_graph_query_with(
    query: &str,
    designated: impl FnOnce(Solver, &str) -> SolverResult,
    fallback: impl FnOnce(&str) -> Result<PortfolioResult, SolverDisagreement>,
) -> Result<PortfolioResult, SolverDisagreement> {
    let result = designated(Solver::Bitwuzla, query);
    let consensus = match result.status {
        SolverStatus::Sat => PortfolioConsensus::Sat,
        SolverStatus::Unsat => PortfolioConsensus::Unsat,
        _ => {
            let mut fallback = fallback(query)?;
            if let Some(bitwuzla) = fallback
                .results
                .iter_mut()
                .find(|r| r.solver == Solver::Bitwuzla)
            {
                bitwuzla.duration += result.duration;
                bitwuzla.stderr = format!(
                    "initial graph attempt: {:?}: {}\n{}",
                    result.status, result.stderr, bitwuzla.stderr
                );
            }
            return Ok(fallback);
        }
    };
    Ok(PortfolioResult {
        consensus,
        results: vec![result],
    })
}
