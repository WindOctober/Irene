//! Stage 3: lower complete observations to density kernels and aggregate them.
use crate::equivalence::*;
use aggregate::{AggregateComparison, compare_kernels};
use kernel::{KernelInput, KernelTerminalInput, build_kernel};

pub(in crate::equivalence) mod aggregate;
pub(in crate::equivalence) mod kernel;

pub(super) fn compare(prepared: &PreparedComparison) -> Result<Analysis, InterfaceError> {
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!("comparison prepared; kernel build start");
    }
    let left_kernel = match kernel_for(&prepared.left) {
        Ok(kernel) => kernel,
        Err(error) => {
            return Ok(Analysis::new(
                Verdict::Unknown,
                Evidence::KernelBuild(error),
                (0, 0),
            ));
        }
    };
    let right_kernel = match kernel_for(&prepared.right) {
        Ok(kernel) => kernel,
        Err(error) => {
            return Ok(Analysis::new(
                Verdict::Unknown,
                Evidence::KernelBuild(error),
                (left_kernel.terms.len(), 0),
            ));
        }
    };
    let kernel_terms = (left_kernel.terms.len(), right_kernel.terms.len());
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!("kernel build finished; polynomial aggregation start");
    }

    match compare_kernels(&left_kernel, &right_kernel) {
        AggregateComparison::Equivalent => {
            return Ok(Analysis::new(
                Verdict::Equivalent,
                Evidence::DensityKernelExact,
                kernel_terms,
            ));
        }
        AggregateComparison::SmtEquivalent(query) => {
            let mut analysis = Analysis::new(
                Verdict::Equivalent,
                Evidence::DensityKernelExact,
                kernel_terms,
            );
            analysis.solver_queries.push(query);
            return Ok(analysis);
        }
        AggregateComparison::Different(witness, query) => {
            let mut analysis = Analysis::new(
                Verdict::NotEquivalent,
                Evidence::DensityEntryCounterexample,
                kernel_terms,
            );
            analysis.density_counterexample = Some(*witness);
            analysis.solver_queries.push(query);
            return Ok(analysis);
        }
        AggregateComparison::Unknown => {}
    }

    Ok(Analysis::new(
        Verdict::Unknown,
        Evidence::KernelAggregationRequired,
        kernel_terms,
    ))
}

/// Preserve canonical input order and per-kind terminal order when lowering
/// one prepared program. Hidden history stays in the HPS for ket/bra pairing.
fn kernel_for(side: &PreparedSide) -> Result<DensityKernel, KernelBuildError> {
    let input_variables = side.hps.input.quantum.keys().cloned().collect();
    let terminals = side
        .terminals
        .iter()
        .map(|terminal| {
            let mut input = KernelTerminalInput::default();
            for output in &terminal.outputs {
                match output.kind {
                    PreparedOutputKind::Quantum => input.quantum.push(output.value.clone()),
                    PreparedOutputKind::Classical => input.classical.push(output.value.clone()),
                }
            }
            input
        })
        .collect();
    build_kernel(&KernelInput::new(&side.hps, input_variables, terminals))
}
