//! Full-unitary trace certificate, before independent density construction.
use super::{Endpoint, EquivalenceConfig, InputPair, OutputPair};
use crate::{
    ir::{Gate, Program, StatementKind, unitary},
    symbolic::{ExecutionConfig, OutputSelection, Scalar, execute, normalized_trace_component},
};
use num_rational::BigRational;

#[derive(Debug, PartialEq, Eq)]
pub(super) enum TraceNorm {
    Rational(BigRational),
}

impl TraceNorm {
    pub(super) fn is_one(&self) -> bool {
        matches!(self, Self::Rational(r) if *r == BigRational::from_integer(1.into()))
    }
}

/// For d-dimensional unitaries L,R, |Tr(L†R)|=d iff R=e^(it)L.
/// This follows from equality in Hilbert-Schmidt Cauchy-Schwarz, since
/// ||I||²=||L†R||²=d. It tests all coherent inputs, not basis output samples.
pub(super) fn certificate(
    left: &Program,
    right: &Program,
    config: &EquivalenceConfig,
) -> Option<TraceNorm> {
    // The miter uses positional wires. Require exactly that full interface;
    // do not silently replace a different pairing or classical observation.
    let l = super::qubits(left);
    let r = super::qubits(right);
    if l.len() != r.len()
        || !config.numeric_input_pairs.is_empty()
        || config.input_pairs
            != l.iter()
                .cloned()
                .zip(r.iter().cloned())
                .map(|(l, r)| InputPair::quantum(l, r))
                .collect::<Vec<_>>()
        || config.output_pairs
            != l.into_iter()
                .zip(r)
                .map(|(l, r)| OutputPair {
                    left: Endpoint::Quantum(l),
                    right: Endpoint::Quantum(r),
                })
                .collect::<Vec<_>>()
    {
        return None;
    }
    // Prefer the shorter inverse network: its propagated Boolean expressions
    // otherwise enlarge every surviving forward phase selector. Both choices
    // are ordinary sequential miters; no noncommuting gates are interleaved.
    let (forward, inverse) = if left.operation_count() >= right.operation_count() {
        (left, right)
    } else {
        (right, left)
    };
    let Ok((circuit, _)) = unitary::miter(forward, inverse) else {
        return None;
    };
    let was_mixing = circuit.body.statements.iter().any(|s| {
        matches!(
            s.kind,
            StatementKind::Apply {
                gate: Gate::H | Gate::Rx | Gate::Ry | Gate::Crx | Gate::Cry,
                ..
            }
        )
    });
    // Validate the original miter before any rule could erase a bad numeric
    // domain (e.g. a pair of rotations with a zero denominator).
    crate::symbolic::numeric_domains(&circuit).ok()?;
    let circuit = super::unitary_rewrite::preprocess(&circuit).unwrap_or(circuit);
    if circuit.body.statements.is_empty()
        && super::unitary_rewrite::strategy().ok()? != super::unitary_rewrite::Strategy::Off
    {
        return Some(TraceNorm::Rational(BigRational::from_integer(1.into())));
    }
    // H plus monomial gates avoids path-dependent trigonometric scalars.
    // Purely monomial programs are outside this optional fast path.
    let mut has_h = false;
    for s in &circuit.body.statements {
        match &s.kind {
            StatementKind::Apply {
                gate: Gate::Rx | Gate::Ry | Gate::Crx | Gate::Cry,
                ..
            } => return None,
            StatementKind::Apply { gate: Gate::H, .. } => has_h = true,
            StatementKind::Apply { .. } => {}
            _ => return None,
        }
    }
    if !has_h && !was_mixing {
        return None;
    }
    let outputs = OutputSelection::new(super::qubits(&circuit), []);
    let trace_started = std::time::Instant::now();
    let Ok(mut hps) = execute(&circuit, &ExecutionConfig::all_symbolic(), &outputs) else {
        return None;
    };
    if std::env::var_os("IRENE_DEBUG_COMPACTION").is_some() {
        eprintln!(
            "unitary trace execution seconds={:.6}",
            trace_started.elapsed().as_secs_f64()
        );
    }
    if hps.components.len() != 1 {
        return None;
    }
    let c = normalized_trace_component(hps.components.pop().unwrap(), &hps.input)?;
    // Keep the closed rational fast path, including arbitrary constant real
    // rational phases whose modulus cancels exactly.
    let norm = if c.path_support.is_empty()
        && c.guard.is_empty()
        && c.phase.variables().is_empty()
        && c.phase.selectors().all(|(_, a)| a.as_rational().is_some())
        && let Scalar::Rational(norm) = c.scalar.clone().multiply(c.scalar.clone())
    {
        norm
    } else {
        // Residual sums require a separate exact backend, not a guessed norm.
        return None;
    };
    // This is a consistency check, not a numerical tolerance or a bound used
    // as a proof. Only the exactly computed rational is returned.
    (norm >= BigRational::from_integer(0.into()) && norm <= BigRational::from_integer(1.into()))
        .then_some(TraceNorm::Rational(norm))
}

#[cfg(test)]
mod tests;
