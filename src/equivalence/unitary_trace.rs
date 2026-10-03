//! Full-unitary trace certificate, before independent density construction.
use super::{Endpoint, EquivalenceConfig, InputPair, OutputPair};
use crate::{
    ir::{AstIdGenerator, Gate, Program, StatementKind, unitary},
    symbolic::{
        ExecutionConfig, OutputSelection, PhaseCoefficient, Scalar, execute,
        normalized_trace_component,
    },
};
use num_rational::BigRational;

#[derive(Debug, PartialEq, Eq)]
pub(super) enum TraceNorm {
    Rational(BigRational),
    Cyclotomic(Vec<(u64, BigRational)>),
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
    let circuit = phase_only_rotations(circuit)?;
    let circuit = super::unitary_rewrite::preprocess(&circuit).unwrap_or(circuit);
    if circuit.body.statements.is_empty()
        && super::unitary_rewrite::strategy().ok()? != super::unitary_rewrite::Strategy::Off
    {
        return Some(TraceNorm::Rational(BigRational::from_integer(1.into())));
    }
    // H plus monomial gates avoids path-dependent trigonometric scalars.
    // Purely monomial programs already have the cheap deterministic route.
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
        let terms = if super::aggregate::prefer_frontier_trace(&circuit, c.path_support.len()) {
            super::aggregate::frontier_trace_norm(&circuit)
                .or_else(|| super::aggregate::closed_trace_norm(&c))
        } else {
            super::aggregate::closed_trace_norm(&c)
                .or_else(|| super::aggregate::frontier_trace_norm(&circuit))
        }?;
        match terms.as_slice() {
            [] => BigRational::from_integer(0.into()),
            [(0, r)] => r.clone(),
            _ => return Some(TraceNorm::Cyclotomic(terms)),
        }
    };
    // This is a consistency check, not a numerical tolerance or a bound used
    // as a proof. Only the exactly computed rational is returned.
    (norm >= BigRational::from_integer(0.into()) && norm <= BigRational::from_integer(1.into()))
        .then_some(TraceNorm::Rational(norm))
}

/// Exact basis conjugations after full-unitary validation. Parameters are
/// transferred unchanged, including the controlled rotation's relative phase.
/// Admission is restricted to the existing reducer's bounded dyadic domain;
/// unsupported numeric atoms remain on the original general-channel route.
fn phase_only_rotations(mut circuit: Program) -> Option<Program> {
    let needs_lowering = circuit.body.statements.iter().any(|s| {
        matches!(
            s.kind,
            StatementKind::Apply {
                gate: Gate::Rx | Gate::Ry | Gate::Crx | Gate::Cry,
                ..
            }
        )
    });
    if !needs_lowering {
        return Some(circuit);
    }
    // This extension is for dyadic phase circuits as a whole, not just one
    // dyadic rotation embedded in unsupported transcendental phase atoms.
    // The pre-existing H/monomial admission above is unchanged.
    for statement in &circuit.body.statements {
        let StatementKind::Apply { parameters, .. } = &statement.kind else {
            return None;
        };
        for parameter in parameters {
            let turns =
                PhaseCoefficient::angle(parameter.clone(), BigRational::from_integer(1.into()))
                    .as_rational()?;
            let denominator = u64::try_from(turns.denom()).ok()?;
            // Same 12-bit optional local phase domain as joint_phase.
            if !denominator.is_power_of_two() || denominator > 4096 {
                return None;
            }
        }
    }
    let mut next_id = 0;
    circuit.visit_ast_ids(|id| next_id = next_id.max(id.index() + 1));
    let mut ids = AstIdGenerator::starting_at(next_id);
    let mut out = Vec::new();
    for statement in std::mem::take(&mut circuit.body.statements) {
        let StatementKind::Apply { gate, qubits, .. } = &statement.kind else {
            return None;
        };
        if !matches!(gate, Gate::Rx | Gate::Ry | Gate::Crx | Gate::Cry) {
            out.push(statement);
            continue;
        }
        let is_y = matches!(gate, Gate::Ry | Gate::Cry);
        let diagonal = if matches!(gate, Gate::Crx | Gate::Cry) {
            Gate::Crz
        } else {
            Gate::Rz
        };
        let target = qubits.last()?.clone();
        let one = |gate, ids: &mut AstIdGenerator| {
            ids.node(StatementKind::Apply {
                gate,
                parameters: Vec::new(),
                qubits: vec![target.clone()],
            })
        };
        // Rx = H Rz H; Ry = S H Rz H S† as operators (textual
        // execution order below is reversed). On control=0 the basis changes
        // cancel, so the same construction implements Crx/Cry exactly.
        if is_y {
            out.push(one(Gate::Sdg, &mut ids));
        }
        out.push(one(Gate::H, &mut ids));
        let StatementKind::Apply {
            parameters, qubits, ..
        } = statement.kind
        else {
            unreachable!()
        };
        out.push(ids.node(StatementKind::Apply {
            gate: diagonal,
            parameters,
            qubits,
        }));
        out.push(one(Gate::H, &mut ids));
        if is_y {
            out.push(one(Gate::S, &mut ids));
        }
    }
    circuit.body.statements = out;
    Some(circuit)
}

#[cfg(test)]
mod tests;
