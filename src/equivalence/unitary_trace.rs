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
    if circuit.body.statements.is_empty() {
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
/// Decide admission per rotation, not per circuit. Unsupported rotations and
/// other gates stay unchanged; the caller checks the remaining backend domain.
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
    let mut next_id = 0;
    circuit.visit_ast_ids(|id| next_id = next_id.max(id.index() + 1));
    let mut ids = AstIdGenerator::starting_at(next_id);
    let mut out = Vec::new();
    for statement in std::mem::take(&mut circuit.body.statements) {
        let StatementKind::Apply {
            gate,
            qubits,
            parameters,
        } = &statement.kind
        else {
            return None;
        };
        // Keep the same bounded dyadic expansion policy, but only inspect this
        // gate. A decimal angle elsewhere must not veto an exact local change.
        let supported = matches!(gate, Gate::Rx | Gate::Ry | Gate::Crx | Gate::Cry)
            && parameters.iter().all(|parameter| {
                PhaseCoefficient::angle(parameter.clone(), BigRational::from_integer(1.into()))
                    .as_rational()
                    .and_then(|turns| u64::try_from(turns.denom()).ok())
                    .is_some_and(|d| d.is_power_of_two() && d <= 4096)
            });
        if !supported {
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
mod tests {
    use super::*;
    use crate::frontend::openqasm3;
    fn proves(left: &Program, right: &Program, config: &EquivalenceConfig) -> bool {
        certificate(left, right, config).is_some_and(|n| n.is_one())
    }
    fn parse(gates: &str) -> Program {
        openqasm3::parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; {gates}"),
            "trace-test",
        )
        .unwrap()
    }
    fn config(left: &Program, right: &Program) -> EquivalenceConfig {
        let l = super::super::qubits(left);
        let r = super::super::qubits(right);
        EquivalenceConfig {
            input_pairs: l
                .iter()
                .cloned()
                .zip(r.iter().cloned())
                .map(|(l, r)| InputPair::quantum(l, r))
                .collect(),
            output_pairs: l
                .into_iter()
                .zip(r)
                .map(|(l, r)| OutputPair {
                    left: Endpoint::Quantum(l),
                    right: Endpoint::Quantum(r),
                })
                .collect(),
            numeric_input_pairs: vec![],
        }
    }
    #[test]
    fn exact_trace_preserves_vacuous_inputs_and_constant_global_phases() {
        for (a, b) in [
            ("h q[0];", "h q[0];"),
            ("h q[0]; x q[0]; z q[0]; x q[0]; z q[0];", "h q[0];"),
            ("h q[0]; x q[0]; y q[0]; z q[0];", "h q[0];"),
            (
                "h q[0]; cx q[0],q[1]; t q[1];",
                "h q[0]; cx q[0],q[1]; t q[1];",
            ),
        ] {
            let (a, b) = (parse(a), parse(b));
            assert!(proves(&a, &b, &config(&a, &b)));
            assert!(proves(&b, &a, &config(&b, &a)));
        }
    }
    #[test]
    fn trace_rejects_input_dependent_phase_and_noncommuting_order() {
        for (a, b) in [
            ("h q[0]; x q[0];", "h q[0];"),
            ("h q[0]; z q[0];", "h q[0];"),
            ("h q[0]; t q[0];", "h q[0];"),
            ("h q[0]; cx q[0],q[1];", "cx q[0],q[1]; h q[0];"),
        ] {
            let (a, b) = (parse(a), parse(b));
            assert!(!proves(&a, &b, &config(&a, &b)));
        }
    }
    #[test]
    fn trace_refuses_incomplete_duplicate_permuted_and_classical_interfaces() {
        let a = parse("h q[0]; bit c=0;");
        let full = config(&a, &a);
        assert!(proves(&a, &a, &full));
        let mut c = full.clone();
        c.input_pairs.pop();
        assert!(!proves(&a, &a, &c));
        let mut c = full.clone();
        c.output_pairs.pop();
        assert!(!proves(&a, &a, &c));
        let mut c = full.clone();
        c.output_pairs[0].right = c.output_pairs[1].right.clone();
        assert!(!proves(&a, &a, &c));
        let mut c = full.clone();
        c.output_pairs.swap(0, 1);
        assert!(!proves(&a, &a, &c));
        let c = EquivalenceConfig::positional(&a, &a).unwrap();
        assert!(!proves(&a, &a, &c));
    }
    #[test]
    fn unsupported_or_unequal_circuits_are_not_proved_equivalent() {
        let a = parse("h q[0];");
        for body in [
            "h q[0]; reset q[0];",
            "h q[0]; bit c; c=measure q[0];",
            "h q[0]; bit c=0; if(c) x q[0];",
            "h q[0]; rx(0.1) q[0];",
            "h q[0]; rx(pi/3) q[0];",
            "h q[0]; rx(pi/2) q[0]; rz(0.1) q[0];",
        ] {
            let b = parse(body);
            assert!(!proves(&a, &b, &config(&a, &b)));
            assert!(!proves(&b, &a, &config(&b, &a)));
        }
    }

    #[test]
    fn phase_lowering_is_local_and_preserves_unsupported_angles() {
        let source = parse(
            "rz(0.5709439576515822) q[0]; rx(pi/2) q[0]; ry(pi/4) q[1]; rx(1.5707963267948966) q[0]; ry(pi/3) q[1]; crx(pi/8192) q[0],q[1];",
        );
        let lowered = phase_only_rotations(source).unwrap();
        let expected = parse(
            "rz(0.5709439576515822) q[0]; h q[0]; rz(pi/2) q[0]; h q[0]; sdg q[1]; h q[1]; rz(pi/4) q[1]; h q[1]; s q[1]; rx(1.5707963267948966) q[0]; ry(pi/3) q[1]; crx(pi/8192) q[0],q[1];",
        );
        assert_eq!(lowered, expected);
        let mut ids = std::collections::BTreeSet::new();
        lowered.visit_ast_ids(|id| assert!(ids.insert(id)));
        // Local success does not imply that trace can handle the residual Rx.
        let identity = parse("");
        assert_eq!(
            certificate(&lowered, &identity, &config(&lowered, &identity)),
            None
        );
    }

    #[test]
    fn mixed_angle_trace_succeeds_when_residual_phases_cancel_exactly() {
        // The decimal Rz gates are separated in the miter, so adjacent
        // preprocessing cannot remove them before local Rx lowering.
        let a = parse("rx(pi/2) q[0]; rz(0.5709439576515822) q[1];");
        let b = parse("rz(0.5709439576515822) q[1]; h q[0]; rz(pi/2) q[0]; h q[0];");
        assert!(proves(&a, &b, &config(&a, &b)));
        assert!(proves(&b, &a, &config(&b, &a)));
    }

    #[test]
    fn mixed_angles_keep_local_reductions_on_the_general_channel_route() {
        let a =
            parse("rx(0.123) q[0]; h q[0]; rx(pi/2) q[0]; h q[0]; rz(0.5709439576515822) q[0];");
        let b = parse("rx(0.123) q[0]; rz(pi/2) q[0]; rz(0.5709439576515822) q[0];");
        let mut c = config(&a, &b);
        // Observe only one wire: force fallback instead of a unitary trace proof.
        c.input_pairs.pop();
        c.output_pairs.pop();
        assert_eq!(certificate(&a, &b, &c), None);
        assert_eq!(
            super::super::analyze(&a, &b, &c).unwrap().verdict,
            super::super::Verdict::Equivalent
        );
    }

    #[test]
    fn trace_basis_conjugation_preserves_controlled_phase_and_ast_identity() {
        for (gate, decomposition, operands) in [
            ("rx", "h q[1]; rz(ANGLE) q[1]; h q[1];", "q[1]"),
            (
                "ry",
                "sdg q[1]; h q[1]; rz(ANGLE) q[1]; h q[1]; s q[1];",
                "q[1]",
            ),
            ("crx", "h q[1]; crz(ANGLE) q[0],q[1]; h q[1];", "q[0],q[1]"),
            (
                "cry",
                "sdg q[1]; h q[1]; crz(ANGLE) q[0],q[1]; h q[1]; s q[1];",
                "q[0],q[1]",
            ),
        ] {
            for angle in ["pi/4", "-pi/2", "2*pi"] {
                let a = parse(&format!("{gate}({angle}) {operands};"));
                let b = parse(&decomposition.replace("ANGLE", angle));
                assert!(proves(&a, &b, &config(&a, &b)), "{gate} {angle}");
                let (m, _) = unitary::miter(&a, &b).unwrap();
                let lowered = phase_only_rotations(m).unwrap();
                let mut seen = std::collections::BTreeSet::new();
                lowered.visit_ast_ids(|id| assert!(seen.insert(id)));
            }
        }
        let identity = parse("");
        for gate in ["crx", "cry"] {
            let a = parse(&format!("{gate}(2*pi) q[0],q[1];"));
            assert_eq!(
                certificate(&a, &identity, &config(&a, &identity)),
                Some(TraceNorm::Rational(BigRational::from_integer(0.into())))
            );
        }
    }
    #[test]
    fn exact_zero_trace_certifies_inequality_but_refusal_does_not() {
        let a = parse("h q[0];");
        for body in ["h q[0]; x q[0];", "h q[0]; z q[0];"] {
            let b = parse(body);
            assert_eq!(
                certificate(&a, &b, &config(&a, &b)),
                Some(TraceNorm::Rational(BigRational::from_integer(0.into())))
            );
        }
        let b = parse("h q[0]; t q[0];");
        // (2+sqrt(2))/4 is irrational but exactly unequal to one in the
        // cyclotomic power basis. It is not rounded to a rational witness.
        assert!(matches!(
            certificate(&a, &b, &config(&a, &b)),
            Some(TraceNorm::Cyclotomic(_))
        ));
    }

    #[test]
    fn rotation_lowering_agrees_with_the_independent_general_channel_executor() {
        for gate in ["rx", "ry", "crx", "cry"] {
            for angle in ["pi/4", "-pi/2", "2*pi"] {
                let operands = if gate.starts_with('c') {
                    "q[0],q[1]"
                } else {
                    "q[1]"
                };
                let a = openqasm3::parse_str(
                    &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {gate}({angle}) {operands};"),
                    "rotation-channel-test",
                ).unwrap();
                let mut identity = a.clone();
                identity.body.statements.clear();
                let (m, _) = unitary::miter(&a, &identity).unwrap();
                let b = phase_only_rotations(m).unwrap();
                let mut c = config(&a, &b);
                // Unused initialized spectator: same visible two-qubit channel,
                // but the full-unitary certificate must refuse this interface.
                c.input_pairs.pop();
                c.output_pairs.pop();
                assert_eq!(certificate(&a, &b, &c), None);
                let result = super::super::analyze(&a, &b, &c).unwrap();
                assert_eq!(
                    result.verdict,
                    super::super::Verdict::Equivalent,
                    "{gate} {angle}: {:?}",
                    result.evidence
                );
            }
        }
    }
}
