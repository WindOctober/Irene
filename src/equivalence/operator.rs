//! Shared exact gate/block semantics for physical-wire contraction.
//! Backends interpret closed amplitudes; input/path enumeration stays common.
use crate::ir::{Gate, Program, Qubit, Statement, StatementKind};
use crate::symbolic::{
    BooleanPolynomial, Component, ExecutionConfig, HybridPathSum, OutputSelection, Variable,
    execute,
};
use std::collections::BTreeMap;

pub(super) fn local_hps(
    circuit: &Program,
    statements: &[Statement],
    qubits: &[Qubit],
) -> Option<(HybridPathSum, Vec<Qubit>)> {
    if qubits.is_empty() || qubits.len() > 10 {
        return None;
    }
    // Isolate only gate operands. Spectators remain in the global matrix, not
    // initialized or discarded by this local executor call.
    let mut local = circuit.clone();
    let mut register = local.quantum_registers.first()?.clone();
    register.width = qubits.len();
    let operands: Vec<_> = (0..qubits.len())
        .map(|index| crate::ir::Qubit {
            register: register.id,
            index,
        })
        .collect();
    local.quantum_registers = vec![register];
    local.classical_registers.clear();
    local.body.classical_registers.clear();
    local.body.statements = statements.to_vec();
    for statement in &mut local.body.statements {
        let StatementKind::Apply {
            qubits: targets, ..
        } = &mut statement.kind
        else {
            return None;
        };
        for q in targets {
            *q = operands[qubits.iter().position(|original| original == q)?].clone();
        }
    }
    let hps = execute(
        &local,
        &ExecutionConfig::all_symbolic(),
        &OutputSelection::new(operands.clone(), []),
    )
    .ok()?;
    Some((hps, operands))
}

/// Contiguous unitary blocks with at most one path-creating gate. Combining
/// monomial runs changes neither gate order nor the coefficient domain.
pub(super) fn blocks(circuit: &Program) -> Option<Vec<&[Statement]>> {
    let mut blocks = Vec::new();
    let (mut start, mut mixing) = (0, false);
    for (i, s) in circuit.body.statements.iter().enumerate() {
        let StatementKind::Apply { gate, .. } = s.kind else {
            return None;
        };
        let next = matches!(gate, Gate::H | Gate::Rx | Gate::Ry | Gate::Crx | Gate::Cry);
        if i - start >= 64 || (mixing && next) {
            blocks.push(&circuit.body.statements[start..i]);
            start = i;
            mixing = false;
        }
        mixing |= next;
    }
    if start < circuit.body.statements.len() {
        blocks.push(&circuit.body.statements[start..]);
    }
    Some(blocks)
}

/// Visit every coherent contribution. A callback may refuse its coefficient domain.
pub(super) fn visit_amplitudes(
    hps: &HybridPathSum,
    operands: &[Qubit],
    mut visit: impl FnMut(usize, usize, &Component) -> Option<()>,
) -> Option<()> {
    for input in 0..(1usize << operands.len()) {
        for component in &hps.components {
            if !component.output.classical.is_empty()
                || !component.output.history.is_empty()
                || component.output.quantum.len() != operands.len()
                || component.path_support.len() > 8
            {
                return None;
            }
            for paths in 0..(1usize << component.path_support.len()) {
                let bindings: BTreeMap<_, _> = operands
                    .iter()
                    .enumerate()
                    .map(|(i, q)| (Variable::Input(q.clone()), input & (1 << i) != 0))
                    .chain(
                        component
                            .path_support
                            .iter()
                            .enumerate()
                            .map(|(i, p)| (Variable::Path(*p), paths & (1 << i) != 0)),
                    )
                    .collect();
                let evaluate =
                    |p: &BooleanPolynomial| p.evaluate(|v| bindings.get(v).copied().ok_or(())).ok();
                let guards: Vec<_> = component
                    .guard
                    .iter()
                    .map(evaluate)
                    .collect::<Option<_>>()?;
                if guards.into_iter().any(|g| g) {
                    continue;
                }
                let mut output = 0;
                for (i, q) in operands.iter().enumerate() {
                    if evaluate(component.output.quantum.get(q)?)? {
                        output |= 1 << i;
                    }
                }
                let mut closed = component.clone();
                closed.output.quantum.clear();
                closed.guard.clear();
                closed.path_support.clear();
                let replacement = |v: &Variable| {
                    bindings
                        .get(v)
                        .map(|b| {
                            if *b {
                                BooleanPolynomial::one()
                            } else {
                                BooleanPolynomial::zero()
                            }
                        })
                        .unwrap_or_else(|| BooleanPolynomial::variable(v.clone()))
                };
                closed.phase.map_variables(replacement);
                for v in bindings.keys() {
                    closed.scalar = closed.scalar.substitute(v, &replacement(v));
                }
                visit(input, output, &closed)?;
            }
        }
    }
    Some(())
}
