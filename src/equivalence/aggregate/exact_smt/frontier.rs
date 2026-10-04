//! Complete small physical-wire operator contraction. Gate amplitudes come
//! from the ordinary HPS executor; all columns and all coherent paths survive
//! until the complete normalized trace is formed. No gate-matrix library or
//! probabilistic/candidate proof is introduced here.
use super::*;
use crate::ir::{Gate, Program, Statement, StatementKind};
use crate::symbolic::{BooleanPolynomial, ExecutionConfig, OutputSelection, Variable, execute};

const MAX_CELLS: usize = 4096;
const MAX_TABLE_STEPS: usize = 1_000_000;

fn table_cost(circuit: &Program) -> Option<(usize, usize, usize)> {
    let width = crate::equivalence::qubits(circuit).len();
    let dimension = 1usize.checked_shl(u32::try_from(width).ok()?)?;
    let cells = dimension.checked_mul(dimension)?;
    let steps = cells.checked_mul(circuit.body.statements.len())?;
    (cells <= MAX_CELLS && steps <= MAX_TABLE_STEPS).then_some((dimension, cells, steps))
}

pub(super) fn preferred(circuit: &Program, paths: usize) -> bool {
    table_cost(circuit)
        .and_then(|(_, cells, _)| cells.checked_mul(blocks(circuit)?.len()))
        .is_some_and(|steps| {
            // Compare complete dense table traversal to complete bound assignment
            // enumeration. Propagation visits the table once per actual block,
            // not once per source gate. Keep the gate-count admission cap above
            // unchanged; both exact routes still fall back on bounded refusal.
            u32::try_from(paths)
                .ok()
                .and_then(|p| 1usize.checked_shl(p))
                .is_none_or(|assignments| assignments > steps)
        })
}

pub(super) fn norm(circuit: &Program) -> Option<Vec<(u64, BigRational)>> {
    let start = std::time::Instant::now();
    let kernel = DensityKernel {
        input_pairs: vec![],
        quantum_output_count: 0,
        classical_output_count: 0,
        terms: vec![],
    };
    let mut encoder = Encoder::new(&kernel)?;
    // This optional route remains bounded even during solver diagnostic runs.
    encoder.unlimited_work = false;
    encoder.work = MAX_WORK;
    let result = matrix(circuit, &mut encoder).and_then(|(dimension, values)| {
        let mut trace = Vec::new();
        for i in 0..dimension {
            trace.extend(values[i * dimension + i].clone());
        }
        let trace = encoder.compact(trace)?;
        let scale = encoder.literal(BigRational::new(1.into(), dimension.into()), 0, false)?;
        let trace = encoder.multiply(trace, scale)?;
        encoder.closed_value_norm(trace)
    });
    if std::env::var_os("IRENE_DEBUG_COMPACTION").is_some() {
        eprintln!(
            "unitary frontier seconds={:.6} work={} success={}",
            start.elapsed().as_secs_f64(),
            MAX_WORK.saturating_sub(encoder.work),
            result.is_some()
        );
    }
    result
}

fn blocks(circuit: &Program) -> Option<Vec<&[Statement]>> {
    // Summarize ordinary contiguous execution, up to one branching H per
    // block. Monomial gate runs then update the matrix once instead of once
    // per gate. No gates are reordered or recognized as a special circuit.
    let mut blocks = Vec::new();
    let mut start = 0;
    let mut has_h = false;
    for (i, statement) in circuit.body.statements.iter().enumerate() {
        let StatementKind::Apply { gate, .. } = statement.kind else {
            return None;
        };
        if !matches!(
            gate,
            Gate::H
                | Gate::X
                | Gate::Y
                | Gate::Z
                | Gate::S
                | Gate::Sdg
                | Gate::T
                | Gate::Tdg
                | Gate::Cx
                | Gate::Cy
                | Gate::Cz
                | Gate::Swap
                | Gate::Ccx
                | Gate::Ccz
                | Gate::P
                | Gate::Cp
                | Gate::Rz
                | Gate::Crz
        ) {
            return None;
        }
        if i - start >= 64 || (has_h && gate == Gate::H) {
            blocks.push(&circuit.body.statements[start..i]);
            start = i;
            has_h = false;
        }
        has_h |= gate == Gate::H;
    }
    if start < circuit.body.statements.len() {
        blocks.push(&circuit.body.statements[start..]);
    }
    Some(blocks)
}

fn matrix(circuit: &Program, encoder: &mut Encoder) -> Option<(usize, Vec<Polynomial>)> {
    let started = std::time::Instant::now();
    let mut lowering_seconds = 0.0;
    let mut peak_atoms = 0;
    let wires = crate::equivalence::qubits(circuit);
    let (dimension, cells, _) = table_cost(circuit)?;
    let mut values = vec![Vec::new(); cells];
    let mut common = encoder.literal(integer(1), 0, false)?;
    for i in 0..dimension {
        values[i * dimension + i] = encoder.literal(integer(1), 0, false)?;
    }
    let blocks = blocks(circuit)?;
    for (index, block) in blocks.iter().enumerate() {
        let qubits: BTreeSet<_> = block
            .iter()
            .flat_map(|s| match &s.kind {
                StatementKind::Apply { qubits, .. } => qubits.clone(),
                _ => vec![],
            })
            .collect();
        let qubits: Vec<_> = qubits.into_iter().collect();
        let positions: Vec<_> = qubits
            .iter()
            .map(|q| wires.iter().position(|w| w == q))
            .collect::<Option<_>>()?;
        if positions.iter().collect::<BTreeSet<_>>().len() != positions.len() {
            return None;
        }
        let local_started = std::time::Instant::now();
        let (transitions, factor) = local_block(circuit, block, &qubits, encoder)?;
        lowering_seconds += local_started.elapsed().as_secs_f64();
        common = encoder.multiply(common, factor)?;
        let mask = positions.iter().fold(0usize, |m, p| m | (1usize << p));
        let mut next = vec![Vec::new(); cells];
        // A complete operator often repeats coefficients across columns (in
        // particular through spectators). Reuse exact algebraic values, never
        // confuse distinct columns or infer equality from numerical samples.
        // Caches are gate-local and bounded by the already capped table size.
        let mut products = BTreeMap::new();
        for row in 0..dimension {
            let local_input = positions
                .iter()
                .enumerate()
                .fold(0, |x, (i, p)| x | (((row >> p) & 1) << i));
            for (local_output, coefficient) in &transitions[local_input] {
                let output = positions.iter().enumerate().fold(row & !mask, |x, (i, p)| {
                    x | (((local_output >> i) & 1) << p)
                });
                for column in 0..dimension {
                    encoder.charge(1)?;
                    let value = &values[row * dimension + column];
                    if value.is_empty() {
                        continue;
                    }
                    let key = (coefficient.clone(), value.clone());
                    if !products.contains_key(&key) {
                        products
                            .insert(key.clone(), encoder.multiply(key.0.clone(), key.1.clone())?);
                    }
                    let target = &mut next[output * dimension + column];
                    *target = encoder.add_closed(std::mem::take(target), products[&key].clone())?;
                }
            }
        }
        values = next;
        peak_atoms = peak_atoms.max(values.iter().map(Vec::len).sum::<usize>());
        if std::env::var_os("IRENE_DEBUG_COMPACTION").is_some() && index % 25 == 0 {
            eprintln!(
                "unitary frontier block={index}/{} gates={} cells={cells} products={} atoms={} work={}",
                blocks.len(),
                circuit.body.statements.len(),
                products.len(),
                values.iter().map(Vec::len).sum::<usize>(),
                MAX_WORK.saturating_sub(encoder.work)
            );
        }
    }
    // Keep identical block-wide normalization outside all matrix cells until
    // composition finishes. This is scalar factoring, not a path norm.
    for value in &mut values {
        *value = encoder.multiply(std::mem::take(value), common.clone())?;
    }
    if std::env::var_os("IRENE_DEBUG_COMPACTION").is_some() {
        eprintln!(
            "unitary frontier complete cells={cells} blocks={} peak_matrix_atoms={peak_atoms} lowering_seconds={lowering_seconds:.6} matrix_seconds={:.6} smt_text_bytes={}",
            blocks.len(),
            started.elapsed().as_secs_f64() - lowering_seconds,
            encoder.definitions.len()
        );
    }
    Some((dimension, values))
}

fn local_block(
    circuit: &Program,
    statements: &[Statement],
    qubits: &[crate::ir::Qubit],
    encoder: &mut Encoder,
) -> Option<(Vec<Vec<(usize, Polynomial)>>, Polynomial)> {
    if qubits.is_empty() || qubits.len() > 6 {
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
    let mut hps = execute(
        &local,
        &ExecutionConfig::all_symbolic(),
        &OutputSelection::new(operands.clone(), []),
    )
    .ok()?;
    let mut factor = encoder.literal(integer(1), 0, false)?;
    if let Some(first) = hps.components.first()
        && hps.components.iter().all(|c| c.scalar == first.scalar)
    {
        let mut scalar = first.clone();
        scalar.output.quantum.clear();
        scalar.guard.clear();
        scalar.phase = Default::default();
        scalar.path_support.clear();
        // Only a closed coefficient can be factored across every path/input.
        if let Some((paths, constraints, coefficient, phase)) =
            crate::equivalence::kernel::closed_scalar_parts(&scalar)
        {
            factor = encoder.term(&WorkingTerm {
                paths,
                constraints,
                coefficient,
                phase,
            })?;
            for c in &mut hps.components {
                c.scalar = crate::symbolic::Scalar::one();
            }
        }
    }
    let dimension = 1usize << operands.len();
    let mut result = vec![Vec::new(); dimension];
    for (input, transitions) in result.iter_mut().enumerate() {
        let mut row = vec![Vec::new(); dimension];
        for component in &hps.components {
            if !component.output.classical.is_empty()
                || !component.output.history.is_empty()
                || component.output.quantum.len() != operands.len()
                || component.path_support.len() > 8
            {
                return None;
            }
            for paths in 0..(1usize << component.path_support.len()) {
                encoder.charge(1)?;
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
                // Any unknown dependency, including in scalar conditions,
                // refuses lowering rather than receiving a default value.
                let (paths, constraints, coefficient, phase) =
                    crate::equivalence::kernel::closed_scalar_parts(&closed)?;
                row[output].extend(encoder.term(&WorkingTerm {
                    paths,
                    constraints,
                    coefficient,
                    phase,
                })?);
            }
        }
        for (output, value) in row.into_iter().enumerate() {
            let value = encoder.compact(value)?;
            if !value.is_empty() {
                transitions.push((output, value));
            }
        }
    }
    Some((result, factor))
}

#[cfg(test)]
mod tests;
