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
mod tests {
    use super::*;
    fn parse(width: usize, gates: &str) -> Program {
        crate::frontend::openqasm3::parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[{width}] q; {gates}"),
            "frontier-test",
        )
        .unwrap()
    }
    fn encoder() -> Encoder {
        Encoder::new(&DensityKernel {
            input_pairs: vec![],
            quantum_output_count: 0,
            classical_output_count: 0,
            terms: vec![],
        })
        .unwrap()
    }
    fn coefficients(p: &Polynomial) -> [BigRational; 4] {
        let mut out = std::array::from_fn(|_| integer(0));
        for atom in p {
            assert_eq!(atom.guard, "true");
            assert!(!atom.radical);
            let Power::Constant(p) = atom.power else {
                panic!("unclosed power");
            };
            assert_eq!(p % (ORDER / 8), 0);
            out[(p / (ORDER / 8)) as usize] += &atom.weight;
        }
        out
    }

    #[test]
    fn complete_frontier_matches_independent_integer_eighth_root_matrices() {
        // Independent test-only integer arithmetic: a shared denominator2^h,
        // zeta^4=-1, H=(zeta-zeta^3)/2 times the signed Hadamard matrix.
        // Every basis column is computed, including the untouched spectator.
        for seed in 0..12 {
            let mut exact = vec![[0i64; 4]; 64];
            for i in 0..8 {
                exact[i * 8 + i][0] = 1;
            }
            let mut denominator = 1i64;
            let mut gates = String::new();
            let mut state = seed + 19u64;
            let shift = |a: [i64; 4], exponent: usize| {
                let mut b = [0; 4];
                for (i, c) in a.into_iter().enumerate() {
                    b[(i + exponent) % 4] += if (i + exponent) % 8 >= 4 { -c } else { c };
                }
                b
            };
            for _ in 0..18 {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
                let gate = (state >> 32) % 7;
                gates.push_str(match gate {
                    0 => "h q[0];",
                    1 => "t q[0];",
                    2 => "tdg q[1];",
                    3 => "x q[1];",
                    4 => "y q[0];",
                    5 => "cx q[0],q[1];",
                    _ => "swap q[0],q[1];",
                });
                let mut next = vec![[0i64; 4]; 64];
                for row in 0..8 {
                    for col in 0..8 {
                        let value = exact[row * 8 + col];
                        let mut add = |out: usize, v: [i64; 4]| {
                            for i in 0..4 {
                                next[out * 8 + col][i] += v[i];
                            }
                        };
                        match gate {
                            0 => {
                                let a = shift(value, 1);
                                let b = shift(value, 3);
                                let v = std::array::from_fn(|i| a[i] - b[i]);
                                add(row & !1, v);
                                add(row | 1, if row & 1 == 0 { v } else { v.map(|c| -c) });
                            }
                            1 => add(row, shift(value, if row & 1 != 0 { 1 } else { 0 })),
                            2 => add(row, shift(value, if row & 2 != 0 { 7 } else { 0 })),
                            3 => add(row ^ 2, value),
                            4 => add(row ^ 1, shift(value, if row & 1 == 0 { 2 } else { 6 })),
                            5 => add(row ^ if row & 1 != 0 { 2 } else { 0 }, value),
                            _ => add((row & !3) | ((row & 1) << 1) | ((row & 2) >> 1), value),
                        }
                    }
                }
                if gate == 0 {
                    denominator *= 2;
                }
                exact = next;
            }
            let (d, actual) = matrix(&parse(3, &gates), &mut encoder()).unwrap();
            assert_eq!(d, 8);
            for (i, entry) in actual.iter().enumerate() {
                assert_eq!(
                    coefficients(entry),
                    exact[i].map(|n| BigRational::new(n.into(), denominator.into())),
                    "seed={seed} entry={i} gates={gates}"
                );
            }
        }
    }

    #[test]
    fn frontier_norm_retains_global_relative_phase_and_coherent_cancellation() {
        for gates in [
            "h q[0]; h q[0];",
            "h q[0]; z q[0]; h q[0]; x q[0];",
            "x q[0]; y q[0]; z q[0];",
            "h q[0]; t q[0]; tdg q[0]; h q[0];",
        ] {
            assert_eq!(
                norm(&parse(2, gates)),
                Some(vec![(0, integer(1))]),
                "{gates}"
            );
        }
        for gates in ["z q[1];", "h q[0]; z q[0]; h q[0];", "crz(2*pi) q[0],q[1];"] {
            assert_eq!(norm(&parse(2, gates)), Some(vec![]), "{gates}");
        }
        assert_eq!(
            norm(&parse(2, "t q[1];")),
            Some(vec![
                (0, ratio(1, 2)),
                (ORDER / 8, ratio(1, 4)),
                (3 * ORDER / 8, ratio(-1, 4))
            ])
        );
        let a = matrix(&parse(2, "h q[0]; cx q[0],q[1];"), &mut encoder())
            .unwrap()
            .1;
        let b = matrix(&parse(2, "cx q[0],q[1]; h q[0];"), &mut encoder())
            .unwrap()
            .1;
        assert!(a != b);
    }

    #[test]
    fn frontier_refuses_unsupported_coefficients_nonunitary_and_budgets() {
        for gates in [
            "p(pi/3) q[0];",
            "p(0.1) q[0];",
            "rx(0.1) q[0];",
            "reset q[0];",
            "bit c; c=measure q[0];",
        ] {
            assert_eq!(norm(&parse(2, gates)), None, "{gates}");
        }
        assert_eq!(norm(&parse(7, "h q[0];")), None);
        let mut e = encoder();
        e.work = 0;
        assert!(matrix(&parse(2, "h q[0];"), &mut e).is_none());
        assert_eq!(
            norm(&parse(6, &"h q[0];".repeat(MAX_TABLE_STEPS / 4096 + 1))),
            None
        );
    }

    #[test]
    fn frontier_preference_counts_actual_blocks_without_relaxing_admission() {
        let circuit = parse(
            5,
            &format!("h q[0]; {} h q[0];", "t q[0]; tdg q[0];".repeat(64)),
        );
        let (_, cells, gate_steps) = table_cost(&circuit).unwrap();
        let block_steps = cells * blocks(&circuit).unwrap().len();
        assert!(block_steps < (1 << 17) && (1 << 17) < gate_steps);
        assert!(preferred(&circuit, 17));
        assert!(!preferred(&circuit, 8));
        assert_eq!(norm(&circuit), Some(vec![(0, integer(1))]));
        let over = parse(6, &"t q[0];".repeat(MAX_TABLE_STEPS / 4096 + 1));
        assert!(!preferred(&over, usize::MAX));
        assert!(!preferred(&parse(7, "h q[0];"), usize::MAX));
        assert!(!preferred(&parse(2, "reset q[0];"), usize::MAX));
    }

    #[test]
    fn frontier_block_operand_remapping_matches_complete_toffoli_matrix() {
        for gates in ["ccx q[2],q[0],q[1];", "h q[1]; ccz q[2],q[0],q[1]; h q[1];"] {
            let (d, actual) = matrix(&parse(4, gates), &mut encoder()).unwrap();
            assert_eq!(d, 16);
            for input in 0..d {
                let output = input ^ if input & 5 == 5 { 2 } else { 0 };
                for row in 0..d {
                    assert_eq!(
                        coefficients(&actual[row * d + input]),
                        [
                            integer(i64::from(row == output)),
                            integer(0),
                            integer(0),
                            integer(0)
                        ]
                    );
                }
            }
        }
    }

    #[test]
    fn signed_unit_root_products_preserve_radicals_and_noncanonical_sums() {
        for sign in [-1, 1] {
            for shift in 0..8 {
                let mut e = encoder();
                let root = e
                    .literal(integer(sign), shift * (ORDER / 8), false)
                    .unwrap();
                let mut value = Vec::new();
                for p in 0..4 {
                    for radical in [false, true] {
                        value.extend(
                            e.literal(ratio(p as i64 + 1, 3), p * (ORDER / 8), radical)
                                .unwrap(),
                        );
                    }
                }
                let fast = e.multiply(root.clone(), value.clone()).unwrap();
                // Split a unit root into two half roots to force the ordinary
                // generic convolution, including duplicate-result compaction.
                let mut halves = e
                    .literal(ratio(sign, 2), shift * (ORDER / 8), false)
                    .unwrap();
                halves.extend(halves.clone());
                assert!(fast == e.multiply(halves, value.clone()).unwrap());
                let mut noncanonical = value.clone();
                noncanonical.extend(value);
                let actual = e.multiply(root, noncanonical).unwrap();
                let mut expected = fast.clone();
                expected.extend(fast);
                assert!(actual == e.compact(expected).unwrap());
            }
        }
    }
}
