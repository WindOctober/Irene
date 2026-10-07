//! Complete physical-wire contraction, with certified coefficient enclosures.
//! Gate semantics and coherent local sums are shared with the exact frontier.
use super::*;
use crate::ir::{Gate, StatementKind};

const MAX_QUBITS: usize = 10;
const MAX_CELL_STEPS: usize = 1_500_000_000;
const MAX_SECONDS: u64 = 180;

#[cfg(test)]
mod tests;

type Matrix = Vec<Vec<(usize, Complex)>>;
fn block_matrix(
    program: &Program,
    statements: &[crate::ir::Statement],
    qubits: &[crate::ir::Qubit],
    domain: &super::super::numeric::Enclosure,
) -> Option<Matrix> {
    let (hps, operands) = crate::equivalence::operator::local_hps(program, statements, qubits)?;
    let dimension = 1 << operands.len();
    let mut matrix = vec![BTreeMap::<usize, Complex>::new(); dimension];
    let mut scalars = BTreeMap::new();
    let mut phases = BTreeMap::new();
    crate::equivalence::operator::visit_amplitudes(&hps, &operands, |input, output, closed| {
        if !scalars.contains_key(&closed.scalar) {
            scalars.insert(closed.scalar.clone(), domain.scalar(&closed.scalar)?);
        }
        let mut value = Complex::real(scalars[&closed.scalar].clone());
        for (predicate, coefficient) in closed.phase.selectors() {
            if predicate.is_one() {
                if !phases.contains_key(coefficient) {
                    phases.insert(coefficient.clone(), domain.phase(coefficient)?);
                }
                value = value.mul(&phases[coefficient]);
            } else if !predicate.is_zero() {
                return None;
            }
        }
        let prior = matrix[output].entry(input).or_insert_with(|| Complex::n(0));
        *prior = prior.add(&value);
        Some(())
    })?;
    Some(
        matrix
            .into_iter()
            .map(|r| r.into_iter().filter(|(_, v)| !v.is_zero()).collect())
            .collect(),
    )
}

pub(super) fn identity_bound(program: &Program) -> Option<Report> {
    let wires = super::super::qubits(program);
    let n = wires.len();
    if n > MAX_QUBITS || !program.numeric_inputs.is_empty() {
        return None;
    }
    let dimension = 1usize << n;
    let cells = dimension * dimension;
    let blocks = crate::equivalence::operator::blocks(program)?;
    if cells.checked_mul(blocks.len())? > MAX_CELL_STEPS {
        return None;
    }
    unitary_miter::validate(program).ok()?;
    crate::symbolic::numeric_domains(program).ok()?;
    let start = Instant::now();
    // Entrywise interval dependency grows through mixing gates. Extra precision
    // is a resource policy, not a proof assumption: final enclosures still decide.
    let mixing = program
        .body
        .statements
        .iter()
        .filter(|s| {
            matches!(
                s.kind,
                StatementKind::Apply {
                    gate: Gate::H | Gate::Rx | Gate::Ry | Gate::Crx | Gate::Cry,
                    ..
                }
            )
        })
        .count();
    let domain = super::super::numeric::Enclosure {
        precision: (256 + mixing.min(3840)) as u32,
    };
    let mut values = vec![Complex::n(0); cells];
    for i in 0..dimension {
        values[i * dimension + i] = Complex::n(1);
    }
    let mut work = 0usize;
    for block in blocks {
        if start.elapsed() >= Duration::from_secs(MAX_SECONDS) {
            return None;
        }
        let qubits: BTreeSet<_> = block
            .iter()
            .flat_map(|s| match &s.kind {
                StatementKind::Apply { qubits, .. } => qubits.clone(),
                _ => vec![],
            })
            .collect();
        let qubits: Vec<_> = qubits.into_iter().collect();
        let positions = qubits
            .iter()
            .map(|q| wires.iter().position(|w| w == q))
            .collect::<Option<Vec<_>>>()?;
        let sparse = block_matrix(program, block, &qubits, &domain)?;
        let size = sparse.len();
        let mask = positions.iter().fold(0, |m, q| m | (1 << q));
        let offsets: Vec<_> = (0..size)
            .map(|k| {
                positions
                    .iter()
                    .enumerate()
                    .fold(0, |v, (i, q)| v | (((k >> i) & 1) << q))
            })
            .collect();
        let permutation = sparse.iter().all(|r| r.len() == 1)
            && sparse.iter().map(|r| r[0].0).collect::<BTreeSet<_>>().len() == size;
        let mut scratch = vec![Complex::n(0); size];
        for base in (0..dimension).filter(|r| r & mask == 0) {
            if start.elapsed() >= Duration::from_secs(MAX_SECONDS) {
                return None;
            }
            if permutation {
                // Move MPFR allocations instead of cloning whole rows for CX/SWAP.
                let mut current: Vec<_> = (0..size).collect();
                for output in 0..size {
                    let input = sparse[output][0].0;
                    let at = current.iter().position(|i| *i == input)?;
                    if at != output {
                        for col in 0..dimension {
                            values.swap(
                                (base | offsets[at]) * dimension + col,
                                (base | offsets[output]) * dimension + col,
                            );
                        }
                        current.swap(at, output);
                    }
                }
                for output in 0..size {
                    let coefficient = &sparse[output][0].1;
                    if coefficient.im.is_zero() && coefficient.re.lo == 1 && coefficient.re.hi == 1
                    {
                        continue;
                    }
                    for col in 0..dimension {
                        let at = (base | offsets[output]) * dimension + col;
                        values[at].multiply_assign(coefficient);
                    }
                }
            } else {
                for col in 0..dimension {
                    if col % 16 == 0 && start.elapsed() >= Duration::from_secs(MAX_SECONDS) {
                        return None;
                    }
                    for output in 0..size {
                        let mut value = Complex::n(0);
                        for (input, coefficient) in &sparse[output] {
                            value = value.add(
                                &values[(base | offsets[*input]) * dimension + col]
                                    .mul(coefficient),
                            );
                        }
                        scratch[output] = value;
                    }
                    for output in 0..size {
                        std::mem::swap(
                            &mut values[(base | offsets[output]) * dimension + col],
                            &mut scratch[output],
                        );
                    }
                }
            }
        }
        work += cells;
    }
    let mut trace = Complex::n(0);
    for i in 0..dimension {
        trace = trace.add(&values[i * dimension + i]);
    }
    let norm = Complex::real(Interval::rational(&BigRational::new(
        1.into(),
        dimension.into(),
    ))?);
    trace = trace.mul(&norm);
    let (upper, lower) = trace_bounds(&trace, n)?;
    Some(Report {
        method: "frontier",
        precision: domain.precision,
        bound: Some(upper),
        lower_bound: Some(lower),
        reason: "bounded",
        paths: 0,
        work,
        max_width: n,
        nodes: cells,
    })
}
