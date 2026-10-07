//! Complete physical-wire contraction, with certified coefficient enclosures.
//! Gate semantics and coherent local sums are shared with the exact frontier.
use super::*;
use crate::ir::StatementKind;
mod ball;
use ball::{Balls, Magnitude, Norm};

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

#[cfg(test)]
fn identity_bound(program: &Program) -> Option<Report> {
    identity_bound_with_tolerance(
        program,
        &BigRational::new(1.into(), 1_000_000_000_000i64.into()),
    )
}

pub(super) fn identity_bound_with_tolerance(
    program: &Program,
    target: &BigRational,
) -> Option<Report> {
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
    unitary::validate(program).ok()?;
    crate::symbolic::numeric_domains(program).ok()?;
    let start = Instant::now();
    let first = contract(program, &wires, &blocks, start, 64)?;
    if first.bound.as_ref().is_some_and(|u| u <= target)
        || first.lower_bound.as_ref().is_some_and(|l| l > target)
        || first.work.saturating_mul(2) > MAX_CELL_STEPS
    {
        return Some(first);
    }
    // Precision is selected by certificate success, never by gate count. Both
    // attempts share the deadline; a refused retry preserves the first bounds.
    let Some(mut second) = contract(program, &wires, &blocks, start, 128) else {
        return Some(first);
    };
    second.bound = first.bound.into_iter().chain(second.bound).min();
    second.lower_bound = first
        .lower_bound
        .into_iter()
        .chain(second.lower_bound)
        .max();
    second.work += first.work;
    Some(second)
}

fn contract(
    program: &Program,
    wires: &[crate::ir::Qubit],
    blocks: &[&[crate::ir::Statement]],
    start: Instant,
    precision: u32,
) -> Option<Report> {
    let n = wires.len();
    let dimension = 1usize << n;
    let cells = dimension * dimension;
    let domain = super::super::numeric::Enclosure { precision };
    let mut values = Balls::new(cells);
    for i in 0..dimension {
        values.one(i * dimension + i);
    }
    // M is always a point matrix, with ||U-M||_2 <= error. For the next true
    // unitary block G, ||GU-GM||_2 = ||U-M||_2. Arb encloses GM; we collect
    // the newly introduced entry radii as an operator-norm bound before
    // retaining the midpoint. Thus uncertainty adds, rather than wrapping
    // exponentially through successive entrywise interval products.
    let mut error = Magnitude::zero();
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
        let coefficients: Vec<_> = sparse
            .iter()
            .map(|row| {
                let mut values = Balls::new(row.len().max(1));
                for (i, (_, coefficient)) in row.iter().enumerate() {
                    values.set_enclosure(i, coefficient, precision);
                }
                values
            })
            .collect();
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
        let mut scratch = Balls::new(size);
        let mut roundoff = Norm::new(dimension);
        for base in (0..dimension).filter(|r| r & mask == 0) {
            if start.elapsed() >= Duration::from_secs(MAX_SECONDS) {
                return None;
            }
            if permutation {
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
                    let coefficient = &coefficients[output];
                    if coefficient.is_one(0) {
                        continue;
                    }
                    for col in 0..dimension {
                        let row = base | offsets[output];
                        let at = row * dimension + col;
                        values.multiply(at, coefficient, 0, precision);
                        roundoff.add_radius(row, col, &values, at);
                        values.midpoint(at);
                    }
                }
            } else {
                for col in 0..dimension {
                    if col % 16 == 0 && start.elapsed() >= Duration::from_secs(MAX_SECONDS) {
                        return None;
                    }
                    for output in 0..size {
                        scratch.sum_products(
                            output,
                            &values,
                            &coefficients[output],
                            sparse[output]
                                .iter()
                                .map(|(input, _)| (base | offsets[*input]) * dimension + col),
                            precision,
                        );
                    }
                    for (output, offset) in offsets.iter().enumerate() {
                        let row = base | offset;
                        roundoff.add_radius(row, col, &scratch, output);
                        scratch.midpoint(output);
                        values.swap_from(row * dimension + col, &mut scratch, output);
                    }
                }
            }
        }
        error.add_assign(&roundoff.bound());
        work += cells;
    }
    let (upper, lower) = values.certificates(dimension, &error, precision)?;
    Some(Report {
        method: "frontier",
        precision,
        bound: Some(upper),
        lower_bound: Some(lower),
        reason: "bounded",
        paths: 0,
        work,
        max_width: n,
        nodes: cells,
    })
}
