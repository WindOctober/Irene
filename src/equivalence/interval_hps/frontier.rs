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

#[cfg(test)]
pub(super) fn identity_bound_with_tolerance(program: &Program, target: &BigRational) -> Option<Report> {
    identity_bound_with_witness_target(program, target, target)
}

pub(super) fn identity_bound_with_witness_target(
    program: &Program,
    target: &BigRational,
    witness_target: &BigRational,
) -> Option<Report> {
    let wires = super::super::qubits(program);
    let n = wires.len();
    if n > MAX_QUBITS || !program.numeric_inputs.is_empty() {
        return None;
    }
    let dimension = 1usize << n;
    let cells = dimension * dimension;
    let original = crate::equivalence::operator::blocks(program)?;
    // Concatenate only adjacent slices in their existing order. No gate
    // commutation, butterfly, tiling, point coefficients, or third block.
    let mut at = 0;
    let blocks: Vec<_> = original
        .chunks(2)
        .map(|chunk| {
            let len = chunk.iter().map(|b| b.len()).sum::<usize>();
            let block = &program.body.statements[at..at + len];
            at += len;
            block
        })
        .collect();
    // Charge TWO original block units even for an odd last singleton. This
    // preserves a conservative cell-step budget instead of doubling resources
    // merely because the fused block list has half as many entries.
    if cells.checked_mul(blocks.len())?.checked_mul(2)? > MAX_CELL_STEPS {
        return None;
    }
    unitary::validate(program).ok()?;
    crate::symbolic::numeric_domains(program).ok()?;
    let start = Instant::now();
    let mut budget = MAX_CELL_STEPS;
    if n > 0 {
        for precision in [64, 128] {
            if let Some(mut witness) = contract(
                program,
                &wires,
                &blocks,
                start,
                precision,
                true,
                &mut budget,
            ) && witness
                .lower_bound
                .as_ref()
                .is_some_and(|l| l > witness_target)
            {
                witness.work = MAX_CELL_STEPS - budget;
                return Some(witness);
            }
        }
    }
    let mut first = contract(program, &wires, &blocks, start, 64, false, &mut budget)?;
    first.work = MAX_CELL_STEPS - budget;
    if first.bound.as_ref().is_some_and(|u| u <= target)
        || first.lower_bound.as_ref().is_some_and(|l| l > target)
        || cells.checked_mul(blocks.len())?.checked_mul(2)? > budget
    {
        return Some(first);
    }
    // Precision is selected by certificate success, never by gate count. Both
    // attempts share the deadline; a refused retry preserves the first bounds.
    let Some(mut second) = contract(program, &wires, &blocks, start, 128, false, &mut budget)
    else {
        return Some(first);
    };
    second.bound = first.bound.into_iter().chain(second.bound).min();
    second.lower_bound = first
        .lower_bound
        .into_iter()
        .chain(second.lower_bound)
        .max();
    second.work = MAX_CELL_STEPS - budget;
    Some(second)
}

fn contract(
    program: &Program,
    wires: &[crate::ir::Qubit],
    blocks: &[&[crate::ir::Statement]],
    start: Instant,
    precision: u32,
    witness: bool,
    budget: &mut usize,
) -> Option<Report> {
    let n = wires.len();
    let dimension = 1usize << n;
    let columns = if witness { 3 } else { dimension };
    let cells = dimension * columns;
    let domain = super::super::numeric::Enclosure { precision };
    let mut values = Balls::new(cells);
    let mut error = Magnitude::zero();
    if witness {
        if dimension < 2 {
            return None;
        }
        values.one(0);
        values.one(columns + 1);
        let amplitude = Complex::real(Interval::n(1).div(&Interval::n(dimension as i32).sqrt()?)?);
        let mut initial = Norm::new(dimension.max(columns));
        for row in 0..dimension {
            let at = row * columns + 2;
            values.set_enclosure(at, &amplitude, precision);
            initial.add_radius(row, 2, &values, at);
            values.midpoint(at);
        }
        error.add_assign(&initial.bound());
    } else {
        for i in 0..dimension {
            values.one(i * columns + i);
        }
    }
    // M is a point matrix approximating either U or the three columns U S.
    // For the exact current matrix T and next unitary block G,
    // ||GT-GM||_2 = ||T-M||_2 <= error. Arb encloses GM; we collect
    // the newly introduced entry radii as an operator-norm bound before
    // retaining the midpoint. Thus uncertainty adds, rather than wrapping
    // exponentially through successive entrywise interval products.
    let mut work = 0usize;
    for block in blocks {
        if start.elapsed() >= Duration::from_secs(MAX_SECONDS) {
            return None;
        }
        // Charge every attempted block, including refused attempts, across
        // both precision levels and full fallback. No free witness budget.
        *budget = budget.checked_sub(cells.checked_mul(2)?)?;
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
        let mut roundoff = Norm::new(dimension.max(columns));
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
                        for col in 0..columns {
                            values.swap(
                                (base | offsets[at]) * columns + col,
                                (base | offsets[output]) * columns + col,
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
                    for col in 0..columns {
                        let row = base | offsets[output];
                        let at = row * columns + col;
                        values.multiply(at, coefficient, 0, precision);
                        roundoff.add_radius(row, col, &values, at);
                        values.midpoint(at);
                    }
                }
            } else {
                for col in 0..columns {
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
                                .map(|(input, _)| (base | offsets[*input]) * columns + col),
                            precision,
                        );
                    }
                    for (output, offset) in offsets.iter().enumerate() {
                        let row = base | offset;
                        roundoff.add_radius(row, col, &scratch, output);
                        scratch.midpoint(output);
                        values.swap_from(row * columns + col, &mut scratch, output);
                    }
                }
            }
        }
        error.add_assign(&roundoff.bound());
        work += cells * 2;
    }
    let (upper, lower) = if witness {
        // 2 is the universal channel bound, never inferred from probe agreement.
        (
            BigRational::from_integer(2.into()),
            values.witness_lower(dimension, &error, precision)?,
        )
    } else {
        values.certificates(dimension, &error, precision)?
    };
    Some(Report {
        method: if witness { "state-witness" } else { "frontier" },
        precision,
        bound: Some(upper),
        lower_bound: Some(lower),
        reason: if witness {
            "certified-input-state"
        } else {
            "bounded"
        },
        paths: 0,
        work,
        max_width: n,
        nodes: cells,
    })
}
