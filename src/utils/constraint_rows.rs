//! Exact GF(2) row-space reduction shared by HPS and density-kernel guards.
//! Monomials are formal columns, NEVER independent Boolean variables.
//! Only reversible row XORs are used; no Boolean-ideal completion is claimed.

use bitgauss::BitMatrix;
use std::cmp::Ordering;
use std::collections::BTreeSet;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Error {
    BudgetExceeded,
    Contradiction,
}

pub(crate) struct Limits {
    pub rows: usize,
    pub terms: usize,
    pub cells: usize,
}

/// Each source row is a canonical set of monomials (duplicates already XORed).
/// The caller's total column order must distinguish unequal monomials.
pub(crate) fn reduce<M: Ord + Clone>(
    source: &[Vec<&M>],
    one: &M,
    limits: Limits,
    order: impl Fn(&M, &M) -> Ordering,
) -> Result<Vec<Vec<M>>, Error> {
    if source.len() > limits.rows || source.iter().any(|r| r.len() > limits.terms) {
        return Err(Error::BudgetExceeded);
    }
    if source.iter().any(|r| r.as_slice() == [one]) {
        return Err(Error::Contradiction);
    }
    if source.len() <= 1 {
        return Ok(source
            .iter()
            .filter(|r| !r.is_empty())
            .map(|r| r.iter().map(|m| (*m).clone()).collect())
            .collect());
    }
    let mut columns = BTreeSet::new();
    for &monomial in source.iter().flatten().filter(|m| **m != one) {
        columns.insert(monomial);
        if source
            .len()
            .checked_mul(columns.len().saturating_add(1))
            .is_none_or(|cells| cells > limits.cells)
        {
            return Err(Error::BudgetExceeded);
        }
    }
    let mut columns: Vec<_> = columns.into_iter().collect();
    columns.sort_by(|a, b| order(a, b));
    let rows: Vec<_> = source
        .iter()
        .map(|r| {
            let mut row: Vec<_> = r
                .iter()
                .filter(|m| **m != one)
                .map(|m| {
                    columns
                        .binary_search_by(|c| order(c, m))
                        .expect("collected column")
                })
                .collect();
            row.sort_unstable();
            if r.contains(&one) {
                row.push(columns.len());
            }
            row
        })
        .collect();
    let reduced = packed_reduce(&rows, columns.len()).ok_or(Error::Contradiction)?;
    if reduced.iter().any(|r| r.len() > limits.terms) {
        return Err(Error::BudgetExceeded);
    }
    Ok(reduced
        .into_iter()
        .map(|row| {
            row.into_iter()
                .map(|c| {
                    if c == columns.len() {
                        one.clone()
                    } else {
                        columns[c].clone()
                    }
                })
                .collect()
        })
        .collect())
}

/// Sparse rows of an augmented GF(2) matrix. `columns` is the constant column,
/// NOT a free variable. Input columns are sorted, unique and <= `columns`.
/// Returns None exactly when the row span contains the constant-one equation.
fn packed_reduce(rows: &[Vec<usize>], columns: usize) -> Option<Vec<Vec<usize>>> {
    if rows.iter().any(|r| r.as_slice() == [columns]) {
        return None;
    }
    if rows.len() <= 1 {
        return Some(rows.iter().filter(|r| !r.is_empty()).cloned().collect());
    }
    let nonzeros = rows.iter().map(Vec::len).sum::<usize>();
    if rows.len() <= 64 || columns <= 64 || nonzeros > rows.len().saturating_mul(8) {
        return block(
            rows,
            &(0..rows.len()).collect::<Vec<_>>(),
            &(0..columns).collect::<Vec<_>>(),
            columns,
            &mut vec![0; columns],
        );
    }
    // Walk the row/column incidence graph. Constants never connect components:
    // x=1 and y=1 have independent variable supports despite sharing the RHS.
    let mut incident = vec![Vec::new(); columns];
    for (i, row) in rows.iter().enumerate() {
        for &c in row.iter().filter(|&&c| c < columns) {
            incident[c].push(i);
        }
    }
    let mut seen_rows = vec![false; rows.len()];
    let mut seen_columns = vec![false; columns];
    let mut local = vec![0; columns];
    let mut result = Vec::new();
    for root in 0..rows.len() {
        if seen_rows[root] || rows[root].is_empty() {
            continue;
        }
        let mut component_rows = vec![root];
        let mut component_columns = Vec::new();
        seen_rows[root] = true;
        let mut next = 0;
        while next < component_rows.len() {
            let row = component_rows[next];
            next += 1;
            for &c in rows[row].iter().filter(|&&c| c < columns) {
                if seen_columns[c] {
                    continue;
                }
                seen_columns[c] = true;
                component_columns.push(c);
                for &i in &incident[c] {
                    if !seen_rows[i] {
                        seen_rows[i] = true;
                        component_rows.push(i);
                    }
                }
            }
        }
        if component_rows.len() == 1 {
            result.push(rows[root].clone());
        } else {
            component_columns.sort_unstable();
            result.extend(block(
                rows,
                &component_rows,
                &component_columns,
                columns,
                &mut local,
            )?);
        }
    }
    Some(result)
}

fn block(
    rows: &[Vec<usize>],
    selected: &[usize],
    columns: &[usize],
    constant: usize,
    local: &mut [usize],
) -> Option<Vec<Vec<usize>>> {
    for (i, &c) in columns.iter().enumerate() {
        local[c] = i;
    }
    let mut matrix = BitMatrix::zeros(selected.len(), columns.len() + 1);
    for (i, &row) in selected.iter().enumerate() {
        for &c in &rows[row] {
            matrix.set_bit(
                i,
                if c == constant {
                    columns.len()
                } else {
                    local[c]
                },
                true,
            );
        }
    }
    matrix.gauss(true);
    let mut result = Vec::new();
    for i in 0..selected.len() {
        let mut row = Vec::new();
        for (b, mut word) in matrix.row(i).block_iter().enumerate() {
            while word != 0 {
                let bit = word.leading_zeros() as usize;
                let c = b * 64 + bit;
                word ^= 1u64 << (63 - bit);
                if c < columns.len() {
                    row.push(columns[c]);
                }
            }
        }
        if matrix.bit(i, columns.len()) {
            if row.is_empty() {
                return None;
            }
            row.push(constant);
        }
        if !row.is_empty() {
            result.push(row);
        }
    }
    Some(result)
}

#[cfg(test)]
mod tests;
