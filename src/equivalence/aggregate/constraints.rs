//! Exact kernel constraint preparation and unique bound-path substitution.

use super::*;
use crate::symbolic::BooleanPolynomial;
use crate::utils::constraint_rows::{self as rows, Error, Limits};

pub(super) fn graph_rows(t: &WorkingTerm) -> Result<Vec<KernelBooleanPolynomial>, Error> {
    let summands: Vec<_> = t
        .constraints
        .iter()
        .map(|p| p.as_graph().xor_terms())
        .collect();
    let source: Vec<_> = summands.iter().map(|r| r.iter().collect()).collect();
    let rank = |p: &BooleanPolynomial| match p.as_variable() {
        None => 0,
        Some(v) if t.paths.contains(&KernelVariable::from_graph_variable(v)) => 1,
        _ => 2,
    };
    rows::reduce(
        &source,
        &BooleanPolynomial::one(),
        Limits {
            rows: usize::MAX,
            terms: usize::MAX,
            cells: 1_000_000,
        },
        |a, b| {
            rank(a)
                .cmp(&rank(b))
                .then_with(|| if rank(a) == 1 { b.cmp(a) } else { a.cmp(b) })
        },
    )
    .map(|rs| {
        rs.into_iter()
            .map(|r| {
                KernelBooleanPolynomial::from_graph(
                    r.into_iter()
                        .fold(BooleanPolynomial::zero(), |a, b| a.xor(&b)),
                )
            })
            .collect()
    })
}

impl WorkingTerm {
    pub(super) fn from_kernel(term: &KernelTerm) -> Self {
        // Reify every visible terminal coordinate as a canonical free kernel
        // index. This turns alpha-equivalent path-dependent output syntax into
        // ordinary delta constraints that path elimination can canonicalize.
        let mut constraints = term
            .ket_guard
            .iter()
            .chain(&term.bra_guard)
            .cloned()
            .chain(
                term.history_equalities
                    .iter()
                    .map(|equality| equality.equation()),
            )
            .collect::<Vec<_>>();
        constraints.extend(term.quantum_outputs_ket.iter().enumerate().map(
            |(position, expression)| {
                KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(position))
                    .xor(expression)
            },
        ));
        constraints.extend(term.quantum_outputs_bra.iter().enumerate().map(
            |(position, expression)| {
                KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputBra(position))
                    .xor(expression)
            },
        ));
        for (position, output) in term.classical_outputs.iter().enumerate() {
            let index =
                KernelBooleanPolynomial::variable(KernelVariable::ClassicalOutput(position));
            // Both deltas are required: sharing one free coordinate preserves the
            // classical-output dephasing condition ket == bra.
            constraints.push(index.xor(&output.ket));
            constraints.push(index.xor(&output.bra));
        }

        WorkingTerm {
            constraints,
            // KernelTerm is public syntax, so defensively refuse to treat a free
            // input/output index accidentally placed in a path set as a binder.
            paths: term
                .ket_paths
                .union(&term.bra_paths)
                .filter(|variable| variable.is_bound_path())
                .cloned()
                .collect(),
            coefficient: term.weight.product(),
            phase: KernelPhasePolynomial::difference(&term.phase.ket, &term.phase.bra),
        }
    }

    /// Canonicalizes the affine equations by exact GF(2) RREF.
    ///
    /// Nonlinear equations are deliberately only sorted and deduplicated.
    /// Their complete ANF row span is canonicalized once at the end, without
    /// claiming completeness for their Boolean ideal.
    pub(super) fn normalize_constraints(&mut self) -> ConstraintNormalization {
        let affine = self
            .constraints
            .iter()
            .filter(|equation| {
                !equation.is_zero()
                    && equation
                        .terms()
                        .all(|monomial| monomial.variables().nth(1).is_none())
            })
            .collect::<Vec<_>>();
        let mut normalized = match constraint_rows::reduce(&affine) {
            Ok(rows) => rows,
            Err(status) => return status,
        };
        normalized.extend(
            self.constraints
                .iter()
                .filter(|equation| {
                    equation
                        .terms()
                        .any(|monomial| monomial.variables().nth(1).is_some())
                })
                .cloned(),
        );
        normalized.sort();
        normalized.dedup();
        self.constraints = normalized;
        ConstraintNormalization::Normalized
    }

    /// Chooses the smallest exact equation `v xor f = 0` for a bound path.
    pub(super) fn best_constraint_pivot(
        &self,
    ) -> Option<(KernelVariable, KernelBooleanPolynomial)> {
        let mut best = None;
        let mut best_size = usize::MAX;
        for equation in &self.constraints {
            // Equal-size rows cannot beat the first candidate. In particular,
            // do not repeatedly inspect every monomial of thousands of rows
            // after a small pivot has already been found. This preserves the
            // original min_by_key tie order, including the first pivot in a row.
            if equation.term_count() >= best_size {
                continue;
            }
            for atom in equation.terms() {
                let mut variables = atom.variables();
                let Some(variable) = variables.next() else {
                    continue;
                };
                if variables.next().is_none()
                    && self.paths.contains(variable)
                    && !equation
                        .terms()
                        .any(|term| term != atom && term.contains(variable))
                {
                    best = Some((variable, equation));
                    best_size = equation.term_count();
                    break;
                }
            }
        }
        best.map(|(variable, equation)| {
            (
                variable.clone(),
                equation.xor(&KernelBooleanPolynomial::variable(variable.clone())),
            )
        })
    }

    pub(super) fn substitute(
        &mut self,
        variable: &KernelVariable,
        replacement: &KernelBooleanPolynomial,
    ) {
        for equation in &mut self.constraints {
            if equation.variables().contains(variable) {
                *equation = equation.substitute(variable, replacement);
            }
        }
        self.coefficient = self.coefficient.substitute(variable, replacement);
        self.phase.substitute(variable, replacement);
    }
}

#[cfg(test)]
mod tests;
