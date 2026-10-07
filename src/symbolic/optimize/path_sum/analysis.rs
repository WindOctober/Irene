//! Read-only analysis of a stable component. Rebuild after every rewrite.
use std::cell::Cell;
use std::collections::BTreeMap;
use std::convert::Infallible;

use super::*;

// Cap index incidences, not the phase semantics. Overflow uses full scanning.
const MAX_INCIDENCES: usize = 1_000_000;
const WITNESS_WORK: usize = 100_000;

struct Term {
    selector: BooleanPolynomial,
    coefficient: PhaseCoefficient,
    size: Cell<Option<usize>>,
}

pub(super) struct Analysis {
    terms: Vec<Term>,
    by_variable: Option<BTreeMap<Variable, Vec<usize>>>,
    pub blocked: BTreeSet<Variable>,
    pub scalar_variables: BTreeSet<Variable>,
    pub history: BTreeSet<Variable>,
    pub phase_variables: BTreeSet<Variable>,
}

impl Analysis {
    pub fn new(c: &Component) -> Self {
        Self::with_limit(c, MAX_INCIDENCES)
    }

    fn with_limit(c: &Component, limit: usize) -> Self {
        let mut by_variable = Some(BTreeMap::<_, Vec<_>>::new());
        let mut phase_variables = BTreeSet::new();
        let mut incidences = 0usize;
        let terms = c
            .phase
            .selectors()
            .enumerate()
            .map(|(i, (selector, coefficient))| {
                let support = selector.variables();
                incidences = incidences.saturating_add(support.len());
                if incidences > limit {
                    by_variable = None;
                }
                for variable in support {
                    if let Some(index) = &mut by_variable {
                        index.entry(variable.clone()).or_default().push(i);
                    }
                    phase_variables.insert(variable);
                }
                Term {
                    selector,
                    coefficient: coefficient.clone(),
                    size: Cell::new(None),
                }
            })
            .collect();
        let mut scalar_variables = BTreeSet::new();
        collect_scalar_variables(&c.scalar, &mut scalar_variables);
        Self {
            terms,
            by_variable,
            phase_variables,
            blocked: c
                .guard
                .iter()
                .chain(c.output.quantum.values())
                .chain(c.output.classical.values())
                .flat_map(BooleanPolynomial::variables)
                .collect(),
            scalar_variables,
            history: c
                .output
                .history
                .iter()
                .map(HistoryEntry::value)
                .flat_map(BooleanPolynomial::variables)
                .collect(),
        }
    }

    pub fn query<'a>(&'a self, variable: &'a Variable) -> Query<'a> {
        let terms = if let Some(index) = &self.by_variable {
            index
                .get(variable)
                .into_iter()
                .flatten()
                .map(|&i| &self.terms[i])
                .collect()
        } else {
            self.terms
                .iter()
                .filter(|t| t.selector.variables().contains(variable))
                .collect::<Vec<_>>()
        };
        Query {
            variable,
            terms: terms
                .into_iter()
                .map(|term| QueryTerm {
                    term,
                    cofactors: None,
                })
                .collect(),
        }
    }
}

pub(super) struct Query<'a> {
    variable: &'a Variable,
    terms: Vec<QueryTerm<'a>>,
}

struct QueryTerm<'a> {
    term: &'a Term,
    cofactors: Option<(BooleanPolynomial, BooleanPolynomial)>,
}

impl Query<'_> {
    pub fn len(&self) -> usize {
        self.terms.len()
    }

    pub fn coefficient(&self, i: usize) -> &PhaseCoefficient {
        &self.terms[i].term.coefficient
    }

    pub fn size(&self, i: usize) -> usize {
        let term = self.terms[i].term;
        let size = term
            .size
            .get()
            .unwrap_or_else(|| term.selector.storage_size());
        term.size.set(Some(size));
        size
    }

    pub fn cofactors(&mut self, i: usize) -> &(BooleanPolynomial, BooleanPolynomial) {
        let entry = &mut self.terms[i];
        entry.cofactors.get_or_insert_with(|| {
            (
                entry
                    .term
                    .selector
                    .substitute(self.variable, &BooleanPolynomial::zero()),
                entry
                    .term
                    .selector
                    .substitute(self.variable, &BooleanPolynomial::one()),
            )
        })
    }

    /// All existing phase profiles require 4*(P(1,z)-P(0,z)) to be integral
    /// for EVERY z. An exact counterexample rejects only that unconditional
    /// local profile, never the program. Passing these probes proves nothing.
    pub fn excludes_local_profile(&self) -> bool {
        let mut work = WITNESS_WORK;
        let mut fractional = Vec::new();
        for i in 0..self.len() {
            // Never draw a conclusion from an incomplete rational sum.
            let Some(coefficient) = self.coefficient(i).as_rational() else {
                return false;
            };
            // Quarter-turn terms contribute integers to 4*delta under ANY
            // assignment, so they cannot affect this necessary condition.
            if (coefficient * integer(4)).is_integer() {
                continue;
            }
            let Some(remaining) = work.checked_sub(self.size(i)) else {
                return false;
            };
            work = remaining;
            fractional.push(i);
        }
        if fractional.is_empty() {
            return false;
        }
        for other in [false, true] {
            let mut delta = integer(0);
            for &i in &fractional {
                let entry = &self.terms[i];
                let eval = |path| {
                    entry
                        .term
                        .selector
                        .evaluate::<Infallible>(|v| {
                            Ok(if v == self.variable { path } else { other })
                        })
                        .unwrap()
                };
                let low = eval(false);
                let high = eval(true);
                if low != high {
                    let coefficient = entry.term.coefficient.as_rational().unwrap();
                    delta += if high { coefficient } else { -coefficient };
                }
            }
            if !(delta * integer(4)).is_integer() {
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests;
