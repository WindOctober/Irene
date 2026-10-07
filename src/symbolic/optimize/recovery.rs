//! Exact recovery of affine Boolean functions hidden inside shared XAGs.
//!
//! Run only after the existing local rules stall. Bounds charge algebraic
//! operations and materialized terms, not the number of variables. Refusal is
//! inconclusive and leaves the original predicate intact.
use std::collections::HashMap;

use crate::symbolic::{BooleanPolynomial, Component, PhasePolynomial};

const MAX_TERMS: usize = 4096;
const MAX_WORK: usize = 1_000_000;

pub(super) struct Recovery {
    work: usize,
    cache: HashMap<BooleanPolynomial, Option<BooleanPolynomial>>,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::Variable;

    fn y(i: usize) -> BooleanPolynomial {
        BooleanPolynomial::variable(Variable::Path(i))
    }

    fn hidden_zero(a: &BooleanPolynomial, b: &BooleanPolynomial) -> BooleanPolynomial {
        a.complement()
            .and(&b.complement())
            .xor(&a.and(b))
            .xor(a)
            .xor(b)
            .complement()
    }

    #[test]
    fn wide_hidden_affine_functions_are_recovered_exactly() {
        let a = BooleanPolynomial::xor_all((0..150).map(y));
        let zero = hidden_zero(&a, &y(150));
        assert!(!zero.is_affine());
        let mut recovery = Recovery::default();
        assert_eq!(recovery.affine(&zero), Some(BooleanPolynomial::zero()));
        assert_eq!(
            recovery.affine(&zero.complement()),
            Some(BooleanPolynomial::one())
        );
        assert_eq!(recovery.affine(&zero.xor(&y(151))), Some(y(151)));
    }

    #[test]
    fn nonlinear_and_budget_refusals_do_not_claim_affinity() {
        let nonlinear = y(0).and(&y(1));
        let mut recovery = Recovery::default();
        for i in 0..100 {
            assert_eq!(recovery.affine(&nonlinear.xor(&y(i + 2))), None);
        }
        // Completed nonlinear queries charge actual work, not a whole attempt.
        let hidden = hidden_zero(&y(200), &y(201)).xor(&y(202));
        assert_eq!(recovery.affine(&hidden), Some(y(202)));
        let mut exhausted = Recovery {
            work: 1,
            cache: HashMap::new(),
        };
        assert_eq!(exhausted.affine(&hidden), None);
        assert!(!hidden.is_affine());
    }
}

impl Default for Recovery {
    fn default() -> Self {
        Self {
            work: MAX_WORK,
            cache: HashMap::new(),
        }
    }
}

impl Recovery {
    fn affine(&mut self, p: &BooleanPolynomial) -> Option<BooleanPolynomial> {
        if p.is_affine() {
            return None;
        }
        if let Some(result) = self.cache.get(p) {
            return result.clone();
        }
        if self.work == 0 {
            return None;
        }
        let (network, variables) = BooleanPolynomial::graph_network(std::slice::from_ref(p));
        let mut graph_work = self.work.min(200_000);
        let before_graph = graph_work;
        let graph_result = crate::xag::davio::affine(&network, &mut graph_work, 20_000);
        self.work -= before_graph - graph_work;
        if let Some(result) = graph_result {
            let result = result.map(|(constant, inputs)| {
                BooleanPolynomial::xor_all(
                    std::iter::once(if constant {
                        BooleanPolynomial::one()
                    } else {
                        BooleanPolynomial::zero()
                    })
                    .chain(
                        inputs
                            .into_iter()
                            .map(|i| BooleanPolynomial::variable(variables[i as usize].clone())),
                    ),
                )
            });
            self.cache.insert(p.clone(), result.clone());
            return result;
        }
        let mut allowance = self.work.min(MAX_TERMS * 64);
        let before = allowance;
        let expanded = p.expanded_terms_with_work(MAX_TERMS, &mut allowance);
        let refused = expanded.is_none();
        let result = expanded
            .filter(|terms| terms.iter().all(|m| m.variables().count() <= 1))
            .map(|terms| {
                BooleanPolynomial::xor_all(terms.into_iter().map(BooleanPolynomial::from_monomial))
            });
        // A checked-subtraction refusal consumes the rest of this attempt's
        // allowance too; do not repeatedly retry an unaffordable operation.
        self.work = self
            .work
            .saturating_sub(if refused { before } else { before - allowance });
        self.cache.insert(p.clone(), result.clone());
        result
    }

    pub(super) fn recover(&mut self, c: &mut Component) -> bool {
        if c.path_support.is_empty() {
            return false;
        }
        let mut changed = false;
        for g in &mut c.guard {
            if let Some(next) = self.affine(g) {
                *g = next;
                changed = true;
            }
        }
        // Let newly exposed guard pivots run before changing phase syntax.
        if changed {
            return true;
        }
        let mut replacements = Vec::new();
        for (p, coefficient) in c.phase.selectors() {
            let next = self.affine(&p);
            changed |= next.is_some();
            replacements.push((next.unwrap_or(p), coefficient.clone()));
        }
        if !changed {
            return false;
        }
        let mut next = PhasePolynomial::zero();
        for (p, coefficient) in replacements {
            next.add_boolean(&p, coefficient);
        }
        if next == c.phase {
            return false;
        }
        c.phase = next;
        true
    }
}
