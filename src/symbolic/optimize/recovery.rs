//! Exact recovery of affine Boolean functions hidden inside shared XAGs.
//!
//! Run only after the existing local rules stall. Bounds charge algebraic
//! operations and materialized terms, not the number of variables. Refusal is
//! inconclusive and leaves the original predicate intact.
use std::collections::HashMap;

use crate::symbolic::{BooleanPolynomial, Component, PhasePolynomial};

const MAX_TERMS: usize = 4096;
const MAX_WORK: usize = 1_000_000;

enum Conclusion {
    Proven(Option<BooleanPolynomial>),
    Refused,
}

pub(super) struct Recovery {
    work: usize,
    // Invocation-local memo also suppresses repeated budget refusals. Only
    // completed conclusions are additionally stored on the immutable node.
    cache: HashMap<BooleanPolynomial, Conclusion>,
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
        let hidden = hidden_zero(&y(200), &y(201)).xor(&y(202));
        assert_eq!(exhausted.affine(&hidden), None);
        assert!(!hidden.is_affine());
    }

    #[test]
    fn completed_conclusions_survive_new_reduction_attempts() {
        let hidden = hidden_zero(&y(0), &y(1)).xor(&y(2));
        let nonlinear = y(3).and(&y(4));
        let keys = HashMap::from([(hidden.clone(), 7), (nonlinear.clone(), 9)]);
        let mut first = Recovery::default();
        assert_eq!(first.affine(&hidden), Some(y(2)));
        assert_eq!(first.affine(&nonlinear), None);
        assert_eq!(nonlinear.cached_affine_recovery(), Some(&None));
        drop(first);

        let mut later = Recovery {
            work: 0,
            cache: HashMap::new(),
        };
        assert_eq!(later.affine(&hidden.clone()), Some(y(2)));
        assert_eq!(later.affine(&nonlinear), None);
        assert_eq!(later.work, 0);
        // Populating metadata must not change structural hashing/equality.
        assert_eq!(keys.get(&hidden), Some(&7));
        assert_eq!(keys.get(&nonlinear), Some(&9));
    }

    #[test]
    fn repeated_reducers_share_facts_but_recheck_observable_paths() {
        use crate::ir::{Qubit, SymbolId};
        use crate::symbolic::{HybridMemory, PhaseCoefficient, Scalar};
        use num_rational::BigRational;
        let nonlinear = y(0).and(&y(1));
        let mut phase = PhasePolynomial::zero();
        phase.add_boolean(
            &nonlinear,
            PhaseCoefficient::rational(BigRational::new(1.into(), 2.into())),
        );
        let mut first = Component {
            guard: Vec::new(),
            scalar: Scalar::one(),
            path_support: [0, 1, 2].into(),
            phase,
            output: HybridMemory {
                quantum: (0..3)
                    .map(|i| {
                        (
                            Qubit {
                                register: SymbolId(0),
                                index: i,
                            },
                            y(i),
                        )
                    })
                    .collect(),
                ..HybridMemory::default()
            },
        };
        let mut second = first.clone();
        assert!(super::super::path_sum::reduce_path_sums(&mut first, false));
        assert!(
            second
                .phase
                .selectors()
                .any(|(p, _)| p.cached_affine_recovery().is_some())
        );
        assert!(super::super::path_sum::reduce_path_sums(&mut second, false));
        assert_eq!(first, second);
        // A cached structural fact does not authorize dropping visible paths.
        assert_eq!(second.path_support, [0, 1, 2].into());
        let mut expected = PhasePolynomial::zero();
        expected.add_boolean(
            &nonlinear,
            PhaseCoefficient::rational(BigRational::new(1.into(), 2.into())),
        );
        assert_eq!(second.phase, expected);
        second.output.quantum.remove(&Qubit {
            register: SymbolId(0),
            index: 0,
        });
        assert!(super::super::path_sum::reduce_path_sums(&mut second, false));
        assert!(!second.path_support.contains(&0));
    }

    #[test]
    fn refusal_is_local_and_does_not_poison_later_proofs() {
        let hidden = hidden_zero(&y(0), &y(1)).xor(&y(2));
        let mut limited = Recovery {
            work: 1,
            cache: HashMap::new(),
        };
        assert_eq!(limited.affine(&hidden), None);
        assert!(hidden.cached_affine_recovery().is_none());
        assert!(matches!(
            limited.cache.get(&hidden),
            Some(Conclusion::Refused)
        ));
        assert_eq!(Recovery::default().affine(&hidden), Some(y(2)));
    }

    #[test]
    fn structural_cache_hits_publish_to_distinct_roots_but_not_changed_forms() {
        let make = || hidden_zero(&y(0), &y(1)).xor(&y(2));
        let original = make();
        let rebuilt = make();
        let mut recovery = Recovery::default();
        assert_eq!(recovery.affine(&original), Some(y(2)));
        assert!(rebuilt.cached_affine_recovery().is_none());
        assert_eq!(recovery.affine(&rebuilt), Some(y(2)));
        assert_eq!(rebuilt.cached_affine_recovery(), Some(&Some(y(2))));

        let changed = rebuilt.substitute(&Variable::Path(2), &y(3).and(&y(4)));
        assert!(changed.cached_affine_recovery().is_none());
        assert_eq!(Recovery::default().affine(&changed), None);
        assert_eq!(changed.cached_affine_recovery(), Some(&None));
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
        if crate::symbolic::deadline::expired() {
            return None;
        }
        if let Some(result) = p.cached_affine_recovery() {
            return result.clone();
        }
        if p.is_affine() {
            return None;
        }
        if let Some(result) = self.cache.get(p) {
            return match result {
                Conclusion::Proven(result) => {
                    // Structurally equal but separately allocated roots share
                    // the conclusion too; HashMap checks Eq after hashing.
                    p.cache_affine_recovery(result.clone());
                    result.clone()
                }
                Conclusion::Refused => None,
            };
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
            p.cache_affine_recovery(result.clone());
            self.cache
                .insert(p.clone(), Conclusion::Proven(result.clone()));
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
        if !refused {
            p.cache_affine_recovery(result.clone());
        }
        self.cache.insert(
            p.clone(),
            if refused {
                Conclusion::Refused
            } else {
                Conclusion::Proven(result.clone())
            },
        );
        result
    }

    pub(super) fn recover(&mut self, c: &mut Component) -> bool {
        if c.path_support.is_empty() {
            return false;
        }
        let mut changed = false;
        for g in &mut c.guard {
            if crate::symbolic::deadline::expired() {
                return changed;
            }
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
            if crate::symbolic::deadline::expired() {
                return false;
            }
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
