//! Case analysis of free coordinates in complete products of exact sums.
//! Prove both Boolean cofactors; unlike bound-path elimination they are NOT
//! added together. Inputs and backend results must be complete, well-defined,
//! path-free expressions. Failure is inconclusive and produces no certificate.
use super::factor_normalize::normalize as normalize_factor;
use super::product_form::Product;
use crate::equivalence::density::aggregate::KernelBooleanPolynomial;
use crate::equivalence::density::aggregate::KernelPhasePolynomial;
use crate::equivalence::density::aggregate::KernelScalar;
use crate::equivalence::density::aggregate::KernelVariable;
use crate::equivalence::density::aggregate::collection::{
    ExactAggregate, ExactTerm, accumulate_exact_term,
};
use crate::equivalence::density::aggregate::sums::free_split::restrict_aggregate;
use std::collections::{BTreeMap, BTreeSet};

pub(in crate::equivalence::density::aggregate) const MAX_PRODUCT_SPLIT_DEPTH: usize = 4;
const MAX_FACTORS: usize = 128;

/// All proof and arithmetic work shares one backend across BOTH branches.
/// Matching true certifies whole-product equality. Arithmetic/refinement must
/// preserve complete operands; None cannot expose an accumulated prefix.
pub(in crate::equivalence::density::aggregate) trait Proof {
    fn matches(
        &mut self,
        left: &Product,
        right: &Product,
        relevant: &mut BTreeSet<KernelVariable>,
    ) -> bool;
    fn free_splits(&mut self) -> &mut usize;
    fn charge(&mut self, sum: &ExactAggregate) -> Option<()>;
    fn refine(&mut self, sum: ExactAggregate) -> Option<Vec<ExactAggregate>>;
    fn multiply(&mut self, left: ExactAggregate, right: ExactAggregate) -> Option<ExactAggregate>;
}

pub(in crate::equivalence::density::aggregate) fn prove(
    left: Product,
    right: Product,
    backend: &mut impl Proof,
    depth: usize,
) -> bool {
    let mut relevant = BTreeSet::new();
    if backend.matches(&left, &right, &mut relevant) {
        return true;
    }
    if depth >= MAX_PRODUCT_SPLIT_DEPTH || *backend.free_splits() == 0 {
        return false;
    }
    // A coordinate shared by independent factors is a parameter, not a
    // bound summation variable. Prove BOTH cofactors separately; never add
    // them. Ignore selectors when scheduling, but retain them in every child.
    let mut counts = BTreeMap::<KernelVariable, usize>::new();
    let mut coupled = BTreeMap::<KernelVariable, usize>::new();
    for factor in left.factors.iter().chain(&right.factors) {
        for (entry, coefficients) in factor {
            let shared = entry
                .constraints
                .iter()
                .flat_map(KernelBooleanPolynomial::variables)
                .collect::<BTreeSet<_>>();
            for phase in coefficients.keys() {
                for (monomial, _) in phase.terms() {
                    let private = monomial
                        .variables()
                        .filter(|variable| !shared.contains(*variable))
                        .collect::<Vec<_>>();
                    let ket = private.iter().any(|variable| {
                        matches!(
                            variable,
                            KernelVariable::InputKet(_) | KernelVariable::QuantumOutputKet(_)
                        )
                    });
                    let bra = private.iter().any(|variable| {
                        matches!(
                            variable,
                            KernelVariable::InputBra(_) | KernelVariable::QuantumOutputBra(_)
                        )
                    });
                    if ket && bra {
                        for variable in private {
                            *coupled.entry(variable.clone()).or_default() += 1;
                        }
                    }
                }
            }
        }
        let variables = factor
            .values()
            .flat_map(BTreeMap::keys)
            .flat_map(KernelPhasePolynomial::variables)
            .collect::<BTreeSet<_>>();
        for variable in variables {
            if variable.is_bound_path() {
                return false;
            }
            *counts.entry(variable).or_default() += 1;
        }
    }
    // Mixed private ket/bra monomials block exact tensor refinement. A
    // cofactor can remove that obstruction before splitting merely shared
    // parameters. This is scheduling only, with identical proof budgets.
    let mut candidates = if coupled.is_empty() { counts } else { coupled };
    if candidates
        .keys()
        .any(|variable| relevant.contains(variable))
    {
        candidates.retain(|variable, _| relevant.contains(variable));
    }
    let Some((variable, _)) = candidates.into_iter().max_by_key(|(_, count)| *count) else {
        return false;
    };
    if variable.is_bound_path() {
        return false;
    }
    *backend.free_splits() -= 1;
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!("aggregate factored cofactor: depth={depth} variable={variable:?}");
    }
    for value in [false, true] {
        let Some(l) = restrict(&left, &variable, value, backend) else {
            return false;
        };
        let Some(r) = restrict(&right, &variable, value, backend) else {
            return false;
        };
        if !prove(l, r, backend, depth + 1) {
            return false;
        }
    }
    true
}

pub(in crate::equivalence::density::aggregate) fn restrict(
    source: &Product,
    variable: &KernelVariable,
    value: bool,
    backend: &mut impl Proof,
) -> Option<Product> {
    if variable.is_bound_path() {
        return None;
    }
    let mut common = restrict_aggregate(&source.common, variable, value)?;
    let mut factors = Vec::new();
    for factor in &source.factors {
        backend.charge(factor)?;
        for factor in backend.refine(restrict_aggregate(factor, variable, value)?)? {
            if factor.is_empty() {
                return Some(Product {
                    common: ExactAggregate::new(),
                    factors: Vec::new(),
                });
            }
            let (factor, scalar, phase) = normalize_factor(factor)?;
            backend.charge(&factor)?;
            let mut unit = ExactAggregate::new();
            accumulate_exact_term(
                ExactTerm {
                    constraints: Vec::new(),
                    coefficient: KernelScalar::Rational(scalar),
                    phase,
                },
                &mut unit,
                &mut 0,
            )?;
            common = backend.multiply(common, unit)?;
            // A fully reduced one-atom factor belongs in the common term.
            // Multiply it in with its selector; do not discard an indicator
            // merely because its scalar/phase normalized to one.
            if factor.values().map(BTreeMap::len).sum::<usize>() == 1 {
                common = backend.multiply(common, factor)?;
                continue;
            }
            factors.push(factor);
            if factors.len() > MAX_FACTORS {
                return None;
            }
        }
    }
    Some(Product { common, factors })
}
