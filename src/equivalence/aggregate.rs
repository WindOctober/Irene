//! Exact, resource-bounded reduction of density-kernel summations.
//!
//! This pass works after ket/bra doubling, where hidden-history equalities are
//! available. Local reduction does not enumerate assignments; a bounded
//! exact Shannon fallback handles small residual sums. A constraint
//! `v xor f = 0`, with bound path `v` absent from `f`, has exactly one value of
//! `v` for every assignment of the remaining variables, so the summation may
//! substitute `v=f` without changing its coefficient. A subsequently unused
//! path contributes the exact factor `sum_v 1 = 2`.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_rational::BigRational;

use super::DensityCounterexample;
use super::kernel::{
    DensityKernel, KernelBooleanPolynomial, KernelMonomial, KernelPhasePolynomial, KernelScalar,
    KernelTerm, KernelVariable,
};

mod constraint_rows;
mod exact_affine_pivot;
mod exact_guard_pivot;
mod exact_smt;
mod exact_trig;
mod factored;
mod phase_basis;

// Borrowed projection onto the complete ordered free-variable sequence.
#[derive(Clone, Copy)]
struct FreeKey<'a>(&'a KernelMonomial);

impl<'a> FreeKey<'a> {
    fn variables(&self) -> impl Iterator<Item = &'a KernelVariable> {
        self.0.variables().filter(|v| !v.is_bound_path())
    }
}

impl PartialEq for FreeKey<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.cmp(other).is_eq()
    }
}
impl Eq for FreeKey<'_> {}
impl PartialOrd for FreeKey<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for FreeKey<'_> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.variables().cmp(other.variables())
    }
}

mod conditioning;
mod graph;
mod witness;

/// Exact squared modulus in the power basis of Q(zeta_(2^62)).
/// The empty vector is zero; all exponents are below 2^61.
pub(super) fn closed_trace_norm(c: &crate::symbolic::Component) -> Option<Vec<(u64, BigRational)>> {
    let (paths, constraints, coefficient, phase) = super::kernel::closed_scalar_parts(c)?;
    exact_smt::closed_norm(WorkingTerm {
        paths,
        constraints,
        coefficient,
        phase,
    })
}

pub(super) fn frontier_trace_norm(circuit: &crate::ir::Program) -> Option<Vec<(u64, BigRational)>> {
    exact_smt::frontier_norm(circuit)
}

pub(super) fn prefer_frontier_trace(circuit: &crate::ir::Program, paths: usize) -> bool {
    exact_smt::prefer_frontier(circuit, paths)
}

const MAX_BOOLEAN_TERMS: usize = 100_000;
const MAX_CONSTRAINTS: usize = 100_000;
const MAX_AFFINE_MATRIX_CELLS: usize = 10_000_000;
const MAX_PHASE_TERMS: usize = 100_000;
const MAX_SCALAR_NODES: usize = 100_000;
const MAX_AGGREGATE_ATOMS: usize = 100_000;
const MAX_SPLIT_DEPTH: usize = 8;
const MAX_RESIDUAL_SPLITS: usize = 255;
const MAX_RESIDUAL_ORDER_VISITS: usize = 4096;
const MAX_FACTOR_PRODUCTS: usize = 100_000;
const MAX_FACTOR_PHASE_CELLS: usize = 250_000;
const MAX_FREE_SPLIT_DEPTH: usize = 12;
const MAX_FREE_SPLITS: usize = 4095;
// Optional scheduling probes, shared across one local reduction's iterations.
const MAX_ALTERNATIVE_PIVOT_PROBES: usize = 32;
const MAX_DEFERRED_PHASE_PROBES: usize = 16;
const MAX_DEFERRED_PHASE_PATHS: usize = 64;
const MAX_DEFERRED_PHASE_TERMS: usize = 4096;
const MAX_SELECTOR_RECOVERY_ROWS: usize = 64;
const MAX_SELECTOR_RECOVERY_TERMS: usize = 4096;

/// A path-free density term in a sufficient exact normal form.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ExactTerm {
    constraints: Vec<KernelBooleanPolynomial>,
    coefficient: KernelScalar,
    phase: KernelPhasePolynomial,
}

/// One symbolic density-kernel entry after every bound path was eliminated.
///
/// Constraints remain part of the entry selector.  Treating differently
/// guarded contributions as equal without a canonical Boolean decision
/// procedure would be unsound, so this sufficient form combines only
/// structurally identical selectors and output indices.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct ExactEntry {
    constraints: Vec<KernelBooleanPolynomial>,
}

/// An exact formal complex coefficient.
///
/// The outer key denotes `exp(2*pi*i*phase)` and the value is its exact real
/// scalar coefficient.  Equal phase atoms are added coherently.  Keeping
/// distinct phase polynomials separate is incomplete but sound: this pass
/// never assumes two different roots of unity or symbolic phases are unequal.
type ExactCoefficient = BTreeMap<KernelPhasePolynomial, KernelScalar>;
type ExactAggregate = BTreeMap<ExactEntry, ExactCoefficient>;

enum Reduction {
    Exact(ExactTerm),
    Zero,
    /// A valid, bounded summand that local identities could not finish.
    Sum(Box<WorkingTerm>),
    /// Unsupported/resource refusal; must not be salvaged as a partial sum.
    Residual,
}

struct ReductionBudget {
    splits: usize,
    products: usize,
    phase_cells: usize,
}

/// Proves equality when both kernels reduce to the same exact formal sum.
///
/// Failure is deliberately inconclusive: distinct residual syntax can still
/// denote the same channel after Fourier elimination or coefficient summation.
#[cfg(test)]
fn exact_aggregate_match(left: &DensityKernel, right: &DensityKernel) -> bool {
    matches!(
        compare_kernels(left, right),
        AggregateComparison::Equivalent | AggregateComparison::SmtEquivalent(_)
    )
}

pub(crate) enum AggregateComparison {
    Equivalent,
    SmtEquivalent(crate::equivalence::smt::PortfolioResult),
    Different(
        Box<DensityCounterexample>,
        crate::equivalence::smt::PortfolioResult,
    ),
    Unknown,
}

pub(crate) fn compare_kernels(left: &DensityKernel, right: &DensityKernel) -> AggregateComparison {
    if left.input_pairs != right.input_pairs
        || left.quantum_output_count != right.quantum_output_count
        || left.classical_output_count != right.classical_output_count
    {
        return AggregateComparison::Unknown;
    }

    // A non-flat XAG is not an ANF expansion request. Keep the full graph for
    // graph-native elimination and exact SMT lowering instead.
    if left
        .terms
        .iter()
        .chain(&right.terms)
        .any(|t| !graph::is_algebraic(&working_term(t)))
    {
        return exact_smt::compare_raw(left, right);
    }

    let (reduced_left, reduced_right) =
        if let ([left_term], [right_term]) = (left.terms.as_slice(), right.terms.as_slice()) {
            // Reuse the same local reductions if the optional product certificate
            // refuses. Never repeat large local substitutions merely to probe it.
            let mut left_checkpoint = None;
            let mut right_checkpoint = None;
            let left = reduce_working_term_with_checkpoint(
                working_term(left_term),
                Some(&mut left_checkpoint),
            );
            let right = reduce_working_term_with_checkpoint(
                working_term(right_term),
                Some(&mut right_checkpoint),
            );
            if factored::matches(&left, &right) {
                return AggregateComparison::Equivalent;
            }
            if phase_basis::matches(&left, &right) {
                return AggregateComparison::Equivalent;
            }
            if phase_basis::matches_checkpoints(
                &left,
                &right,
                left_checkpoint.as_ref(),
                right_checkpoint.as_ref(),
            ) {
                return AggregateComparison::Equivalent;
            }
            (
                reduce_reductions(std::iter::once(left)),
                reduce_reductions(std::iter::once(right)),
            )
        } else {
            (reduce_kernel(left), reduce_kernel(right))
        };
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        for (side, reduced) in [("left", &reduced_left), ("right", &reduced_right)] {
            eprintln!(
                "aggregate {side} finished: {:?}",
                reduced
                    .as_ref()
                    .map(|map| (map.len(), map.values().map(BTreeMap::len).sum::<usize>()))
            );
        }
    }
    match (reduced_left, reduced_right) {
        (Some(reduced_left), Some(reduced_right)) => {
            if reduced_left == reduced_right {
                return AggregateComparison::Equivalent;
            }
            let mut budget = MAX_FREE_SPLITS;
            if tensor_aggregate_match(&reduced_left, &reduced_right, &mut budget) {
                return AggregateComparison::Equivalent;
            }
            let Some(difference) = aggregate_difference(reduced_left, reduced_right) else {
                return AggregateComparison::Unknown;
            };
            // The SMT query sees the COMPLETE selector-bearing difference,
            // never a selector/phase-erased sufficient EQ obligation.
            let smt_result = exact_smt::compare(&difference, left);
            if !matches!(smt_result, AggregateComparison::Unknown) {
                return smt_result;
            }
            if zero_by_free_splitting(difference, &mut budget, 0) {
                return AggregateComparison::Equivalent;
            }
            AggregateComparison::Unknown
        }
        _ => exact_smt::compare_raw(left, right),
    }
}

/// A sufficient product certificate for a single common selector. The
/// proposed ket/bra separation is checked by reconstructing the original
/// formal aggregate exactly, before either smaller equality is used.
fn tensor_aggregate_match(
    left: &ExactAggregate,
    right: &ExactAggregate,
    free_budget: &mut usize,
) -> bool {
    if !crate::ablation::permit(crate::ablation::Group::PathSumPlanning) {
        return false;
    }
    if left.len() != 1 || right.len() != 1 || left.keys().next() != right.keys().next() {
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!("aggregate tensor refused: selectors");
        }
        return false;
    }
    let mut budget = ReductionBudget {
        splits: 0,
        products: MAX_FACTOR_PRODUCTS,
        phase_cells: MAX_FACTOR_PHASE_CELLS,
    };
    let Some([left_ket, left_bra]) = factor_free_tensor(left, &mut budget) else {
        return false;
    };
    let Some([right_ket, right_bra]) = factor_free_tensor(right, &mut budget) else {
        return false;
    };
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!("aggregate tensor factors reconstructed on both sides");
    }
    for (left, right) in [(left_ket, right_ket), (left_bra, right_bra)] {
        if left == right {
            continue;
        }
        let Some(difference) = aggregate_difference(left, right) else {
            return false;
        };
        if !zero_by_free_splitting(difference, free_budget, 0) {
            return false;
        }
    }
    true
}

fn factor_free_tensor(
    source: &ExactAggregate,
    budget: &mut ReductionBudget,
) -> Option<[ExactAggregate; 2]> {
    if source.len() != 1 {
        return None;
    }
    // A common selector may identify a ket coordinate with a bra coordinate.
    // Such coordinates are shared parameters, not evidence of entanglement
    // between the remaining coordinate sets. Keep their exact dependence in
    // both factors and in the nonzero exponential used as a pivot.
    let shared = source
        .keys()
        .next()?
        .constraints
        .iter()
        .flat_map(KernelBooleanPolynomial::variables)
        .collect::<BTreeSet<_>>();
    let coefficients = source.values().next()?;
    // Cells are formal complex coefficients constant in the two private
    // coordinate sets, but may depend on shared selector parameters. No
    // phase independence is assumed.
    let mut cells: BTreeMap<(KernelPhasePolynomial, KernelPhasePolynomial), ExactCoefficient> =
        BTreeMap::new();
    let mut scanned = 0usize;
    for (phase, coefficient) in coefficients {
        if !matches!(coefficient, KernelScalar::Rational(_)) {
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!("aggregate tensor refused: non-rational scalar");
            }
            return None;
        }
        let mut ket = KernelPhasePolynomial::default();
        let mut bra = KernelPhasePolynomial::default();
        let mut constant = KernelPhasePolynomial::default();
        for (monomial, coefficient) in phase.terms() {
            let mut is_ket = false;
            let mut is_bra = false;
            for variable in monomial.variables() {
                scanned = scanned.checked_add(1)?;
                if scanned > MAX_FACTOR_PHASE_CELLS {
                    return None;
                }
                if shared.contains(variable) {
                    continue;
                }
                match variable {
                    KernelVariable::InputKet(_) | KernelVariable::QuantumOutputKet(_) => {
                        is_ket = true
                    }
                    KernelVariable::InputBra(_) | KernelVariable::QuantumOutputBra(_) => {
                        is_bra = true
                    }
                    _ => return None,
                }
            }
            let target = match (is_ket, is_bra) {
                (true, false) => &mut ket,
                (false, true) => &mut bra,
                (false, false) => &mut constant,
                (true, true) => {
                    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                        eprintln!("aggregate tensor refused: mixed monomial {monomial:?}");
                    }
                    return None;
                }
            };
            target.add_boolean(
                &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                coefficient.clone(),
            );
        }
        if cells
            .entry((ket, bra))
            .or_default()
            .insert(constant, coefficient.clone())
            .is_some()
        {
            return None;
        }
    }
    let ((pivot_ket, pivot_bra), pivot) = cells.iter().find(|(_, cell)| cell.len() == 1)?;
    let (pivot_phase, KernelScalar::Rational(pivot_scalar)) = pivot.first_key_value()? else {
        return None;
    };
    if *pivot_scalar == integer(0) {
        return None;
    }
    let mut ket_factor = ExactAggregate::new();
    let mut bra_factor = ExactAggregate::new();
    let mut ket_atoms = 0;
    let mut bra_atoms = 0;
    for ((ket, bra), cell) in &cells {
        for (constant, coefficient) in cell {
            if bra == pivot_bra {
                let mut phase = ket.clone();
                for (monomial, value) in constant.terms() {
                    phase.add_boolean(
                        &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                        value.clone(),
                    );
                }
                accumulate_exact_term(
                    ExactTerm {
                        constraints: Vec::new(),
                        coefficient: coefficient.clone(),
                        phase,
                    },
                    &mut ket_factor,
                    &mut ket_atoms,
                )?;
            }
            if ket == pivot_ket {
                let KernelScalar::Rational(value) = coefficient else {
                    return None;
                };
                let mut phase = bra.clone();
                for (monomial, value) in constant.terms() {
                    phase.add_boolean(
                        &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                        value.clone(),
                    );
                }
                for (monomial, value) in pivot_phase.terms() {
                    phase.add_boolean(
                        &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                        value.scaled(BigInt::from(-1)),
                    );
                }
                accumulate_exact_term(
                    ExactTerm {
                        constraints: Vec::new(),
                        coefficient: KernelScalar::Rational(value / pivot_scalar),
                        phase,
                    },
                    &mut bra_factor,
                    &mut bra_atoms,
                )?;
            }
        }
    }
    // This is the certificate gate: a false rank-one guess, missing cell,
    // sign, relative phase, or scale can never survive reconstruction.
    let reconstructed = multiply_aggregates(ket_factor.clone(), bra_factor.clone(), budget)?;
    let expected = BTreeMap::from([(
        ExactEntry {
            constraints: Vec::new(),
        },
        coefficients.clone(),
    )]);
    if reconstructed != expected {
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!("aggregate tensor refused: reconstruction");
        }
        return None;
    }
    Some([ket_factor, bra_factor])
}

fn aggregate_difference(mut left: ExactAggregate, right: ExactAggregate) -> Option<ExactAggregate> {
    let mut atoms = left.values().map(BTreeMap::len).sum();
    for (entry, coefficients) in right {
        for (phase, coefficient) in coefficients {
            accumulate_exact_term(
                ExactTerm {
                    constraints: entry.constraints.clone(),
                    phase,
                    coefficient: normalize_scalar(KernelScalar::Neg(Box::new(coefficient))),
                },
                &mut left,
                &mut atoms,
            )?;
        }
    }
    left.retain(|_, coefficients| !coefficients.is_empty());
    Some(left)
}

/// Proves that a difference is zero on *all* free input/output coordinates.
/// Unlike bound-path splitting, free branches are checked separately, never
/// added: both cofactors must be identically zero. Exact cancellation prunes
/// subtrees; exhausting either the depth or total work budget is inconclusive.
fn zero_by_free_splitting(difference: ExactAggregate, budget: &mut usize, depth: usize) -> bool {
    zero_by_free_splitting_with_algebra(
        difference,
        budget,
        &mut witness::ConstantBudget::default(),
        depth,
    )
}

fn zero_by_free_splitting_with_algebra(
    difference: ExactAggregate,
    budget: &mut usize,
    algebra: &mut witness::ConstantBudget,
    depth: usize,
) -> bool {
    // D = [G] F implies D=0 whenever F=0. Removing a selector common to
    // every term is a sufficient proof obligation, never an inequality rule.
    // In particular, variables used only by G need no free case split.
    let Some(difference) = forget_common_selector(difference) else {
        return false;
    };
    let Some(difference) = remove_common_phase(difference) else {
        return false;
    };
    if difference.is_empty() {
        return true;
    }
    if depth >= MAX_FREE_SPLIT_DEPTH || *budget == 0 {
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!("aggregate free-split refusal: depth={depth} budget={budget}");
            let phases = difference
                .values()
                .flat_map(BTreeMap::keys)
                .collect::<Vec<_>>();
            let variables = phases
                .iter()
                .flat_map(|phase| phase.variables())
                .collect::<BTreeSet<_>>();
            eprintln!(
                "aggregate refused phase support: atoms={} variables={variables:?}",
                phases.len()
            );
        }
        return false;
    }
    let mut variables = BTreeSet::new();
    for (entry, coefficients) in &difference {
        for equation in &entry.constraints {
            variables.extend(equation.variables());
        }
        for (phase, coefficient) in coefficients {
            variables.extend(phase.variables());
            if !scalar_conditions_within_budget(coefficient, |condition| {
                variables.extend(condition.variables());
                true
            }) {
                return false;
            }
        }
    }
    let Some(variable) = variables.into_iter().next() else {
        // A nonzero formal coefficient can still cancel exactly in the
        // supported cyclotomic field. Failure of this check is inconclusive.
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "aggregate constant residual: entries={} atoms={}",
                difference.len(),
                difference.values().map(BTreeMap::len).sum::<usize>()
            );
        }
        return witness::constant_is_zero(&difference, algebra);
    };
    if variable.is_bound_path() {
        return false;
    }
    *budget -= 1;
    for value in [false, true] {
        let Some(child) = restrict_aggregate(&difference, &variable, value) else {
            return false;
        };
        if !zero_by_free_splitting_with_algebra(child, budget, algebra, depth + 1) {
            return false;
        }
    }
    true
}

fn forget_common_selector(source: ExactAggregate) -> Option<ExactAggregate> {
    let Some(first) = source.keys().next() else {
        return Some(source);
    };
    if first.constraints.len().saturating_mul(source.len()) > MAX_AFFINE_MATRIX_CELLS {
        return Some(source);
    }
    let common = first
        .constraints
        .iter()
        .filter(|row| {
            source
                .keys()
                .all(|entry| entry.constraints.binary_search(row).is_ok())
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    if common.is_empty() {
        return Some(source);
    }
    let mut result = ExactAggregate::new();
    let mut atoms = 0;
    for (entry, coefficients) in source {
        let constraints = entry
            .constraints
            .into_iter()
            .filter(|row| !common.contains(row))
            .collect::<Vec<_>>();
        for (phase, coefficient) in coefficients {
            accumulate_exact_term(
                ExactTerm {
                    constraints: constraints.clone(),
                    coefficient,
                    phase,
                },
                &mut result,
                &mut atoms,
            )?;
        }
    }
    result.retain(|_, coefficients| !coefficients.is_empty());
    Some(result)
}

/// D = exp(2*pi*i*P) F is zero whenever F is zero, including when P
/// depends on free coordinates. Remove only monomials with the same exact
/// coefficient in every atom. This cannot expand a phase polynomial and
/// avoids splitting coordinates used solely by the common phase factor.
fn remove_common_phase(source: ExactAggregate) -> Option<ExactAggregate> {
    let Some(first) = source.values().flat_map(BTreeMap::keys).next() else {
        return Some(source);
    };
    let atom_count: usize = source.values().map(BTreeMap::len).sum();
    if first.term_count().saturating_mul(atom_count) > MAX_AFFINE_MATRIX_CELLS {
        return Some(source);
    }
    let common = first
        .terms()
        .filter(|(monomial, coefficient)| {
            source
                .values()
                .flat_map(BTreeMap::keys)
                .all(|phase| phase.coefficient(monomial) == **coefficient)
        })
        .map(|(monomial, coefficient)| (monomial.clone(), coefficient.scaled(BigInt::from(-1))))
        .collect::<Vec<_>>();
    if common.is_empty() {
        return Some(source);
    }
    let mut result = ExactAggregate::new();
    let mut atoms = 0;
    for (entry, coefficients) in source {
        for (mut phase, coefficient) in coefficients {
            for (monomial, negative) in &common {
                phase.add_boolean(
                    &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                    negative.clone(),
                );
            }
            accumulate_exact_term(
                ExactTerm {
                    constraints: entry.constraints.clone(),
                    coefficient,
                    phase,
                },
                &mut result,
                &mut atoms,
            )?;
        }
    }
    result.retain(|_, coefficients| !coefficients.is_empty());
    Some(result)
}

fn restrict_aggregate(
    source: &ExactAggregate,
    variable: &KernelVariable,
    value: bool,
) -> Option<ExactAggregate> {
    let replacement = KernelBooleanPolynomial::from(value);
    let mut result = ExactAggregate::new();
    let mut atoms = 0;
    for (entry, coefficients) in source {
        let mut constraints = entry
            .constraints
            .iter()
            .map(|row| row.substitute(variable, &replacement))
            .collect::<Vec<_>>();
        if constraints.iter().any(KernelBooleanPolynomial::is_one) {
            continue;
        }
        constraints.retain(|row| !row.is_zero());
        constraints.sort();
        constraints.dedup();
        for (phase, coefficient) in coefficients {
            let mut phase = phase.clone();
            phase.substitute(variable, &replacement);
            let coefficient = normalize_scalar(coefficient.substitute(variable, &replacement));
            accumulate_exact_term(
                ExactTerm {
                    constraints: constraints.clone(),
                    coefficient,
                    phase,
                },
                &mut result,
                &mut atoms,
            )?;
        }
    }
    result.retain(|_, coefficients| !coefficients.is_empty());
    Some(result)
}

/// Reduces and coherently combines every component-pair contribution.
///
/// A resource refusal or unexpanded residual aborts the entire certificate. Returning a partially
/// accumulated map would make resource or rule order observable in the proof
/// result.  Zero terms and exact coefficient cancellations are removed only
/// after exact normalization.
fn reduce_kernel(kernel: &DensityKernel) -> Option<ExactAggregate> {
    reduce_reductions(kernel.terms.iter().map(reduce_term))
}

fn reduce_reductions(reductions: impl Iterator<Item = Reduction>) -> Option<ExactAggregate> {
    let mut aggregate = ExactAggregate::new();
    let mut atoms = 0usize;
    let mut budget = ReductionBudget {
        splits: MAX_RESIDUAL_SPLITS,
        products: MAX_FACTOR_PRODUCTS,
        phase_cells: MAX_FACTOR_PHASE_CELLS,
    };
    for reduction in reductions {
        accumulate_reduction(reduction, &mut aggregate, &mut atoms, &mut budget, 0)?;
    }
    aggregate.retain(|_, coefficient| !coefficient.is_empty());
    Some(aggregate)
}

/// Exact Shannon splitting of a *bound* Boolean sum. No averaging factor is
/// introduced: sum_v F(v) = F(0) + F(1). Each child again uses local exact
/// identities before another split. A shared kernel-wide budget and depth
/// bound prevent an unbounded enumeration fallback; any refusal discards the
/// complete aggregate, including already visited siblings.
fn accumulate_reduction(
    reduction: Reduction,
    aggregate: &mut ExactAggregate,
    atoms: &mut usize,
    budget: &mut ReductionBudget,
    depth: usize,
) -> Option<()> {
    accumulate_reduction_with_depth(reduction, aggregate, atoms, budget, depth, MAX_SPLIT_DEPTH)
}

fn accumulate_reduction_with_depth(
    reduction: Reduction,
    aggregate: &mut ExactAggregate,
    atoms: &mut usize,
    budget: &mut ReductionBudget,
    depth: usize,
    depth_limit: usize,
) -> Option<()> {
    let exact = match reduction {
        Reduction::Zero => return Some(()),
        Reduction::Residual => return None,
        Reduction::Sum(term) => {
            if let Some(factors) = factor_phase_sums(&term) {
                let mut product = ExactAggregate::new();
                let mut product_atoms = 0;
                accumulate_exact_term(
                    ExactTerm {
                        constraints: Vec::new(),
                        coefficient: KernelScalar::Rational(integer(1)),
                        phase: KernelPhasePolynomial::default(),
                    },
                    &mut product,
                    &mut product_atoms,
                )?;
                for factor in factors {
                    let mut factor_sum = ExactAggregate::new();
                    let mut factor_atoms = 0;
                    accumulate_reduction_with_depth(
                        reduce_working_term(factor),
                        &mut factor_sum,
                        &mut factor_atoms,
                        budget,
                        0,
                        depth_limit,
                    )?;
                    product = multiply_aggregates(product, factor_sum, budget)?;
                }
                for (entry, coefficients) in product {
                    for (phase, coefficient) in coefficients {
                        accumulate_exact_term(
                            ExactTerm {
                                constraints: entry.constraints.clone(),
                                coefficient,
                                phase,
                            },
                            aggregate,
                            atoms,
                        )?;
                    }
                }
                return Some(());
            }
            if depth >= depth_limit || budget.splits == 0 {
                return None;
            }
            budget.splits -= 1;
            let variable = term.residual_split_variable()?;
            for value in [false, true] {
                let mut child = (*term).clone();
                let replacement = KernelBooleanPolynomial::from(value);
                if !child.substitution_within_budget(&variable, &replacement) {
                    return None;
                }
                child.substitute(&variable, &replacement);
                child.paths.remove(&variable);
                accumulate_reduction_with_depth(
                    reduce_working_term(child),
                    aggregate,
                    atoms,
                    budget,
                    depth + 1,
                    depth_limit,
                )?;
            }
            return Some(());
        }
        Reduction::Exact(term) => term,
    };
    accumulate_exact_term(exact, aggregate, atoms)
}

/// Factor separated bound sums. The real scalar must contain no bound path;
/// each whole guard equation connects all of its bound dependencies. Shared
/// *free* coordinates do not connect factors:
/// for each fixed u, sum_(a,b) C(u) exp(i(P(a,u)+Q(b,u))) is the product of
/// the two sums times C(u). Every phase monomial connects all of its bound
/// variables, so a mixed term can never be accidentally split between them.
fn factor_phase_sums(term: &WorkingTerm) -> Option<Vec<WorkingTerm>> {
    factor_phase_sums_with_guard_cells(term, 32768)
}

// The optional compactor supplies its separately preflighted scan/copy bound.
// Ordinary aggregation and factor proofs retain their original entrance.
fn factor_phase_sums_with_guard_cells(
    term: &WorkingTerm,
    guard_phase_cells: usize,
) -> Option<Vec<WorkingTerm>> {
    if !crate::ablation::permit(crate::ablation::Group::PathSumPlanning) {
        return None;
    }
    if term.paths.len() < 2 || term.paths.len() > MAX_BOOLEAN_TERMS {
        return None;
    }
    let path_free = |polynomial: &KernelBooleanPolynomial| {
        polynomial
            .variables()
            .iter()
            .all(|variable| !term.paths.contains(variable))
    };
    if !scalar_conditions_within_budget(&term.coefficient, path_free) {
        return None;
    }
    // Guard-aware decomposition is optional and restricted by the actual
    // combined guard/phase syntax scanned and copied, not phase term count
    // alone. The previous phase-only admission remains unchanged.
    if !term.constraints.iter().all(path_free)
        && (term.paths.len() > 256
            || term.constraints.len() > 64
            || term
                .constraints
                .iter()
                .map(KernelBooleanPolynomial::variables)
                .chain(term.phase.selectors().map(|(p, _)| p.variables()))
                .try_fold(0usize, |cells, variables| {
                    cells
                        .checked_add(1 + variables.len())
                        .filter(|n| *n <= guard_phase_cells)
                })
                .is_none())
    {
        return None;
    }
    let positions = term
        .paths
        .iter()
        .enumerate()
        .map(|(index, variable)| (variable.clone(), index))
        .collect::<BTreeMap<_, _>>();
    let mut parents = (0..positions.len()).collect::<Vec<_>>();
    fn root(parents: &mut [usize], mut index: usize) -> usize {
        while parents[index] != index {
            parents[index] = parents[parents[index]];
            index = parents[index];
        }
        index
    }
    let mut occurrences = 0usize;
    for (selector, _) in term.phase.selectors() {
        let mut first = None;
        for variable in &selector.variables() {
            occurrences = occurrences.checked_add(1)?;
            if occurrences > MAX_AFFINE_MATRIX_CELLS {
                return None;
            }
            let Some(&position) = positions.get(variable) else {
                continue;
            };
            let current = root(&mut parents, position);
            if let Some(previous) = first {
                let previous = root(&mut parents, previous);
                parents[current] = previous;
            } else {
                first = Some(current);
            }
        }
    }
    for equation in &term.constraints {
        let mut first = None;
        // An XOR equation is ONE indicator, not a product of indicators for
        // its monomials. All bound variables in the entire row must connect.
        for variable in &equation.variables() {
            occurrences = occurrences.checked_add(1)?;
            if occurrences > MAX_AFFINE_MATRIX_CELLS {
                return None;
            }
            let Some(&position) = positions.get(variable) else {
                continue;
            };
            let current = root(&mut parents, position);
            if let Some(previous) = first {
                let previous = root(&mut parents, previous);
                parents[current] = previous;
            } else {
                first = Some(current);
            }
        }
    }
    let mut groups = BTreeMap::new();
    for (variable, &position) in &positions {
        groups
            .entry(root(&mut parents, position))
            .or_insert_with(BTreeSet::new)
            .insert(variable.clone());
    }
    if groups.len() < 2 {
        return None;
    }
    let mut factors = groups
        .into_iter()
        .map(|(id, paths)| {
            (
                id,
                WorkingTerm {
                    constraints: Vec::new(),
                    paths,
                    coefficient: KernelScalar::Rational(integer(1)),
                    phase: KernelPhasePolynomial::default(),
                },
            )
        })
        .collect::<BTreeMap<_, _>>();
    let mut common = WorkingTerm {
        constraints: Vec::new(),
        paths: BTreeSet::new(),
        coefficient: term.coefficient.clone(),
        phase: KernelPhasePolynomial::default(),
    };
    for equation in &term.constraints {
        let owner = equation
            .variables()
            .into_iter()
            .find_map(|variable| positions.get(&variable))
            .map(|&position| root(&mut parents, position));
        match owner {
            Some(owner) => factors.get_mut(&owner)?.constraints.push(equation.clone()),
            None => common.constraints.push(equation.clone()),
        }
    }
    for (selector, coefficient) in term.phase.selectors() {
        let owner = selector
            .variables()
            .into_iter()
            .find_map(|variable| positions.get(&variable))
            .map(|&position| root(&mut parents, position));
        let destination = match owner {
            Some(owner) => &mut factors.get_mut(&owner)?.phase,
            None => &mut common.phase,
        };
        destination.add_boolean(&selector, coefficient.clone());
    }
    Some(
        std::iter::once(common)
            .chain(factors.into_values())
            .collect(),
    )
}

/// Exact convolution, with a shared kernel-wide bound on all atom pairs
/// visited (including pairs that later cancel). Failure discards the entire
/// product; neither a partial factor nor a partially accumulated kernel is a
/// certificate. Constraint conjunction, scalar multiplication and phase
/// addition are all retained in each product entry.
fn multiply_aggregates(
    left: ExactAggregate,
    right: ExactAggregate,
    budget: &mut ReductionBudget,
) -> Option<ExactAggregate> {
    let left_atoms: usize = left.values().map(BTreeMap::len).sum();
    let right_atoms: usize = right.values().map(BTreeMap::len).sum();
    // Atom count alone does not bound the large monomial sets copied by
    // convolution. Charge an upper bound on all copied phase terms and
    // variable occurrences before constructing any product phase.
    fn phase_cells(aggregate: &ExactAggregate) -> Option<usize> {
        aggregate
            .values()
            .flat_map(BTreeMap::keys)
            .try_fold(0usize, |total, phase| {
                phase.terms().try_fold(total, |total, (monomial, _)| {
                    total
                        .checked_add(1)?
                        .checked_add(monomial.variables().count())
                })
            })
    }
    let cells = phase_cells(&left)?
        .checked_mul(right_atoms)?
        .checked_add(phase_cells(&right)?.checked_mul(left_atoms)?)?;
    budget.phase_cells = budget.phase_cells.checked_sub(cells)?;
    budget.products = budget
        .products
        .checked_sub(left_atoms.checked_mul(right_atoms)?)?;
    let mut result = ExactAggregate::new();
    let mut atoms = 0;
    for (left_entry, left_coefficients) in &left {
        for (right_entry, right_coefficients) in &right {
            if left_entry
                .constraints
                .len()
                .saturating_add(right_entry.constraints.len())
                > MAX_CONSTRAINTS
            {
                return None;
            }
            let constraints = left_entry
                .constraints
                .iter()
                .chain(&right_entry.constraints)
                .cloned()
                .collect::<Vec<_>>();
            for (left_phase, left_coefficient) in left_coefficients {
                for (right_phase, right_coefficient) in right_coefficients {
                    if left_phase
                        .term_count()
                        .saturating_add(right_phase.term_count())
                        > MAX_PHASE_TERMS
                    {
                        return None;
                    }
                    let coefficient = KernelScalar::Mul(
                        Box::new(left_coefficient.clone()),
                        Box::new(right_coefficient.clone()),
                    );
                    if !scalar_within_budget(&coefficient) {
                        return None;
                    }
                    let mut phase = left_phase.clone();
                    for (monomial, coefficient) in right_phase.terms() {
                        phase.add_boolean(
                            &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                            coefficient.clone(),
                        );
                    }
                    let product = reduce_working_term(WorkingTerm {
                        constraints: constraints.clone(),
                        paths: BTreeSet::new(),
                        coefficient: normalize_scalar(coefficient),
                        phase,
                    });
                    match product {
                        Reduction::Zero => {}
                        Reduction::Exact(exact) => {
                            accumulate_exact_term(exact, &mut result, &mut atoms)?
                        }
                        _ => return None,
                    }
                }
            }
        }
    }
    result.retain(|_, coefficients| !coefficients.is_empty());
    Some(result)
}

fn accumulate_exact_term(
    mut exact: ExactTerm,
    aggregate: &mut ExactAggregate,
    atoms: &mut usize,
) -> Option<()> {
    // exp(2*pi*i*(p+1/2)) = -exp(2*pi*i*p). This is an exact
    // coefficient identity, not a claim that different phase atoms differ.
    if exact
        .phase
        .coefficient(&KernelMonomial::one())
        .rational_part()
        >= ratio(1, 2)
    {
        exact.phase.add_boolean(
            &KernelBooleanPolynomial::one(),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
        exact.coefficient = normalize_scalar(KernelScalar::Neg(Box::new(exact.coefficient)));
    }
    let ExactTerm {
        constraints,
        coefficient,
        phase,
    } = exact;
    if coefficient.is_zero() {
        return Some(());
    }
    let coefficient_map = aggregate.entry(ExactEntry { constraints }).or_default();
    let had_atom = coefficient_map.contains_key(&phase);
    let combined = coefficient_map
        .remove(&phase)
        .map_or(coefficient.clone(), |current| {
            normalize_scalar(KernelScalar::Add(Box::new(current), Box::new(coefficient)))
        });
    if !scalar_within_budget(&combined) {
        return None;
    }
    if !combined.is_zero() {
        if !had_atom {
            *atoms = atoms.checked_add(1)?;
            if *atoms > MAX_AGGREGATE_ATOMS {
                return None;
            }
        }
        coefficient_map.insert(phase, combined);
    } else if had_atom {
        *atoms = atoms.saturating_sub(1);
    }
    Some(())
}

fn reduce_term(term: &KernelTerm) -> Reduction {
    reduce_working_term(working_term(term))
}

fn working_term(term: &KernelTerm) -> WorkingTerm {
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
        let index = KernelBooleanPolynomial::variable(KernelVariable::ClassicalOutput(position));
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
        coefficient: normalize_scalar(term.weight.product()),
        phase: KernelPhasePolynomial::difference(&term.phase.ket, &term.phase.bra),
    }
}

fn reduce_working_term(term: WorkingTerm) -> Reduction {
    reduce_working_term_with_checkpoint(term, None)
}

fn reduce_working_term_with_checkpoint(
    mut term: WorkingTerm,
    checkpoint: Option<&mut Option<WorkingTerm>>,
) -> Reduction {
    if !graph::is_algebraic(&term) {
        return graph::reduce(term);
    }
    if term.phase.term_count() > MAX_PHASE_TERMS && term.initial_alias_compaction_within_budget() {
        // Literal renaming cannot grow any Boolean/phase polynomial. This
        // bounded entrance may compact an oversized initial alias encoding,
        // but the original representation check remains mandatory afterward.
        term.eliminate_literal_aliases();
        debug_term("initial-alias-compaction", &term);
    }
    if !term.within_budget() {
        debug_term("initial-representation-budget", &term);
        return Reduction::Residual;
    }
    term.eliminate_literal_aliases();
    match term.normalize_constraints() {
        ConstraintNormalization::Normalized => {}
        ConstraintNormalization::Contradiction => return Reduction::Zero,
        ConstraintNormalization::BudgetExceeded => {
            // normalize_constraints is transactional: its matrix work uses
            // local rows and commits only on success. Keep the original
            // bounded conjunction and use direct exact pivots instead.
            debug_term("initial-affine-budget-sparse-fallback", &term);
            match term.clean_constraints() {
                ConstraintNormalization::Normalized => {}
                ConstraintNormalization::Contradiction => return Reduction::Zero,
                ConstraintNormalization::BudgetExceeded => return Reduction::Residual,
            }
        }
    }
    term.eliminate_literal_aliases();
    if term.phase.term_count() >= 256 {
        term.phase.index_occurrences();
    }
    debug_term("initial", &term);

    let mut span_recovery_available = true;
    let mut selector_recovery_available = true;
    let mut alternative_pivot_probes = MAX_ALTERNATIVE_PIVOT_PROBES;
    let mut deferred_phase_probes = MAX_DEFERRED_PHASE_PROBES;
    let mut exact_pivot_cells = exact_affine_pivot::WORK_CELLS;
    loop {
        let mut local_budget_refused = false;
        if let Some((mut variable, mut replacement)) = term.best_constraint_pivot() {
            let substitution_fits = term.substitution_within_budget(&variable, &replacement);
            if !substitution_fits || (span_recovery_available && replacement.term_count() > 64) {
                // A definition v=F and an observed output o=F can expose
                // v=o by exact ANF row operations, avoiding expansion of
                // F into the phase or another large definition. There is
                // one proactive probe, but a later unsafe substitution may
                // probe again: exact pivots can have shrunk the matrix since
                // an earlier refusal. Commit only a changed normal form, so
                // repeatedly probing the same span cannot cause a loop.
                span_recovery_available = false;
                // Probe transactionally: a refused optional normalization
                // must not discard an otherwise budget-safe substitution or
                // expose a partially row-reduced constraint collection.
                let mut normalized = term.constraints.clone();
                match normalize_constraint_span(&mut normalized) {
                    ConstraintNormalization::Normalized if normalized != term.constraints => {
                        term.constraints = normalized;
                        term.eliminate_literal_aliases();
                        continue;
                    }
                    ConstraintNormalization::Normalized => {}
                    ConstraintNormalization::Contradiction => return Reduction::Zero,
                    ConstraintNormalization::BudgetExceeded => {}
                }
            }
            if !substitution_fits {
                if exact_affine_pivot::apply(
                    &mut term,
                    &variable,
                    &replacement,
                    &mut exact_pivot_cells,
                ) {
                    debug_term("exact-affine-phase-pivot", &term);
                    match term.clean_constraints() {
                        ConstraintNormalization::Normalized => continue,
                        ConstraintNormalization::Contradiction => return Reduction::Zero,
                        ConstraintNormalization::BudgetExceeded => return Reduction::Residual,
                    }
                }
                if let Some(alternative) =
                    term.budget_safe_constraint_pivot(&mut alternative_pivot_probes)
                {
                    (variable, replacement) = alternative;
                    debug_term("alternative-pivot", &term);
                } else if exact_guard_pivot::apply(
                    &mut term,
                    &variable,
                    &replacement,
                    &mut exact_pivot_cells,
                ) {
                    // Preserve cheap safe pivots first; they may shrink the
                    // complete source/RHS before the shared diagram attempt.
                    debug_term("exact-guard-pivot", &term);
                    match term.clean_constraints() {
                        ConstraintNormalization::Normalized => continue,
                        ConstraintNormalization::Contradiction => return Reduction::Zero,
                        ConstraintNormalization::BudgetExceeded => return Reduction::Residual,
                    }
                } else {
                    debug_term("substitution-budget-postponed", &term);
                    local_budget_refused = true;
                }
            }
            if !local_budget_refused {
                term.substitute(&variable, &replacement);
                term.paths.remove(&variable);
                if !term.within_budget() {
                    debug_term("representation-budget", &term);
                    return Reduction::Residual;
                }
                match term.clean_constraints() {
                    ConstraintNormalization::Normalized => {}
                    ConstraintNormalization::Contradiction => return Reduction::Zero,
                    ConstraintNormalization::BudgetExceeded => return Reduction::Residual,
                }
                continue;
            }
        }

        let mut reduced = false;
        for variable in term.paths.iter().cloned().collect::<Vec<_>>() {
            if local_budget_refused {
                // An earlier unbounded phase-first prototype regressed real
                // cases. Recovery is optional and only scans a small residual,
                // with a shared probe limit across all local iterations.
                if deferred_phase_probes == 0
                    || term.paths.len() > MAX_DEFERRED_PHASE_PATHS
                    || term.phase.term_count() > MAX_DEFERRED_PHASE_TERMS
                    || term
                        .constraints
                        .iter()
                        .try_fold(0usize, |total, row| {
                            total
                                .checked_add(row.term_count())
                                .filter(|size| *size <= MAX_DEFERRED_PHASE_TERMS)
                        })
                        .is_none()
                {
                    break;
                }
                deferred_phase_probes -= 1;
            }
            if term.occurs_outside_phase(&variable) {
                continue;
            }
            match phase_profile(&term.phase, &variable) {
                PhaseProfile::Absent => {
                    term.remove_summed_path(&variable, KernelScalar::Rational(integer(2)));
                }
                PhaseProfile::Fourier(relation) => {
                    term.phase
                        .substitute(&variable, &KernelBooleanPolynomial::zero());
                    term.constraints.push(relation);
                    term.remove_summed_path(&variable, KernelScalar::Rational(integer(2)));
                }
                PhaseProfile::Omega { parity, positive } => {
                    let (constant, coefficient) = if positive {
                        (ratio(1, 8), ratio(-1, 4))
                    } else {
                        (ratio(-1, 8), ratio(1, 4))
                    };
                    let constant_polynomial = KernelBooleanPolynomial::one();
                    let constant_coefficient =
                        crate::symbolic::PhaseCoefficient::rational(constant);
                    let parity_coefficient =
                        crate::symbolic::PhaseCoefficient::rational(coefficient);
                    if !term.phase_rewrite_within_budget(
                        &variable,
                        [
                            (&constant_polynomial, &constant_coefficient),
                            (&parity, &parity_coefficient),
                        ],
                    ) {
                        debug_term("omega-lift-budget-postponed", &term);
                        local_budget_refused = true;
                        continue;
                    }
                    term.phase
                        .substitute(&variable, &KernelBooleanPolynomial::zero());
                    term.phase
                        .add_boolean(&constant_polynomial, constant_coefficient);
                    term.phase.add_boolean(&parity, parity_coefficient);
                    term.remove_summed_path(
                        &variable,
                        KernelScalar::Sqrt(Box::new(KernelScalar::Rational(integer(2)))),
                    );
                }
                PhaseProfile::Unsupported => continue,
            }
            if !term.within_budget() {
                debug_term("path-rule-budget", &term);
                return Reduction::Residual;
            }
            match term.clean_constraints() {
                ConstraintNormalization::Normalized => {}
                // In particular, sum_v (-1)^v creates the exact Fourier
                // constraint 1 = 0 and therefore annihilates this term.
                ConstraintNormalization::Contradiction => return Reduction::Zero,
                ConstraintNormalization::BudgetExceeded => {
                    debug_term("path-rule-budget", &term);
                    return Reduction::Residual;
                }
            }
            reduced = true;
            break;
        }
        if !reduced {
            if span_recovery_available
                && term.constraints.iter().any(|equation| {
                    equation
                        .terms()
                        .flat_map(KernelMonomial::variables)
                        .any(|variable| term.paths.contains(variable))
                })
            {
                span_recovery_available = false;
                let mut normalized = term.constraints.clone();
                match normalize_constraint_span(&mut normalized) {
                    ConstraintNormalization::Normalized if normalized != term.constraints => {
                        term.constraints = normalized;
                        continue;
                    }
                    ConstraintNormalization::Contradiction => return Reduction::Zero,
                    _ => {}
                }
            }
            // Free-coordinate equalities may cancel a bound-dependent phase
            // before the paths can be summed. Retain their defining deltas;
            // this is simplification on the selector, never summing a free
            // coordinate. The optional probe is transactional and runs once.
            if selector_recovery_available && !term.paths.is_empty() {
                selector_recovery_available = false;
                if term.constraints.len() <= MAX_SELECTOR_RECOVERY_ROWS
                    && term.phase.term_count() <= MAX_SELECTOR_RECOVERY_TERMS
                    && term
                        .constraints
                        .iter()
                        .try_fold(0usize, |total, row| {
                            total
                                .checked_add(row.term_count())
                                .filter(|size| *size <= MAX_SELECTOR_RECOVERY_TERMS)
                        })
                        .is_some()
                {
                    let mut normalized = term.clone();
                    match normalized.normalize_selector() {
                        ConstraintNormalization::Contradiction => return Reduction::Zero,
                        ConstraintNormalization::Normalized
                            if normalized.constraints != term.constraints
                                || normalized.coefficient != term.coefficient
                                || normalized.phase != term.phase =>
                        {
                            term = normalized;
                            debug_term("bound-selector-recovery", &term);
                            continue;
                        }
                        _ => {}
                    }
                }
            }
            if local_budget_refused {
                // Every committed local step is complete. No refused pivot,
                // partial matrix, or prefix aggregate has changed this term.
                // Move (do not clone) this exact bounded checkpoint for the
                // optional EQ-only route; the ordinary result stays Residual.
                if let Some(checkpoint) = checkpoint
                    && phase_basis::checkpoint_admitted(&term)
                {
                    debug_term("whole-term-checkpoint", &term);
                    *checkpoint = Some(term);
                }
                return Reduction::Residual;
            }
            break;
        }
    }

    if !term.paths.is_empty() {
        debug_term("residual", &term);
        return Reduction::Sum(Box::new(term));
    }
    match term.normalize_selector() {
        ConstraintNormalization::Normalized => {}
        ConstraintNormalization::Contradiction => return Reduction::Zero,
        ConstraintNormalization::BudgetExceeded => return Reduction::Residual,
    }
    debug_term("exact", &term);
    Reduction::Exact(ExactTerm {
        constraints: term.constraints,
        coefficient: normalize_scalar(term.coefficient),
        phase: term.phase,
    })
}

fn debug_term(stage: &str, term: &WorkingTerm) {
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate {stage}: paths={} constraints={} phase_terms={}",
            term.paths.len(),
            term.constraints.len(),
            term.phase.term_count(),
        );
    }
}

#[derive(Clone)]
struct WorkingTerm {
    constraints: Vec<KernelBooleanPolynomial>,
    paths: BTreeSet<KernelVariable>,
    coefficient: KernelScalar,
    phase: KernelPhasePolynomial,
}

enum ConstraintNormalization {
    Normalized,
    Contradiction,
    BudgetExceeded,
}

/// Canonicalizes the GF(2) linear span of complete ANF equations.
///
/// Monomials are formal columns, not independent Boolean inputs. An elementary
/// XOR row operation preserves simultaneous zero evaluation at *every* actual
/// input assignment: `f=0 && g=0` iff `f=0 && (f xor g)=0`. Thus equal row
/// spaces certify equal selectors even for nonlinear equations. This does not
/// compute the Boolean ideal: multiplying equations by variables can yield
/// equivalent selectors with different spans, which remain inconclusive.
///
/// Run once after bound-path elimination; the inner reducer keeps its cheaper
/// affine normal form. Preflight bounds packed matrix storage; decoded rows
/// must also fit the sparse output budget. Both forms use bitgauss RREF.
fn normalize_constraint_span(
    constraints: &mut Vec<KernelBooleanPolynomial>,
) -> ConstraintNormalization {
    match constraint_rows::reduce(&constraints.iter().collect::<Vec<_>>()) {
        Ok(normalized) => {
            *constraints = normalized;
            ConstraintNormalization::Normalized
        }
        Err(status) => status,
    }
}

impl WorkingTerm {
    fn initial_alias_compaction_within_budget(&self) -> bool {
        if self.paths.len() > 100_000
            || self.constraints.len() > MAX_CONSTRAINTS
            || self.phase.term_count() > 200_000
            || !scalar_within_budget(&self.coefficient)
        {
            return false;
        }
        let mut cells = 750_000usize;
        let Some(remaining) = cells.checked_sub(self.paths.len() + self.constraints.len()) else {
            return false;
        };
        cells = remaining;
        let mut inspect = |monomial: &KernelMonomial| {
            for _ in std::iter::once(()).chain(monomial.variables().map(|_| ())) {
                let Some(remaining) = cells.checked_sub(1) else {
                    return false;
                };
                cells = remaining;
            }
            true
        };
        self.constraints
            .iter()
            .all(|row| row.term_count() <= MAX_BOOLEAN_TERMS && row.terms().all(&mut inspect))
            && self.phase.terms().all(|(monomial, _)| inspect(monomial))
            && scalar_conditions_within_budget(&self.coefficient, |row| {
                row.terms().all(&mut inspect)
            })
    }

    /// A selector/weight dependency prevents phase-only factorization. Split
    /// such a binder first, rather than spending the entire Shannon depth on
    /// independent phase factors. This is scheduling only: both assignments
    /// still contribute, with the original shared budgets and full summand.
    fn residual_split_variable(&self) -> Option<KernelVariable> {
        if !crate::ablation::permit(crate::ablation::Group::PathSumPlanning) {
            return self.paths.first().cloned();
        }
        let mut visits = 0usize;
        let mut selected = None;
        let mut inspect = |polynomial: &KernelBooleanPolynomial| {
            for variable in polynomial.terms().flat_map(KernelMonomial::variables) {
                visits += 1;
                if visits > MAX_RESIDUAL_ORDER_VISITS {
                    return false;
                }
                if self.paths.contains(variable) {
                    selected = Some(variable.clone());
                    return false;
                }
            }
            true
        };
        if self.constraints.iter().all(&mut inspect) {
            scalar_conditions_within_budget(&self.coefficient, &mut inspect);
        }
        selected.or_else(|| self.paths.first().cloned())
    }

    /// Eliminate a forest of equations v=w in one traversal of the summand.
    /// Only locally bound roots can be removed. Each removed Boolean binder
    /// has exactly one extension, so this introduces no factor of two.
    /// Distinct free roots are NEVER identified: their equality remains a
    /// selector after renaming every original equation, including forest edges.
    fn eliminate_literal_aliases(&mut self) {
        fn root(
            parents: &mut BTreeMap<KernelVariable, KernelVariable>,
            variable: &KernelVariable,
        ) -> KernelVariable {
            let mut current = variable.clone();
            let mut visited = Vec::new();
            while let Some(parent) = parents.get(&current) {
                visited.push(current.clone());
                current = parent.clone();
            }
            for variable in visited {
                parents.insert(variable, current.clone());
            }
            current
        }

        let mut parents = BTreeMap::new();
        for equation in &self.constraints {
            if equation.term_count() != 2 {
                continue;
            }
            let mut variables = equation.terms().filter_map(|monomial| {
                let mut variables = monomial.variables();
                let first = variables.next()?;
                variables.next().is_none().then_some(first)
            });
            let (Some(left), Some(right)) = (variables.next(), variables.next()) else {
                continue;
            };
            let left = root(&mut parents, left);
            let right = root(&mut parents, right);
            if left == right {
                continue;
            }
            let left_bound = self.paths.contains(&left);
            let right_bound = self.paths.contains(&right);
            let (removed, kept) = match (left_bound, right_bound) {
                (false, false) => continue,
                (true, false) => (left, right),
                (false, true) => (right, left),
                (true, true) if left < right => (right, left),
                (true, true) => (left, right),
            };
            parents.insert(removed, kept);
        }
        if parents.is_empty() {
            return;
        }
        // Resolve every chain before applying a simultaneous substitution.
        for variable in parents.keys().cloned().collect::<Vec<_>>() {
            root(&mut parents, &variable);
        }
        for equation in &mut self.constraints {
            *equation = equation.rename_variables(&parents);
        }
        self.constraints.retain(|equation| !equation.is_zero());
        self.phase.rename_variables(&parents);
        self.coefficient = self.coefficient.rename_variables(&parents);
        self.paths
            .retain(|variable| !parents.contains_key(variable));
    }

    /// Substitution preserves the conjunction without Gaussian elimination.
    /// During path reduction, remove only constant/duplicate equations; defer
    /// rebuilding the matrix to the final selector normalizer. Recomputing
    /// RREF after each of hundreds of path pivots dominated large OWM cases.
    /// Every bound variable occurring in an affine row remains a directly
    /// available pivot even when the rows are not in echelon form.
    fn clean_constraints(&mut self) -> ConstraintNormalization {
        if self.constraints.iter().any(KernelBooleanPolynomial::is_one) {
            return ConstraintNormalization::Contradiction;
        }
        self.constraints.retain(|row| !row.is_zero());
        self.constraints.sort();
        self.constraints.dedup();
        ConstraintNormalization::Normalized
    }

    /// Simplifies the summand under known triangular equalities, retaining each
    /// defining equation because its variables are free kernel coordinates.
    /// Under `[v xor f=0]`, replacing v by f in every *other* constraint,
    /// coefficient and phase is exact. It is not summation over v.
    ///
    /// Choose only the least variable in a row, occurring as a singleton and
    /// nowhere else: its replacement uses strictly greater variables. This
    /// includes nonlinear definitions, e.g. `x = y*z`, but not `x = x*y`.
    /// Substitution may expose new eligible rows, so repeat to a fixed point. A
    /// work limit is an inconclusive result, not a partially reduced proof.
    fn normalize_selector(&mut self) -> ConstraintNormalization {
        const MAX_ROUNDS: usize = 64;
        for _ in 0..MAX_ROUNDS {
            match normalize_constraint_span(&mut self.constraints) {
                ConstraintNormalization::Normalized => {}
                result => return result,
            }
            let before = self.constraints.clone();
            for index in 0..before.len() {
                // Earlier substitutions can change a later definition. Use
                // the current equation, not a stale snapshot of its RHS.
                let equation = self.constraints[index].clone();
                let Some(variable) = equation.variables().into_iter().next() else {
                    continue;
                };
                let atom = KernelMonomial::variable(variable.clone());
                if !equation.has_term(&atom)
                    || equation
                        .terms()
                        .any(|term| term != &atom && term.contains(&variable))
                {
                    continue;
                }
                let replacement =
                    equation.xor(&KernelBooleanPolynomial::variable(variable.clone()));
                if !self.substitution_within_budget(&variable, &replacement) {
                    return ConstraintNormalization::BudgetExceeded;
                }
                for (other, row) in self.constraints.iter_mut().enumerate() {
                    if other != index && row.terms().any(|term| term.contains(&variable)) {
                        *row = row.substitute(&variable, &replacement);
                    }
                }
                self.coefficient =
                    normalize_scalar(self.coefficient.substitute(&variable, &replacement));
                self.phase.substitute(&variable, &replacement);
                if !self.within_budget() {
                    return ConstraintNormalization::BudgetExceeded;
                }
            }
            if self.constraints == before {
                return ConstraintNormalization::Normalized;
            }
        }
        ConstraintNormalization::BudgetExceeded
    }

    /// Canonicalizes the affine equations by exact GF(2) RREF.
    ///
    /// Nonlinear equations are deliberately only sorted and deduplicated.
    /// Their complete ANF row span is canonicalized once at the end, without
    /// claiming completeness for their Boolean ideal.
    fn normalize_constraints(&mut self) -> ConstraintNormalization {
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
    fn best_constraint_pivot(&self) -> Option<(KernelVariable, KernelBooleanPolynomial)> {
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

    /// A bounded, read-only alternative search; every proposal uses the same
    /// exact pivot condition and full substitution preflight as the fast path.
    fn budget_safe_constraint_pivot(
        &self,
        probes: &mut usize,
    ) -> Option<(KernelVariable, KernelBooleanPolynomial)> {
        let mut candidates = self.constraint_pivots();
        while *probes > 0 {
            let (variable, equation) = candidates.next()?;
            *probes -= 1;
            let replacement = equation.xor(&KernelBooleanPolynomial::variable(variable.clone()));
            if self.substitution_within_budget(variable, &replacement) {
                return Some((variable.clone(), replacement));
            }
        }
        None
    }

    fn constraint_pivots(
        &self,
    ) -> impl Iterator<Item = (&KernelVariable, &KernelBooleanPolynomial)> {
        self.constraints.iter().flat_map(move |equation| {
            // Only a singleton monomial can be a pivot. Visiting those
            // directly avoids the old equations x all-paths Cartesian
            // scan; construct the replacement only for the winner.
            equation.terms().filter_map(move |atom| {
                let mut variables = atom.variables();
                let variable = variables.next()?;
                if variables.next().is_some()
                    || !self.paths.contains(variable)
                    || equation
                        .terms()
                        .any(|term| term != atom && term.contains(variable))
                {
                    return None;
                }
                Some((variable, equation))
            })
        })
    }

    fn substitution_within_budget(
        &self,
        variable: &KernelVariable,
        replacement: &KernelBooleanPolynomial,
    ) -> bool {
        // Check indexed phase growth first: oversized parity lifts can be
        // rejected without repeatedly scanning every unrelated constraint.
        // These are read-only conjuncts of the same preflight predicate.
        let replacement_terms = replacement.term_count();
        let mut projected_terms = self.phase.term_count() - self.phase.occurrence_count(variable);
        for (_, coefficient) in self.phase.terms_containing(variable) {
            let Some(lifted_terms) = lifted_boolean_term_bound(replacement_terms, coefficient)
            else {
                return false;
            };
            let Some(projected) = projected_terms.checked_add(lifted_terms) else {
                return false;
            };
            projected_terms = projected;
            if projected_terms > MAX_PHASE_TERMS {
                return false;
            }
        }
        self.constraints
            .iter()
            .all(|value| boolean_substitution_within_budget(value, variable, replacement))
            && scalar_substitution_within_budget(&self.coefficient, variable, replacement)
    }

    fn substitute(&mut self, variable: &KernelVariable, replacement: &KernelBooleanPolynomial) {
        for equation in &mut self.constraints {
            if equation.variables().contains(variable) {
                *equation = equation.substitute(variable, replacement);
            }
        }
        self.coefficient = self.coefficient.substitute(variable, replacement);
        self.phase.substitute(variable, replacement);
    }

    /// Checks the largest phase representation that a local rewrite can
    /// create before changing the working term.
    ///
    /// Zeroing `variable` removes every phase monomial that contains it. Each
    /// subsequent Boolean lift is bounded independently; collisions with the
    /// surviving phase can only reduce the resulting map size. Besides
    /// bounding the final phase, this bounds the temporary map constructed by
    /// `KernelPhasePolynomial::add_boolean`.
    fn phase_rewrite_within_budget<'a>(
        &self,
        variable: &KernelVariable,
        additions: impl IntoIterator<
            Item = (
                &'a KernelBooleanPolynomial,
                &'a crate::symbolic::PhaseCoefficient,
            ),
        >,
    ) -> bool {
        let mut projected_terms = self.phase.term_count() - self.phase.occurrence_count(variable);
        for (polynomial, coefficient) in additions {
            let Some(lifted_terms) =
                lifted_boolean_term_bound(polynomial.term_count(), coefficient)
            else {
                return false;
            };
            let Some(projected) = projected_terms.checked_add(lifted_terms) else {
                return false;
            };
            projected_terms = projected;
            if projected_terms > MAX_PHASE_TERMS {
                return false;
            }
        }
        true
    }

    fn occurs_outside_phase(&self, variable: &KernelVariable) -> bool {
        self.constraints
            .iter()
            .any(|value| value.variables().contains(variable))
            || self
                .coefficient
                .substitute(variable, &KernelBooleanPolynomial::zero())
                != self
                    .coefficient
                    .substitute(variable, &KernelBooleanPolynomial::one())
    }

    fn remove_summed_path(&mut self, variable: &KernelVariable, factor: KernelScalar) {
        self.paths.remove(variable);
        self.coefficient = normalize_scalar(factor.multiply(self.coefficient.clone()));
    }

    fn within_budget(&self) -> bool {
        self.constraints.len() <= MAX_CONSTRAINTS
            && self
                .constraints
                .iter()
                .all(|value| value.term_count() <= MAX_BOOLEAN_TERMS)
            && self.phase.term_count() <= MAX_PHASE_TERMS
            && scalar_within_budget(&self.coefficient)
    }
}

/// Bounds one direct ANF substitution without constructing its products.
///
/// A monomial without `variable` contributes at most one output term. A
/// monomial containing it contributes at most one copy of every replacement
/// term after multiplication by the remaining variables. XOR collisions can
/// only decrease that count.
fn boolean_substitution_within_budget(
    polynomial: &KernelBooleanPolynomial,
    variable: &KernelVariable,
    replacement: &KernelBooleanPolynomial,
) -> bool {
    if polynomial.term_count() > MAX_BOOLEAN_TERMS || replacement.term_count() > MAX_BOOLEAN_TERMS {
        return false;
    }

    let replacement_terms = replacement.term_count();
    // A read-only sufficient bound: every old monomial contributes at most
    // max(1, replacement_terms) terms, regardless of whether it contains v.
    // For the usual small constraints, avoid visiting all their monomials on
    // every pivot. If this loose bound fails, retain the exact old preflight.
    if polynomial
        .term_count()
        .checked_mul(replacement_terms.max(1))
        .is_some_and(|bound| bound <= MAX_BOOLEAN_TERMS)
    {
        return true;
    }
    let mut projected_terms = 0usize;
    for monomial in polynomial.terms() {
        let contribution = if monomial.contains(variable) {
            replacement_terms
        } else {
            1
        };
        let Some(projected) = projected_terms.checked_add(contribution) else {
            return false;
        };
        projected_terms = projected;
        if projected_terms > MAX_BOOLEAN_TERMS {
            return false;
        }
    }
    true
}

/// Bounds scalar cloning and every Boolean condition rewritten inside it.
/// Scalar substitution never duplicates an arithmetic node: an undecided
/// select retains both branches and a decided select drops one. The Boolean
/// conditions are the only scalar children whose ANF can expand.
fn scalar_substitution_within_budget(
    scalar: &KernelScalar,
    variable: &KernelVariable,
    replacement: &KernelBooleanPolynomial,
) -> bool {
    scalar_conditions_within_budget(scalar, |condition| {
        boolean_substitution_within_budget(condition, variable, replacement)
    })
}

fn scalar_within_budget(scalar: &KernelScalar) -> bool {
    scalar_conditions_within_budget(scalar, |condition| {
        condition.term_count() <= MAX_BOOLEAN_TERMS
    })
}

fn scalar_conditions_within_budget(
    scalar: &KernelScalar,
    mut condition_fits: impl FnMut(&KernelBooleanPolynomial) -> bool,
) -> bool {
    let mut pending = vec![scalar];
    let mut nodes = 0usize;
    while let Some(current) = pending.pop() {
        let Some(next_nodes) = nodes.checked_add(1) else {
            return false;
        };
        nodes = next_nodes;
        if nodes > MAX_SCALAR_NODES {
            return false;
        }
        match current {
            KernelScalar::Rational(_) | KernelScalar::Sin(_) | KernelScalar::Cos(_) => {}
            KernelScalar::Sqrt(value) | KernelScalar::Neg(value) | KernelScalar::Inverse(value) => {
                pending.push(value)
            }
            KernelScalar::Add(left, right) | KernelScalar::Mul(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => {
                if !condition_fits(condition) {
                    return false;
                }
                pending.push(when_true);
                pending.push(when_false);
            }
        }
    }
    true
}

/// Upper-bounds the number of nonzero arithmetic monomials created by lifting
/// an ANF XOR into a phase. For a rational coefficient with denominator
/// `2^e`, products above degree `e` have integral coefficients and disappear
/// modulo one. Other exact coefficients use the full `2^n - 1` bound.
fn lifted_boolean_term_bound(
    boolean_terms: usize,
    coefficient: &crate::symbolic::PhaseCoefficient,
) -> Option<usize> {
    if boolean_terms == 0 {
        return Some(0);
    }
    let maximum_degree = coefficient.as_rational().map_or(boolean_terms, |value| {
        let mut denominator = value.denom().clone();
        let two = BigInt::from(2);
        let mut exponent = 0usize;
        while &denominator % &two == BigInt::from(0) {
            denominator /= &two;
            exponent += 1;
        }
        if denominator == BigInt::from(1) {
            exponent.min(boolean_terms)
        } else {
            boolean_terms
        }
    });

    let mut total = 0usize;
    let mut binomial = 1usize;
    for degree in 1..=maximum_degree {
        binomial = binomial.checked_mul(boolean_terms + 1 - degree)? / degree;
        total = total.checked_add(binomial)?;
        if total > MAX_PHASE_TERMS {
            return None;
        }
    }
    Some(total)
}

enum PhaseProfile {
    Absent,
    Fourier(KernelBooleanPolynomial),
    Omega {
        parity: KernelBooleanPolynomial,
        positive: bool,
    },
    Unsupported,
}

/// Classifies `phase = phase_without_v + v * coefficient` for exact local sums.
fn phase_profile(phase: &KernelPhasePolynomial, variable: &KernelVariable) -> PhaseProfile {
    let mut present = false;
    let mut constant = integer(0);
    let mut parity_terms = Vec::new();
    for (monomial, coefficient) in phase.terms_containing(variable) {
        present = true;
        let Some(coefficient) = coefficient.as_rational() else {
            return PhaseProfile::Unsupported;
        };
        let reduced = monomial.without(variable);
        if reduced == KernelMonomial::one() {
            constant = coefficient;
        } else if coefficient == ratio(1, 2) {
            parity_terms.push(reduced);
        } else {
            return PhaseProfile::Unsupported;
        }
    }
    let parity = KernelBooleanPolynomial::from_monomials(parity_terms);
    if !present {
        PhaseProfile::Absent
    } else if constant == integer(0) {
        PhaseProfile::Fourier(parity)
    } else if constant == ratio(1, 2) {
        PhaseProfile::Fourier(parity.complement())
    } else if constant == ratio(1, 4) {
        PhaseProfile::Omega {
            parity,
            positive: true,
        }
    } else if constant == ratio(3, 4) {
        PhaseProfile::Omega {
            parity,
            positive: false,
        }
    } else {
        PhaseProfile::Unsupported
    }
}

/// Canonicalizes the exact scalar products produced by density doubling.
fn normalize_scalar(value: KernelScalar) -> KernelScalar {
    match value {
        KernelScalar::Sin(angle) => {
            exact_trig::normalize(&angle, true).unwrap_or(KernelScalar::Sin(angle))
        }
        KernelScalar::Cos(angle) => {
            exact_trig::normalize(&angle, false).unwrap_or(KernelScalar::Cos(angle))
        }
        KernelScalar::Mul(left, right) => {
            normalize_product(vec![normalize_scalar(*left), normalize_scalar(*right)])
        }
        KernelScalar::Add(left, right) => {
            normalize_sum(vec![normalize_scalar(*left), normalize_scalar(*right)])
        }
        KernelScalar::Sqrt(value) => normalize_sqrt(normalize_scalar(*value)),
        KernelScalar::Neg(value) => normalize_product(vec![
            KernelScalar::Rational(integer(-1)),
            normalize_scalar(*value),
        ]),
        KernelScalar::Inverse(value) => match normalize_scalar(*value) {
            KernelScalar::Rational(value) if value != BigRational::from_integer(0.into()) => {
                KernelScalar::Rational(value.recip())
            }
            KernelScalar::Sqrt(value) => match value.as_ref() {
                KernelScalar::Rational(value) if value > &integer(0) => {
                    normalize_sqrt(KernelScalar::Rational(value.recip()))
                }
                _ => KernelScalar::Inverse(Box::new(KernelScalar::Sqrt(value))),
            },
            value => KernelScalar::Inverse(Box::new(value)),
        },
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => {
            let when_true = normalize_scalar(*when_true);
            let when_false = normalize_scalar(*when_false);
            if condition.is_zero() {
                when_false
            } else if condition.is_one() || when_true == when_false {
                when_true
            } else {
                KernelScalar::Select {
                    condition,
                    when_true: Box::new(when_true),
                    when_false: Box::new(when_false),
                }
            }
        }
        value => value,
    }
}

/// Flattens a real product, combines its exact rational magnitude, and uses
/// only radical identities whose non-negativity side condition is proved.
fn normalize_product(values: Vec<KernelScalar>) -> KernelScalar {
    let mut pending = values;
    let mut rational = integer(1);
    let mut rational_radicand = integer(1);
    let mut has_rational_radical = false;
    let mut factors = Vec::new();

    while let Some(value) = pending.pop() {
        match value {
            KernelScalar::Mul(left, right) => {
                pending.push(*left);
                pending.push(*right);
            }
            KernelScalar::Rational(value) => rational *= value,
            KernelScalar::Sqrt(value) => match value.as_ref() {
                KernelScalar::Rational(value) if value >= &integer(0) => {
                    has_rational_radical = true;
                    rational_radicand *= value;
                }
                _ => factors.push(KernelScalar::Sqrt(value)),
            },
            value => factors.push(value),
        }
    }
    if rational == integer(0) {
        return KernelScalar::Rational(integer(0));
    }

    // sqrt(r)^2 = r is used only when r is known non-negative. This also
    // handles roots of density weights such as sums of syntactic squares.
    factors.sort();
    let mut paired = Vec::with_capacity(factors.len());
    let mut position = 0;
    while position < factors.len() {
        let end = factors[position..]
            .iter()
            .position(|value| value != &factors[position])
            .map_or(factors.len(), |offset| position + offset);
        let count = end - position;
        if let KernelScalar::Sqrt(root) = &factors[position]
            && scalar_is_provably_nonnegative(root)
        {
            for _ in 0..count / 2 {
                paired.push((**root).clone());
            }
            if count % 2 == 1 {
                paired.push(factors[position].clone());
            }
        } else {
            paired.extend(factors[position..end].iter().cloned());
        }
        position = end;
    }
    factors = paired;

    if has_rational_radical {
        // For real rational a and non-negative r,
        // a*sqrt(r) = sign(a)*sqrt(a^2*r). Absorbing the magnitude makes
        // 2*sqrt(1/8) and sqrt(1/2) share one exact representation.
        let negative = rational < integer(0);
        let radicand = rational.clone() * rational * rational_radicand;
        let root = normalize_sqrt(KernelScalar::Rational(radicand));
        rational = if negative { integer(-1) } else { integer(1) };
        match root {
            KernelScalar::Rational(value) => rational *= value,
            value => factors.push(value),
        }
    }

    // Roots collapsed above can expose products. Flatten once more; unlike a
    // distributive rewrite, this cannot increase the number of scalar atoms.
    let mut flattened = Vec::new();
    while let Some(value) = factors.pop() {
        match value {
            KernelScalar::Mul(left, right) => {
                factors.push(*left);
                factors.push(*right);
            }
            KernelScalar::Rational(value) => rational *= value,
            value => flattened.push(value),
        }
    }
    if rational == integer(0) {
        return KernelScalar::Rational(integer(0));
    }
    flattened.sort();
    if rational != integer(1) || flattened.is_empty() {
        flattened.insert(0, KernelScalar::Rational(rational));
    }
    make_product(flattened)
}

/// Collects coefficients of identical exact scalar atoms without distributing
/// products. This proves cancellations such as `a + (-a) = 0` but leaves
/// algebraically different symbolic/trigonometric expressions distinct.
fn normalize_sum(values: Vec<KernelScalar>) -> KernelScalar {
    let mut pending = values;
    let mut coefficients: BTreeMap<Option<KernelScalar>, BigRational> = BTreeMap::new();
    while let Some(value) = pending.pop() {
        match value {
            KernelScalar::Add(left, right) => {
                pending.push(*left);
                pending.push(*right);
            }
            value => {
                let (coefficient, base) = split_scalar_coefficient(value);
                *coefficients.entry(base).or_insert_with(|| integer(0)) += coefficient;
            }
        }
    }

    let mut terms = Vec::new();
    for (base, coefficient) in coefficients {
        if coefficient == integer(0) {
            continue;
        }
        terms.push(match base {
            None => KernelScalar::Rational(coefficient),
            Some(base) => normalize_product(vec![KernelScalar::Rational(coefficient), base]),
        });
    }
    match terms.len() {
        0 => KernelScalar::Rational(integer(0)),
        1 => terms.pop().expect("one scalar term exists"),
        _ => {
            terms.sort();
            make_sum(terms)
        }
    }
}

fn split_scalar_coefficient(value: KernelScalar) -> (BigRational, Option<KernelScalar>) {
    match value {
        KernelScalar::Rational(value) => (value, None),
        value => {
            let mut factors = Vec::new();
            collect_product(value, &mut factors);
            factors.sort();
            let coefficient = if let Some(KernelScalar::Rational(_)) = factors.first() {
                match factors.remove(0) {
                    KernelScalar::Rational(value) => value,
                    _ => unreachable!("the first factor was matched as rational"),
                }
            } else {
                integer(1)
            };
            (coefficient, Some(make_product(factors)))
        }
    }
}

fn collect_product(value: KernelScalar, factors: &mut Vec<KernelScalar>) {
    match value {
        KernelScalar::Mul(left, right) => {
            collect_product(*left, factors);
            collect_product(*right, factors);
        }
        value => factors.push(value),
    }
}

fn make_product(mut factors: Vec<KernelScalar>) -> KernelScalar {
    debug_assert!(!factors.is_empty());
    let first = factors.remove(0);
    factors.into_iter().fold(first, |left, right| {
        KernelScalar::Mul(Box::new(left), Box::new(right))
    })
}

fn make_sum(mut terms: Vec<KernelScalar>) -> KernelScalar {
    debug_assert!(!terms.is_empty());
    let first = terms.remove(0);
    terms.into_iter().fold(first, |left, right| {
        KernelScalar::Add(Box::new(left), Box::new(right))
    })
}

fn normalize_sqrt(value: KernelScalar) -> KernelScalar {
    match value {
        KernelScalar::Rational(value) if value == integer(0) => KernelScalar::Rational(integer(0)),
        KernelScalar::Rational(value) if value == integer(1) => KernelScalar::Rational(integer(1)),
        KernelScalar::Rational(value) if value > integer(0) => {
            let numerator = value.numer().sqrt();
            let denominator = value.denom().sqrt();
            if &numerator * &numerator == *value.numer()
                && &denominator * &denominator == *value.denom()
            {
                KernelScalar::Rational(BigRational::new(numerator, denominator))
            } else {
                KernelScalar::Sqrt(Box::new(KernelScalar::Rational(value)))
            }
        }
        value => KernelScalar::Sqrt(Box::new(value)),
    }
}

fn scalar_is_provably_nonnegative(value: &KernelScalar) -> bool {
    match value {
        KernelScalar::Rational(value) => value >= &integer(0),
        KernelScalar::Sqrt(_) => true,
        KernelScalar::Add(left, right) => {
            scalar_is_provably_nonnegative(left) && scalar_is_provably_nonnegative(right)
        }
        KernelScalar::Mul(left, right) if left == right => true,
        KernelScalar::Mul(left, right) => {
            scalar_is_provably_nonnegative(left) && scalar_is_provably_nonnegative(right)
        }
        KernelScalar::Select {
            when_true,
            when_false,
            ..
        } => {
            scalar_is_provably_nonnegative(when_true) && scalar_is_provably_nonnegative(when_false)
        }
        KernelScalar::Sin(_)
        | KernelScalar::Cos(_)
        | KernelScalar::Neg(_)
        | KernelScalar::Inverse(_) => false,
    }
}

fn integer(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn ratio(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

#[cfg(test)]
mod tests {
    use super::super::kernel::KernelClassicalOutput;
    use super::*;

    fn kernel(terms: Vec<KernelTerm>) -> DensityKernel {
        DensityKernel {
            input_pairs: Vec::new(),
            quantum_output_count: 0,
            classical_output_count: 0,
            terms,
        }
    }

    fn term(coefficient: i64) -> KernelTerm {
        KernelTerm {
            ket_guard: Vec::new(),
            bra_guard: Vec::new(),
            history_equalities: Vec::new(),
            ket_paths: BTreeSet::new(),
            bra_paths: BTreeSet::new(),
            quantum_outputs_ket: Vec::new(),
            quantum_outputs_bra: Vec::new(),
            classical_outputs: Vec::new(),
            weight: super::super::kernel::KernelWeight {
                ket: rational(coefficient),
                bra: rational(1),
            },
            phase: super::super::kernel::KernelPhaseDifference {
                ket: KernelPhasePolynomial::default(),
                bra: KernelPhasePolynomial::default(),
            },
        }
    }

    fn rational(value: i64) -> KernelScalar {
        KernelScalar::Rational(integer(value))
    }

    fn sqrt_ratio(numerator: i64, denominator: i64) -> KernelScalar {
        KernelScalar::Sqrt(Box::new(KernelScalar::Rational(ratio(
            numerator,
            denominator,
        ))))
    }

    fn add(left: KernelScalar, right: KernelScalar) -> KernelScalar {
        KernelScalar::Add(Box::new(left), Box::new(right))
    }

    fn multiply(left: KernelScalar, right: KernelScalar) -> KernelScalar {
        KernelScalar::Mul(Box::new(left), Box::new(right))
    }

    fn variable(variable: KernelVariable) -> KernelBooleanPolynomial {
        KernelBooleanPolynomial::variable(variable)
    }

    fn affine(variables: impl IntoIterator<Item = KernelVariable>) -> KernelBooleanPolynomial {
        variables
            .into_iter()
            .fold(KernelBooleanPolynomial::zero(), |value, variable| {
                value.xor(&KernelBooleanPolynomial::variable(variable))
            })
    }

    #[test]
    fn scalar_product_normal_form_is_associative_and_commutative() {
        let a = sqrt_ratio(2, 1);
        let b = KernelScalar::Inverse(Box::new(sqrt_ratio(3, 1)));
        let left = multiply(multiply(rational(-2), a.clone()), b.clone());
        let reordered = multiply(b, multiply(a, rational(-2)));

        assert_eq!(normalize_scalar(left), normalize_scalar(reordered));
    }

    #[test]
    fn sparse_kernel_substitutions_match_distributive_reference() {
        let variables = [
            KernelVariable::InputKet(0),
            KernelVariable::PathBra { term: 0, path: 0 },
        ];
        let x = variable(variables[0].clone());
        let y = variable(variables[1].clone());
        let atoms = [
            KernelBooleanPolynomial::one(),
            x.clone(),
            y.clone(),
            x.and(&y),
        ];
        let polynomial = |bits: usize| {
            atoms
                .iter()
                .enumerate()
                .fold(KernelBooleanPolynomial::zero(), |sum, (i, m)| {
                    if bits & (1 << i) == 0 {
                        sum
                    } else {
                        sum.xor(m)
                    }
                })
        };
        for bits in 0..16 {
            let source = polynomial(bits);
            for replacement_bits in 0..16 {
                let replacement = polynomial(replacement_bits);
                for v in &variables {
                    let expand = |monomial: &KernelMonomial| {
                        monomial.variables().fold(
                            KernelBooleanPolynomial::one(),
                            |product, current| {
                                product.and(&if current == v {
                                    replacement.clone()
                                } else {
                                    variable(current.clone())
                                })
                            },
                        )
                    };
                    let reference = source
                        .terms()
                        .fold(KernelBooleanPolynomial::zero(), |sum, monomial| {
                            sum.xor(&expand(monomial))
                        });
                    assert_eq!(source.substitute(v, &replacement), reference);
                    let mut phase = KernelPhasePolynomial::default();
                    for (i, monomial) in source.terms().enumerate() {
                        phase.add_boolean(
                            &KernelBooleanPolynomial::from_monomial(monomial.clone()),
                            crate::symbolic::PhaseCoefficient::rational(ratio(1, [8, 3, 4, 7][i])),
                        );
                    }
                    let mut reference = KernelPhasePolynomial::default();
                    for (monomial, coefficient) in phase.terms() {
                        reference.add_boolean(&expand(monomial), coefficient.clone());
                    }
                    phase.substitute(v, &replacement);
                    assert_eq!(phase, reference);
                }
            }
        }
    }

    #[test]
    fn scalar_sum_normal_form_is_associative_commutative_and_cancels() {
        let atom = KernelScalar::Inverse(Box::new(sqrt_ratio(2, 1)));
        let left = add(
            add(atom.clone(), rational(3)),
            KernelScalar::Neg(Box::new(atom.clone())),
        );
        let reordered = add(
            rational(3),
            add(KernelScalar::Neg(Box::new(atom.clone())), atom),
        );

        assert_eq!(normalize_scalar(left), rational(3));
        assert_eq!(normalize_scalar(reordered), rational(3));
    }

    #[test]
    fn scalar_rational_radicals_are_combined_exactly() {
        assert_eq!(
            normalize_scalar(multiply(sqrt_ratio(2, 1), sqrt_ratio(8, 1))),
            rational(4)
        );

        // This is the nested density-weight shape that occurs in
        // sqbricks-owm-vs-tele-0002: 2 * sqrt(1/2) / sqrt(2) = 1.
        let nested = multiply(
            rational(2),
            multiply(
                sqrt_ratio(1, 2),
                KernelScalar::Inverse(Box::new(sqrt_ratio(2, 1))),
            ),
        );
        assert_eq!(normalize_scalar(nested), rational(1));
    }

    #[test]
    fn scalar_does_not_cancel_an_unproved_inverse() {
        let atom = KernelScalar::Select {
            condition: KernelBooleanPolynomial::variable(KernelVariable::InputKet(0)),
            when_true: Box::new(rational(0)),
            when_false: Box::new(rational(1)),
        };
        let value = multiply(atom.clone(), KernelScalar::Inverse(Box::new(atom)));

        assert!(!matches!(
            normalize_scalar(value),
            KernelScalar::Rational(value) if value == integer(1)
        ));
    }

    #[test]
    fn scalar_select_reduces_only_decided_or_equal_branches() {
        let condition = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
        let equal = KernelScalar::Select {
            condition: condition.clone(),
            when_true: Box::new(rational(7)),
            when_false: Box::new(rational(7)),
        };
        let false_condition = KernelScalar::Select {
            condition: KernelBooleanPolynomial::zero(),
            when_true: Box::new(rational(7)),
            when_false: Box::new(rational(9)),
        };
        let unresolved = KernelScalar::Select {
            condition,
            when_true: Box::new(rational(7)),
            when_false: Box::new(rational(9)),
        };

        assert_eq!(normalize_scalar(equal), rational(7));
        assert_eq!(normalize_scalar(false_condition), rational(9));
        assert!(matches!(
            normalize_scalar(unresolved),
            KernelScalar::Select { .. }
        ));
    }

    #[test]
    fn multi_term_coefficients_are_added_coherently() {
        let left = kernel(vec![term(1), term(2)]);
        let right = kernel(vec![term(3)]);

        assert!(exact_aggregate_match(&left, &right));
    }

    #[test]
    fn multi_term_coefficients_cancel_exactly() {
        let left = kernel(vec![term(1), term(-1)]);
        let right = kernel(Vec::new());

        assert!(exact_aggregate_match(&left, &right));
    }

    #[test]
    fn path_dependent_outputs_are_alpha_renamed_by_free_index_reification() {
        fn with_paths(owner: usize, ket_path: usize, bra_path: usize) -> DensityKernel {
            let mut value = term(1);
            let ket = KernelVariable::PathKet {
                term: owner,
                path: ket_path,
            };
            let bra = KernelVariable::PathBra {
                term: owner,
                path: bra_path,
            };
            value.ket_paths.insert(ket.clone());
            value.bra_paths.insert(bra.clone());
            value.quantum_outputs_ket = vec![variable(ket)];
            value.quantum_outputs_bra = vec![variable(bra)];
            DensityKernel {
                input_pairs: Vec::new(),
                quantum_output_count: 1,
                classical_output_count: 0,
                terms: vec![value],
            }
        }

        assert!(exact_aggregate_match(
            &with_paths(0, 0, 1),
            &with_paths(91, 17, 23)
        ));
    }

    #[test]
    fn free_indices_are_never_accepted_as_bound_paths() {
        let mut malformed = term(1);
        malformed
            .ket_paths
            .insert(KernelVariable::QuantumOutputKet(0));

        assert!(exact_aggregate_match(
            &kernel(vec![malformed.clone()]),
            &kernel(vec![term(1)])
        ));
        assert!(!exact_aggregate_match(
            &kernel(vec![malformed]),
            &kernel(vec![term(2)])
        ));
    }

    #[test]
    fn quantum_ket_and_bra_output_indices_remain_distinct() {
        let ket_input = variable(KernelVariable::InputKet(0));
        let bra_input = variable(KernelVariable::InputBra(0));
        let mut direct = term(1);
        direct.quantum_outputs_ket = vec![ket_input.clone()];
        direct.quantum_outputs_bra = vec![bra_input.clone()];
        let mut swapped = term(1);
        swapped.quantum_outputs_ket = vec![bra_input];
        swapped.quantum_outputs_bra = vec![ket_input];

        let mut left = kernel(vec![direct]);
        left.quantum_output_count = 1;
        let mut right = kernel(vec![swapped]);
        right.quantum_output_count = 1;
        assert!(!exact_aggregate_match(&left, &right));
    }

    #[test]
    fn one_shared_classical_index_enforces_both_dephasing_deltas() {
        let ket = variable(KernelVariable::InputKet(0));
        let bra = variable(KernelVariable::InputBra(0));
        let mut dephased = term(1);
        dephased.classical_outputs = vec![KernelClassicalOutput {
            ket: ket.clone(),
            bra,
        }];
        let mut diagonal_only = term(1);
        diagonal_only.classical_outputs = vec![KernelClassicalOutput {
            ket: ket.clone(),
            bra: ket,
        }];

        let mut left = kernel(vec![dephased]);
        left.classical_output_count = 1;
        let mut right = kernel(vec![diagonal_only]);
        right.classical_output_count = 1;
        assert!(!exact_aggregate_match(&left, &right));

        let aggregate = reduce_kernel(&left).expect("the affine deltas reduce exactly");
        let variables = aggregate
            .keys()
            .flat_map(|entry| &entry.constraints)
            .flat_map(KernelBooleanPolynomial::variables)
            .collect::<BTreeSet<_>>();
        assert!(variables.contains(&KernelVariable::ClassicalOutput(0)));
        assert!(!variables.contains(&KernelVariable::QuantumOutputKet(0)));
        assert!(!variables.contains(&KernelVariable::QuantumOutputBra(0)));
    }

    #[test]
    fn dependent_affine_constraint_bases_have_one_exact_rref() {
        let a = KernelVariable::InputKet(0);
        let b = KernelVariable::InputKet(1);
        let c = KernelVariable::InputKet(2);
        let mut left = term(1);
        left.ket_guard = vec![
            affine([a.clone(), b.clone()]),
            affine([b.clone(), c.clone()]),
        ];
        let mut right = term(1);
        right.ket_guard = vec![affine([a, c.clone()]), affine([b, c])];

        assert!(exact_aggregate_match(
            &kernel(vec![left]),
            &kernel(vec![right])
        ));
    }

    #[test]
    fn nonlinear_constraint_row_operations_preserve_the_selector() {
        let x = variable(KernelVariable::InputKet(0));
        let y = variable(KernelVariable::InputKet(1));
        let z = variable(KernelVariable::InputKet(2));
        let xy = x.and(&y);
        let xz = x.and(&z);
        let mut original = term(1);
        original.ket_guard = vec![xy.clone(), xz.clone()];
        let mut changed_basis = term(1);
        changed_basis.ket_guard = vec![xy.xor(&xz), xz];

        assert!(exact_aggregate_match(
            &kernel(vec![original]),
            &kernel(vec![changed_basis])
        ));
    }

    #[test]
    fn constraint_span_is_sufficient_not_a_complete_boolean_ideal() {
        let x = variable(KernelVariable::InputKet(0));
        let y = variable(KernelVariable::InputKet(1));
        let mut left = term(1);
        left.ket_guard = vec![x.clone()];
        let mut right = term(1);
        // xy=0 follows from x=0, but is not in its linear ANF span.
        right.ket_guard = vec![x.clone(), x.and(&y)];
        assert!(matches!(
            normalize_constraint_span(&mut left.ket_guard),
            ConstraintNormalization::Normalized
        ));
        assert!(matches!(
            normalize_constraint_span(&mut right.ket_guard),
            ConstraintNormalization::Normalized
        ));
        assert_ne!(left.ket_guard, right.ket_guard);
        // The selector layer can now discharge this particular implication
        // using x=0, without claiming completeness for general Boolean ideals.
        assert!(exact_aggregate_match(
            &kernel(vec![left]),
            &kernel(vec![right])
        ));
    }

    #[test]
    fn nonlinear_selector_difference_is_not_erased() {
        let x = variable(KernelVariable::InputKet(0));
        let y = variable(KernelVariable::InputKet(1));
        let mut left = term(1);
        left.ket_guard = vec![x.and(&y)];
        let mut right = term(1);
        right.ket_guard = vec![x.xor(&y)];
        assert!(!exact_aggregate_match(
            &kernel(vec![left]),
            &kernel(vec![right])
        ));
    }

    #[test]
    fn affine_selector_substitution_preserves_free_coordinates() {
        let x = variable(KernelVariable::InputKet(0));
        let y = variable(KernelVariable::QuantumOutputKet(0));
        let mut restricted = term(1);
        restricted.ket_guard = vec![x.xor(&y)];
        assert!(!exact_aggregate_match(
            &kernel(vec![restricted]),
            &kernel(vec![term(1)])
        ));
    }

    #[test]
    fn triangular_selector_preserves_nonlinear_definitions_pointwise() {
        let variables = [
            KernelVariable::InputKet(0),
            KernelVariable::InputBra(0),
            KernelVariable::QuantumOutputKet(0),
        ];
        let x = variable(variables[0].clone());
        let y = variable(variables[1].clone());
        let z = variable(variables[2].clone());
        let monomials = (0..8)
            .map(|bits| {
                variables.iter().enumerate().fold(
                    KernelBooleanPolynomial::one(),
                    |product, (i, v)| {
                        if bits & (1 << i) == 0 {
                            product
                        } else {
                            product.and(&variable(v.clone()))
                        }
                    },
                )
            })
            .collect::<Vec<_>>();
        let holds = |rows: &[KernelBooleanPolynomial], assignment: usize| {
            rows.iter().all(|row| {
                variables
                    .iter()
                    .enumerate()
                    .fold(row.clone(), |row, (i, v)| {
                        row.substitute(
                            v,
                            &KernelBooleanPolynomial::from(assignment & (1 << i) != 0),
                        )
                    })
                    .is_zero()
            })
        };
        for bits in 0..256 {
            let extra = monomials.iter().enumerate().fold(
                KernelBooleanPolynomial::zero(),
                |sum, (i, m)| {
                    if bits & (1 << i) == 0 {
                        sum
                    } else {
                        sum.xor(m)
                    }
                },
            );
            for complement in [false, true] {
                let constraints = vec![
                    x.xor(&y.and(&z))
                        .xor(&KernelBooleanPolynomial::from(complement)),
                    extra.clone(),
                ];
                let mut working = WorkingTerm {
                    constraints: constraints.clone(),
                    paths: BTreeSet::new(),
                    coefficient: rational(1),
                    phase: KernelPhasePolynomial::default(),
                };
                let status = working.normalize_selector();
                assert!(!matches!(status, ConstraintNormalization::BudgetExceeded));
                for assignment in 0..8 {
                    assert_eq!(
                        holds(&constraints, assignment),
                        !matches!(status, ConstraintNormalization::Contradiction)
                            && holds(&working.constraints, assignment),
                        "bits={bits} complement={complement} assignment={assignment}"
                    );
                }
            }
        }
    }

    #[test]
    fn triangular_selector_substitutes_phase_and_weight_without_dropping_guard() {
        let x = variable(KernelVariable::InputKet(0));
        let yz = variable(KernelVariable::InputBra(0))
            .and(&variable(KernelVariable::QuantumOutputKet(0)));
        let make = |value: &KernelBooleanPolynomial, guarded: bool| {
            let mut source = term(1);
            if guarded {
                source.ket_guard = vec![x.xor(&yz)];
            }
            source.weight.ket = KernelScalar::Select {
                condition: value.clone(),
                when_true: Box::new(rational(3)),
                when_false: Box::new(rational(5)),
            };
            source.phase.ket.add_boolean(
                value,
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
            );
            kernel(vec![source])
        };
        assert!(exact_aggregate_match(&make(&x, true), &make(&yz, true)));
        assert!(!exact_aggregate_match(&make(&x, true), &make(&yz, false)));
    }

    #[test]
    fn self_dependent_nonlinear_selector_is_not_used_as_a_definition() {
        let x = variable(KernelVariable::InputKet(0));
        let y = variable(KernelVariable::InputBra(0));
        let equation = x.xor(&x.and(&y));
        let mut working = WorkingTerm {
            constraints: vec![equation.clone()],
            paths: BTreeSet::new(),
            coefficient: rational(1),
            phase: KernelPhasePolynomial::default(),
        };
        assert!(matches!(
            working.normalize_selector(),
            ConstraintNormalization::Normalized
        ));
        assert_eq!(working.constraints, vec![equation]);
    }

    #[test]
    fn boolean_preflight_fast_bound_matches_full_monomial_count() {
        let x = KernelVariable::InputKet(0);
        let y = KernelVariable::InputKet(1);
        let basis = [
            KernelBooleanPolynomial::one(),
            variable(x.clone()),
            variable(y.clone()),
            variable(x.clone()).and(&variable(y.clone())),
        ];
        let polynomial = |mask: u8| {
            basis
                .iter()
                .enumerate()
                .fold(KernelBooleanPolynomial::zero(), |sum, (index, term)| {
                    if mask & (1 << index) != 0 {
                        sum.xor(term)
                    } else {
                        sum
                    }
                })
        };
        let check = |source: &KernelBooleanPolynomial, replacement: &KernelBooleanPolynomial| {
            let expected = source
                .terms()
                .map(|term| {
                    if term.contains(&x) {
                        replacement.term_count()
                    } else {
                        1
                    }
                })
                .sum::<usize>()
                <= MAX_BOOLEAN_TERMS;
            let actual = boolean_substitution_within_budget(source, &x, replacement);
            assert_eq!(actual, expected);
            actual
        };
        for left in 0..16 {
            for right in 0..16 {
                check(&polynomial(left), &polynomial(right));
            }
        }
        let mut source = KernelBooleanPolynomial::zero();
        let mut replacement = KernelBooleanPolynomial::zero();
        for index in 2..2002 {
            source = source.xor(&variable(KernelVariable::InputKet(index)));
            if index < 102 {
                replacement = replacement.xor(&variable(KernelVariable::InputBra(index)));
            }
        }
        // The loose bound refuses, but the exact fallback distinguishes
        // zero/one/all occurrences of x. No growth is accepted by truncation.
        assert!(check(&source, &replacement));
        assert!(check(&source.xor(&variable(x.clone())), &replacement));
        assert!(!check(&source.and(&variable(x.clone())), &replacement));
    }

    #[test]
    fn equal_size_pivots_keep_candidate_order_despite_phase_occurrences() {
        let p = KernelVariable::PathKet { term: 0, path: 0 };
        let q = KernelVariable::PathKet { term: 0, path: 1 };
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(
            &variable(p.clone()),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        let working = WorkingTerm {
            paths: BTreeSet::from([p.clone(), q.clone()]),
            constraints: vec![
                variable(p.clone())
                    .xor(&variable(q.clone()))
                    .xor(&variable(KernelVariable::InputKet(0))),
            ],
            coefficient: rational(1),
            phase,
        };
        let (chosen, replacement) = working.best_constraint_pivot().unwrap();
        assert_eq!(chosen, p);
        assert_eq!(
            replacement,
            variable(q).xor(&variable(KernelVariable::InputKet(0)))
        );
        assert!(working.substitution_within_budget(&chosen, &replacement));
    }

    #[test]
    fn sparse_pivot_search_preserves_the_original_candidate_order() {
        let paths = BTreeSet::from([
            KernelVariable::PathKet { term: 0, path: 0 },
            KernelVariable::PathBra { term: 0, path: 0 },
            KernelVariable::PathBra { term: 0, path: 99 },
        ]);
        let x = variable(paths.first().unwrap().clone());
        let y = variable(KernelVariable::PathBra { term: 0, path: 0 });
        let atoms = [
            KernelBooleanPolynomial::one(),
            x.clone(),
            y.clone(),
            x.and(&y),
        ];
        let polynomial = |bits: usize| {
            atoms
                .iter()
                .enumerate()
                .fold(KernelBooleanPolynomial::zero(), |sum, (i, m)| {
                    if bits & (1 << i) == 0 {
                        sum
                    } else {
                        sum.xor(m)
                    }
                })
        };
        for f in 0..16 {
            for g in 0..16 {
                let working = WorkingTerm {
                    paths: paths.clone(),
                    constraints: vec![polynomial(f), polynomial(g)],
                    coefficient: rational(1),
                    phase: KernelPhasePolynomial::default(),
                };
                let reference = working
                    .constraints
                    .iter()
                    .flat_map(|equation| {
                        paths.iter().filter_map(move |v| {
                            let atom = KernelMonomial::variable(v.clone());
                            if !equation.has_term(&atom)
                                || equation
                                    .terms()
                                    .any(|term| term != &atom && term.contains(v))
                            {
                                return None;
                            }
                            Some((v.clone(), equation.xor(&variable(v.clone()))))
                        })
                    })
                    .min_by_key(|(_, replacement)| replacement.term_count());
                assert_eq!(working.best_constraint_pivot(), reference);
            }
        }
    }

    #[test]
    fn affine_selector_substitution_preserves_phase_and_scalar_pointwise() {
        let x = variable(KernelVariable::InputKet(0));
        let y = variable(KernelVariable::InputBra(0));
        let monomials = [
            KernelBooleanPolynomial::one(),
            x.clone(),
            y.clone(),
            x.and(&y),
        ];
        for bits in 0..16 {
            let extra = monomials.iter().enumerate().fold(
                KernelBooleanPolynomial::zero(),
                |sum, (i, m)| {
                    if bits & (1 << i) == 0 {
                        sum
                    } else {
                        sum.xor(m)
                    }
                },
            );
            let mut phase = KernelPhasePolynomial::default();
            phase.add_boolean(
                &x.and(&y),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
            );
            let coefficient = KernelScalar::Select {
                condition: x.clone(),
                when_true: Box::new(rational(2)),
                when_false: Box::new(rational(3)),
            };
            let constraints = vec![x.xor(&y).complement(), extra];
            let mut working = WorkingTerm {
                paths: BTreeSet::new(),
                constraints: constraints.clone(),
                coefficient: coefficient.clone(),
                phase: phase.clone(),
            };
            let result = working.normalize_selector();
            assert!(!matches!(result, ConstraintNormalization::BudgetExceeded));
            for assignment in 0..4 {
                let values = [
                    (
                        KernelVariable::InputKet(0),
                        KernelBooleanPolynomial::from(assignment & 1 != 0),
                    ),
                    (
                        KernelVariable::InputBra(0),
                        KernelBooleanPolynomial::from(assignment & 2 != 0),
                    ),
                ];
                let holds = |rows: &[KernelBooleanPolynomial]| {
                    rows.iter().all(|row| {
                        values
                            .iter()
                            .fold(row.clone(), |row, (v, f)| row.substitute(v, f))
                            .is_zero()
                    })
                };
                let before = holds(&constraints);
                assert_eq!(
                    before,
                    !matches!(result, ConstraintNormalization::Contradiction)
                        && holds(&working.constraints)
                );
                if before {
                    let eval_scalar = |scalar: &KernelScalar| {
                        normalize_scalar(
                            values
                                .iter()
                                .fold(scalar.clone(), |s, (v, f)| s.substitute(v, f)),
                        )
                    };
                    let eval_phase = |phase: &KernelPhasePolynomial| {
                        let mut phase = phase.clone();
                        for (v, f) in &values {
                            phase.substitute(v, f);
                        }
                        phase
                    };
                    assert_eq!(eval_scalar(&coefficient), eval_scalar(&working.coefficient));
                    assert_eq!(eval_phase(&phase), eval_phase(&working.phase));
                }
            }
        }
    }

    #[test]
    fn affine_selector_exposes_new_equalities_in_nonlinear_rows() {
        let x = variable(KernelVariable::InputKet(0));
        let y = variable(KernelVariable::InputKet(1));
        let z = variable(KernelVariable::InputKet(2));
        let mut original = term(1);
        original.ket_guard = vec![x.xor(&y), x.and(&y).xor(&z), x.xor(&z).complement()];
        // x=y implies xy=x, so the other two equations contradict each other.
        assert!(exact_aggregate_match(
            &kernel(vec![original]),
            &kernel(Vec::new())
        ));
    }

    #[test]
    fn path_elimination_counts_exact_solutions_without_repeated_rref() {
        let x = KernelVariable::InputKet(0);
        let p = KernelVariable::PathKet { term: 0, path: 0 };
        let q = KernelVariable::PathBra { term: 0, path: 0 };
        let variables = [x.clone(), p.clone(), q.clone()];
        let monomials = (0..8)
            .map(|bits| {
                variables.iter().enumerate().fold(
                    KernelBooleanPolynomial::one(),
                    |product, (i, v)| {
                        if bits & (1 << i) == 0 {
                            product
                        } else {
                            product.and(&variable(v.clone()))
                        }
                    },
                )
            })
            .collect::<Vec<_>>();
        let eval = |row: &KernelBooleanPolynomial, values: usize| {
            variables
                .iter()
                .enumerate()
                .fold(row.clone(), |row, (i, v)| {
                    row.substitute(v, &KernelBooleanPolynomial::from(values & (1 << i) != 0))
                })
                .is_zero()
        };
        let mut certified = 0;
        for bits in 0..256 {
            let f = monomials.iter().enumerate().fold(
                KernelBooleanPolynomial::zero(),
                |sum, (i, m)| {
                    if bits & (1 << i) == 0 {
                        sum
                    } else {
                        sum.xor(m)
                    }
                },
            );
            for g in [&p, &q] {
                let mut source = term(1);
                source.ket_paths.insert(p.clone());
                source.bra_paths.insert(q.clone());
                source.ket_guard = vec![f.clone(), variable(g.clone()).xor(&variable(x.clone()))];
                let reduction = reduce_term(&source);
                if matches!(reduction, Reduction::Residual | Reduction::Sum(_)) {
                    continue;
                }
                certified += 1;
                for input in 0..2 {
                    let count = (0..4)
                        .filter(|paths| {
                            source
                                .ket_guard
                                .iter()
                                .all(|row| eval(row, (paths << 1) | input))
                        })
                        .count();
                    let actual = match &reduction {
                        Reduction::Zero => rational(0),
                        Reduction::Exact(term) => {
                            assert_eq!(term.phase, KernelPhasePolynomial::default());
                            if term.constraints.iter().all(|row| eval(row, input)) {
                                normalize_scalar(
                                    term.coefficient
                                        .substitute(&x, &KernelBooleanPolynomial::from(input != 0)),
                                )
                            } else {
                                rational(0)
                            }
                        }
                        Reduction::Residual | Reduction::Sum(_) => unreachable!(),
                    };
                    assert_eq!(actual, rational(count as i64), "bits={bits} input={input}");
                }
            }
        }
        assert!(certified > 100);
    }

    #[test]
    fn nonlinear_contradiction_annihilates_the_whole_term() {
        let xy = variable(KernelVariable::InputKet(0)).and(&variable(KernelVariable::InputBra(0)));
        let mut impossible = term(7);
        impossible.ket_guard = vec![xy.clone(), xy.complement()];
        assert!(exact_aggregate_match(
            &kernel(vec![impossible]),
            &kernel(Vec::new())
        ));
    }

    #[test]
    fn constraint_span_refuses_an_oversized_matrix() {
        let mut constraints = vec![variable(KernelVariable::InputKet(0)); 4_000];
        constraints[0] = affine((0..3_000).map(KernelVariable::InputKet));
        assert!(matches!(
            normalize_constraint_span(&mut constraints),
            ConstraintNormalization::BudgetExceeded
        ));
    }

    #[test]
    fn nonlinear_row_span_preserves_all_two_variable_equation_pairs() {
        let x = variable(KernelVariable::InputKet(0));
        let y = variable(KernelVariable::InputKet(1));
        let monomials = [
            KernelBooleanPolynomial::one(),
            x.clone(),
            y.clone(),
            x.and(&y),
        ];
        let polynomial = |bits: usize| {
            monomials
                .iter()
                .enumerate()
                .fold(KernelBooleanPolynomial::zero(), |sum, (i, m)| {
                    if bits & (1 << i) == 0 {
                        sum
                    } else {
                        sum.xor(m)
                    }
                })
        };
        let holds = |rows: &[KernelBooleanPolynomial], bits: usize| {
            rows.iter().all(|row| {
                row.substitute(
                    &KernelVariable::InputKet(0),
                    &KernelBooleanPolynomial::from(bits & 1 != 0),
                )
                .substitute(
                    &KernelVariable::InputKet(1),
                    &KernelBooleanPolynomial::from(bits & 2 != 0),
                )
                .is_zero()
            })
        };
        for f in 0..16 {
            for g in 0..16 {
                let original = vec![polynomial(f), polynomial(g)];
                let mut reduced = original.clone();
                let result = normalize_constraint_span(&mut reduced);
                assert!(!matches!(result, ConstraintNormalization::BudgetExceeded));
                for input in 0..4 {
                    let reduced_holds = !matches!(result, ConstraintNormalization::Contradiction)
                        && holds(&reduced, input);
                    assert_eq!(
                        holds(&original, input),
                        reduced_holds,
                        "f={f} g={g} input={input}"
                    );
                }
                let mut changed = vec![
                    polynomial(f ^ g),
                    polynomial(f),
                    KernelBooleanPolynomial::zero(),
                ];
                let changed_result = normalize_constraint_span(&mut changed);
                assert_eq!(
                    matches!(result, ConstraintNormalization::Contradiction),
                    matches!(changed_result, ConstraintNormalization::Contradiction)
                );
                if matches!(result, ConstraintNormalization::Normalized) {
                    assert_eq!(reduced, changed);
                }
            }
        }
    }

    #[test]
    fn bound_phase_cancels_under_retained_free_selector() {
        let path = KernelVariable::PathKet { term: 0, path: 0 };
        let x = variable(KernelVariable::InputKet(0));
        let y = variable(KernelVariable::InputBra(0));
        let mut source = term(1);
        source.ket_paths.insert(path.clone());
        source.ket_guard.push(x.xor(&y));
        source.phase.ket.add_boolean(
            &variable(path.clone()).and(&x),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        source.phase.ket.add_boolean(
            &variable(path).and(&y),
            crate::symbolic::PhaseCoefficient::rational(ratio(-1, 8)),
        );
        let mut expected = term(2);
        expected.ket_guard.push(x.xor(&y));
        // Local reduction itself succeeds, without Shannon enumeration.
        assert!(matches!(reduce_term(&source), Reduction::Exact(_)));
        assert!(exact_aggregate_match(
            &kernel(vec![source.clone()]),
            &kernel(vec![expected.clone()])
        ));
        // Retaining the selector is essential. Outside x=y the path sum is
        // 1+exp(±i*pi/4), not 2; it must not become the guarded channel.
        source.ket_guard.clear();
        assert!(!exact_aggregate_match(
            &kernel(vec![source]),
            &kernel(vec![expected])
        ));
    }

    #[test]
    fn vacuous_path_sum_contributes_exact_factor_two() {
        let mut summed = term(1);
        summed
            .ket_paths
            .insert(KernelVariable::PathKet { term: 0, path: 0 });

        assert!(exact_aggregate_match(
            &kernel(vec![summed]),
            &kernel(vec![term(2)])
        ));
    }

    #[test]
    fn fourier_path_sum_emits_an_affine_delta() {
        let path = KernelVariable::PathKet { term: 0, path: 0 };
        let input = variable(KernelVariable::InputKet(0));
        let mut summed = term(1);
        summed.ket_paths.insert(path.clone());
        summed.phase.ket.add_boolean(
            &variable(path).and(&input),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
        let mut expected = term(2);
        expected.ket_guard = vec![input];

        assert!(exact_aggregate_match(
            &kernel(vec![summed]),
            &kernel(vec![expected])
        ));
    }

    #[test]
    fn contradictory_fourier_delta_annihilates_the_term() {
        let path = KernelVariable::PathKet { term: 0, path: 0 };
        let mut summed = term(1);
        summed.ket_paths.insert(path.clone());
        summed.phase.ket.add_boolean(
            &variable(path),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );

        assert!(matches!(reduce_term(&summed), Reduction::Zero));
        assert!(exact_aggregate_match(
            &kernel(vec![summed]),
            &kernel(Vec::new())
        ));
    }

    #[test]
    fn omega_path_sum_rewrites_coefficient_and_phase_exactly() {
        let path = KernelVariable::PathKet { term: 0, path: 0 };
        let parity = variable(KernelVariable::InputKet(0));
        let path_polynomial = variable(path.clone());
        let mut summed = term(1);
        summed.ket_paths.insert(path);
        summed.phase.ket.add_boolean(
            &path_polynomial,
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 4)),
        );
        summed.phase.ket.add_boolean(
            &path_polynomial.and(&parity),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );

        let mut expected = term(1);
        expected.weight.ket = sqrt_ratio(2, 1);
        expected.phase.ket.add_boolean(
            &KernelBooleanPolynomial::one(),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        expected.phase.ket.add_boolean(
            &parity,
            crate::symbolic::PhaseCoefficient::rational(ratio(-1, 4)),
        );

        assert!(exact_aggregate_match(
            &kernel(vec![summed]),
            &kernel(vec![expected])
        ));
    }

    #[test]
    fn bounded_residual_weight_sum_adds_both_branches_exactly() {
        let mut residual = term(1);
        let path = KernelVariable::PathKet { term: 0, path: 0 };
        residual.ket_paths.insert(path.clone());
        residual.weight.ket = KernelScalar::Select {
            condition: variable(path),
            when_true: Box::new(rational(3)),
            when_false: Box::new(rational(5)),
        };
        assert!(exact_aggregate_match(
            &kernel(vec![residual.clone()]),
            &kernel(vec![term(8)])
        ));
        assert!(!exact_aggregate_match(
            &kernel(vec![residual]),
            &kernel(vec![term(4)])
        ));
    }

    #[test]
    fn residual_sum_preserves_interference_and_half_turn_cancellation() {
        let path = KernelVariable::PathKet { term: 0, path: 0 };
        let mut summed = term(1);
        summed.ket_paths.insert(path.clone());
        summed.weight.ket = KernelScalar::Select {
            condition: variable(path.clone()),
            when_true: Box::new(rational(3)),
            when_false: Box::new(rational(5)),
        };
        summed.phase.ket.add_boolean(
            &variable(path),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
        assert!(exact_aggregate_match(
            &kernel(vec![summed.clone()]),
            &kernel(vec![term(2)])
        ));
        assert!(!exact_aggregate_match(
            &kernel(vec![summed]),
            &kernel(vec![term(8)])
        ));

        let mut negative = term(1);
        negative.phase.ket.add_boolean(
            &KernelBooleanPolynomial::one(),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
        assert!(exact_aggregate_match(
            &kernel(vec![term(1), negative]),
            &kernel(Vec::new())
        ));
        let mut imaginary = term(1);
        imaginary.phase.ket.add_boolean(
            &KernelBooleanPolynomial::one(),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 4)),
        );
        assert!(!exact_aggregate_match(
            &kernel(vec![imaginary]),
            &kernel(vec![term(1)])
        ));
    }

    #[test]
    fn residual_sum_keeps_free_input_phase_dependence() {
        let path = KernelVariable::PathKet { term: 0, path: 0 };
        let input = variable(KernelVariable::InputKet(0));
        let mut summed = term(1);
        summed.ket_paths.insert(path.clone());
        summed.weight.ket = KernelScalar::Select {
            condition: variable(path.clone()),
            when_true: Box::new(rational(3)),
            when_false: Box::new(rational(5)),
        };
        summed.phase.ket.add_boolean(
            &variable(path).and(&input),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
        let mut expected = term(3);
        expected.phase.ket.add_boolean(
            &input,
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
        assert!(exact_aggregate_match(
            &kernel(vec![summed.clone()]),
            &kernel(vec![term(5), expected])
        ));
        assert!(!exact_aggregate_match(
            &kernel(vec![summed]),
            &kernel(vec![term(8)])
        ));
    }

    #[test]
    fn free_cofactors_prove_complementary_selector_partitions() {
        let x = variable(KernelVariable::InputKet(0));
        let mut zero = term(3);
        zero.ket_guard = vec![x.clone()];
        let mut one = term(3);
        one.ket_guard = vec![x.complement()];
        assert!(exact_aggregate_match(
            &kernel(vec![zero.clone(), one.clone()]),
            &kernel(vec![term(3)])
        ));
        let difference = aggregate_difference(
            reduce_kernel(&kernel(vec![zero, one])).unwrap(),
            reduce_kernel(&kernel(vec![term(3)])).unwrap(),
        )
        .unwrap();
        assert!(!zero_by_free_splitting(difference.clone(), &mut 0, 0));
        assert!(!zero_by_free_splitting(
            difference.clone(),
            &mut 1,
            MAX_FREE_SPLIT_DEPTH
        ));
        assert!(zero_by_free_splitting(difference, &mut 1, 0));
    }

    #[test]
    fn free_branches_must_each_match_not_cancel_each_other() {
        let mut one_branch = term(2);
        one_branch.ket_guard = vec![variable(KernelVariable::InputBra(0))];
        // The two programs have equal sums over the free coordinate (2), but
        // their pointwise values are (2,0) and (1,1). Never sum these branches.
        assert!(!exact_aggregate_match(
            &kernel(vec![one_branch]),
            &kernel(vec![term(1)])
        ));
    }

    #[test]
    fn common_selector_can_be_factored_out_but_does_not_prove_nonzero_coefficients() {
        let common = variable(KernelVariable::InputKet(0));
        let x = variable(KernelVariable::InputBra(0));
        let mut zero = term(3);
        zero.ket_guard = vec![common.clone(), x.clone()];
        let mut one = term(3);
        one.ket_guard = vec![common.clone(), x.complement()];
        let mut whole = term(3);
        whole.ket_guard = vec![common.clone()];
        let difference = aggregate_difference(
            reduce_kernel(&kernel(vec![zero, one])).unwrap(),
            reduce_kernel(&kernel(vec![whole.clone()])).unwrap(),
        )
        .unwrap();
        // Only x needs a split, not the common guard's independent variable.
        assert!(zero_by_free_splitting(difference, &mut 1, 0));
        assert!(!zero_by_free_splitting(
            reduce_kernel(&kernel(vec![whole])).unwrap(),
            &mut 1,
            0
        ));
        let mut complement = term(3);
        complement.ket_guard = vec![common.complement()];
        let mut selected = term(3);
        selected.ket_guard = vec![common];
        assert!(!exact_aggregate_match(
            &kernel(vec![selected]),
            &kernel(vec![complement])
        ));
    }

    #[test]
    fn common_free_phase_does_not_consume_free_split_depth() {
        let mut phased = term(1);
        for input in 0..20 {
            phased.phase.ket.add_boolean(
                &variable(KernelVariable::InputKet(input)),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 7)),
            );
        }
        let split = variable(KernelVariable::InputBra(0));
        let mut zero = phased.clone();
        zero.ket_guard.push(split.clone());
        let mut one = phased.clone();
        one.ket_guard.push(split.complement());
        one.weight.ket = rational(-1);
        phased.phase.ket.add_boolean(
            &split,
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
        let difference = aggregate_difference(
            reduce_kernel(&kernel(vec![phased.clone()])).unwrap(),
            reduce_kernel(&kernel(vec![zero, one])).unwrap(),
        )
        .unwrap();
        assert!(zero_by_free_splitting(difference, &mut 1, 0));
        assert!(!exact_aggregate_match(
            &kernel(vec![phased]),
            &kernel(vec![term(1)])
        ));
    }

    #[test]
    fn removing_common_phase_reconstructs_the_original_exact_sum() {
        let x = variable(KernelVariable::InputKet(0));
        let y = variable(KernelVariable::InputBra(0));
        for numerator in 1..7 {
            let mut left = term(3);
            left.ket_guard
                .push(variable(KernelVariable::ClassicalOutput(0)));
            left.phase.ket.add_boolean(
                &x.and(&y),
                crate::symbolic::PhaseCoefficient::rational(ratio(numerator, 7)),
            );
            let mut right = left.clone();
            right.ket_guard.clear();
            right.weight.ket = rational(5);
            right
                .phase
                .ket
                .add_boolean(&x, crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)));
            let source = reduce_kernel(&kernel(vec![left.clone(), right])).unwrap();
            let reduced = remove_common_phase(source.clone()).unwrap();
            left.ket_guard.clear();
            left.weight.ket = rational(1);
            let common = reduce_kernel(&kernel(vec![left])).unwrap();
            let mut budget = ReductionBudget {
                splits: 0,
                products: MAX_FACTOR_PRODUCTS,
                phase_cells: MAX_FACTOR_PHASE_CELLS,
            };
            assert_eq!(
                multiply_aggregates(common, reduced, &mut budget).unwrap(),
                source
            );
        }
    }

    #[test]
    fn tensor_certificate_checks_smaller_pointwise_equalities() {
        let x = variable(KernelVariable::InputKet(0));
        let y = variable(KernelVariable::InputKet(1));
        let b = variable(KernelVariable::InputBra(0));
        let mut left = term(1);
        left.phase.ket.add_boolean(
            &x.and(&y),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
        left.phase
            .ket
            .add_boolean(&b, crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)));
        let right = [
            KernelBooleanPolynomial::zero(),
            x.clone(),
            y.clone(),
            x.xor(&y),
        ]
        .into_iter()
        .enumerate()
        .map(|(index, parity)| {
            let mut leaf = term(1);
            leaf.weight.ket = KernelScalar::Rational(ratio(if index == 3 { -1 } else { 1 }, 2));
            leaf.phase.ket.add_boolean(
                &parity,
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
            );
            leaf.phase
                .ket
                .add_boolean(&b, crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)));
            leaf
        })
        .collect();
        let left = reduce_kernel(&kernel(vec![left])).unwrap();
        let right = reduce_kernel(&kernel(right)).unwrap();
        assert_ne!(left, right);
        let mut free_budget = MAX_FREE_SPLITS;
        assert!(tensor_aggregate_match(&left, &right, &mut free_budget));
        assert!(!tensor_aggregate_match(&left, &right, &mut 0));
        let wrong = reduce_kernel(&kernel(vec![term(2)])).unwrap();
        free_budget = MAX_FREE_SPLITS;
        assert!(!tensor_aggregate_match(&left, &wrong, &mut free_budget));
    }

    #[test]
    fn tensor_reconstruction_rejects_missing_cells_and_mixed_phases() {
        let mut ket = term(3);
        ket.phase.ket.add_boolean(
            &variable(KernelVariable::InputKet(0)),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        let mut bra = term(5);
        bra.phase.ket.add_boolean(
            &variable(KernelVariable::InputBra(0)),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 7)),
        );
        let mut budget = ReductionBudget {
            splits: 0,
            products: MAX_FACTOR_PRODUCTS,
            phase_cells: MAX_FACTOR_PHASE_CELLS,
        };
        let source = multiply_aggregates(
            reduce_kernel(&kernel(vec![term(1), ket])).unwrap(),
            reduce_kernel(&kernel(vec![term(2), bra])).unwrap(),
            &mut budget,
        )
        .unwrap();
        assert!(factor_free_tensor(&source, &mut budget).is_some());
        let mut missing = source.clone();
        missing.values_mut().next().unwrap().pop_first();
        assert!(factor_free_tensor(&missing, &mut budget).is_none());
        let mut wrong_sign = source;
        let value = wrong_sign
            .values_mut()
            .next()
            .unwrap()
            .values_mut()
            .next()
            .unwrap();
        *value = normalize_scalar(KernelScalar::Neg(Box::new(value.clone())));
        assert!(factor_free_tensor(&wrong_sign, &mut budget).is_none());
        let mut mixed = term(1);
        mixed.phase.ket.add_boolean(
            &variable(KernelVariable::InputKet(0)).and(&variable(KernelVariable::InputBra(0))),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        assert!(
            factor_free_tensor(&reduce_kernel(&kernel(vec![mixed])).unwrap(), &mut budget)
                .is_none()
        );
    }

    #[test]
    fn tensor_factors_preserve_shared_selector_parameters_and_exponential_pivots() {
        let parameter = variable(KernelVariable::QuantumOutputBra(1));
        let mut common = term(2);
        common.phase.ket.add_boolean(
            &parameter,
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 9)),
        );
        let mut ket = term(3);
        ket.phase.ket.add_boolean(
            &variable(KernelVariable::InputKet(0)).and(&parameter),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        let mut bra = term(5);
        bra.phase.ket.add_boolean(
            &variable(KernelVariable::InputBra(0)).and(&parameter),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 7)),
        );
        let mut budget = ReductionBudget {
            splits: 0,
            products: MAX_FACTOR_PRODUCTS,
            phase_cells: MAX_FACTOR_PHASE_CELLS,
        };
        let product = multiply_aggregates(
            reduce_kernel(&kernel(vec![term(1), ket])).unwrap(),
            reduce_kernel(&kernel(vec![term(1), bra])).unwrap(),
            &mut budget,
        )
        .unwrap();
        let product = multiply_aggregates(
            reduce_kernel(&kernel(vec![common])).unwrap(),
            product,
            &mut budget,
        )
        .unwrap();
        let mut guarded = ExactAggregate::new();
        guarded.insert(
            ExactEntry {
                constraints: vec![variable(KernelVariable::InputKet(2)).xor(&parameter)],
            },
            product.values().next().unwrap().clone(),
        );
        assert!(factor_free_tensor(&product, &mut budget).is_none());
        let [ket, bra] = factor_free_tensor(&guarded, &mut budget).unwrap();
        assert_eq!(multiply_aggregates(ket, bra, &mut budget).unwrap(), product);
        // Both values of the shared parameter are compared pointwise; neither
        // a renamed parameter nor the sum of its two values is a certificate.
        let wrong =
            restrict_aggregate(&guarded, &KernelVariable::QuantumOutputBra(1), false).unwrap();
        let mut free_budget = MAX_FREE_SPLITS;
        assert!(!tensor_aggregate_match(&guarded, &wrong, &mut free_budget));
    }

    #[test]
    fn free_splitting_preserves_relative_phase_across_selectors() {
        let x = variable(KernelVariable::InputKet(0));
        let mut phase = term(1);
        phase
            .phase
            .ket
            .add_boolean(&x, crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)));
        let mut zero = term(1);
        zero.ket_guard = vec![x.clone()];
        let mut one = term(-1);
        one.ket_guard = vec![x.complement()];
        assert!(exact_aggregate_match(
            &kernel(vec![phase.clone()]),
            &kernel(vec![zero, one])
        ));
        assert!(!exact_aggregate_match(
            &kernel(vec![phase]),
            &kernel(vec![term(1)])
        ));
    }

    fn eighth_turn_residual(paths: usize) -> KernelTerm {
        let mut summed = term(1);
        for path in 0..paths {
            let v = KernelVariable::PathKet { term: 0, path };
            summed.ket_paths.insert(v.clone());
            summed.phase.ket.add_boolean(
                &variable(v),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        summed
    }

    #[test]
    fn residual_split_unlocks_factors_before_exhausting_depth() {
        let mut source = eighth_turn_residual(10);
        let blocker = KernelVariable::PathKet { term: 0, path: 9 };
        let free = variable(KernelVariable::InputKet(0));
        source.ket_guard.push(variable(blocker.clone()).and(&free));
        let Reduction::Sum(residual) = reduce_term(&source) else {
            panic!("nonlinear selector keeps a genuine bound residual");
        };
        assert_ne!(residual.paths.first(), Some(&blocker));
        assert_eq!(residual.residual_split_variable(), Some(blocker));
        // The two literal blocker branches retain every independent factor,
        // with the original selector applying only to the one branch.
        let zero = eighth_turn_residual(9);
        let mut one = zero.clone();
        one.ket_guard.push(free);
        one.phase.ket.add_boolean(
            &KernelBooleanPolynomial::one(),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        assert!(reduce_kernel(&kernel(vec![source.clone()])).is_some());
        assert!(exact_aggregate_match(
            &kernel(vec![source]),
            &kernel(vec![zero, one])
        ));
    }

    #[test]
    fn residual_split_preserves_weight_branches_and_bounds_order_search() {
        let mut source = eighth_turn_residual(10);
        let blocker = KernelVariable::PathKet { term: 0, path: 9 };
        source.weight.ket = KernelScalar::Select {
            condition: variable(blocker.clone()),
            when_true: Box::new(rational(3)),
            when_false: Box::new(rational(5)),
        };
        let Reduction::Sum(mut residual) = reduce_term(&source) else {
            panic!("path-dependent scalar prevents phase factorization");
        };
        assert_eq!(residual.residual_split_variable(), Some(blocker.clone()));
        let mut zero = eighth_turn_residual(9);
        zero.weight.ket = rational(5);
        let mut one = zero.clone();
        one.weight.ket = rational(3);
        one.phase.ket.add_boolean(
            &KernelBooleanPolynomial::one(),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        assert!(exact_aggregate_match(
            &kernel(vec![source]),
            &kernel(vec![zero, one])
        ));

        residual.constraints = vec![
            affine((0..MAX_RESIDUAL_ORDER_VISITS).map(KernelVariable::InputKet))
                .xor(&variable(blocker)),
        ];
        let before = residual.clone();
        assert_eq!(
            residual.residual_split_variable().as_ref(),
            residual.paths.first()
        );
        assert_eq!(residual.constraints, before.constraints);
        assert_eq!(residual.coefficient, before.coefficient);
        assert_eq!(residual.phase, before.phase);
        assert_eq!(residual.paths, before.paths);
    }

    fn weighted_eighth_turn_residual(paths: usize) -> KernelTerm {
        let mut summed = eighth_turn_residual(paths);
        for path in &summed.ket_paths {
            summed.weight.ket = multiply(
                summed.weight.ket,
                KernelScalar::Select {
                    condition: variable(path.clone()),
                    when_true: Box::new(rational(3)),
                    when_false: Box::new(rational(5)),
                },
            );
        }
        summed
    }

    #[test]
    fn separated_phase_sums_match_literal_enumeration_with_shared_free_coordinates() {
        let mut source = eighth_turn_residual(9);
        let input = variable(KernelVariable::InputKet(0));
        source.ket_guard.push(variable(KernelVariable::InputBra(0)));
        source.weight.ket = KernelScalar::Select {
            condition: input.clone(),
            when_true: Box::new(rational(3)),
            when_false: Box::new(rational(5)),
        };
        source.phase.ket.add_boolean(
            &input,
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 7)),
        );
        // The same free input is shared by all factors, not summed or renamed.
        for path in &source.ket_paths {
            source.phase.ket.add_boolean(
                &variable(path.clone()).and(&input),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        let expected = (0..512)
            .map(|bits| {
                let mut leaf = source.clone();
                for (index, path) in source.ket_paths.iter().enumerate() {
                    leaf.phase.ket.substitute(
                        path,
                        &KernelBooleanPolynomial::from(bits & (1 << index) != 0),
                    );
                }
                leaf.ket_paths.clear();
                leaf
            })
            .collect();
        assert!(reduce_kernel(&kernel(vec![source.clone()])).is_some());
        assert!(exact_aggregate_match(
            &kernel(vec![source]),
            &kernel(expected)
        ));
    }

    #[test]
    fn phase_factorization_respects_mixed_monomials_guards_and_scalar_conditions() {
        let source = eighth_turn_residual(3);
        let Reduction::Sum(mut working) = reduce_term(&source) else {
            panic!("residual expected")
        };
        assert_eq!(factor_phase_sums(&working).unwrap().len(), 4);
        let paths = working.paths.iter().cloned().collect::<Vec<_>>();
        working.phase.add_boolean(
            &variable(paths[0].clone()).and(&variable(paths[1].clone())),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        let factors = factor_phase_sums(&working).unwrap();
        assert_eq!(factors.len(), 3);
        assert!(
            factors
                .iter()
                .any(|f| f.paths.contains(&paths[0]) && f.paths.contains(&paths[1]))
        );
        working.constraints.push(variable(paths[2].clone()));
        let factors = factor_phase_sums(&working).unwrap();
        assert_eq!(factors.len(), 3);
        assert!(
            factors.iter().any(|factor| factor.paths.contains(&paths[2])
                && factor.constraints == working.constraints)
        );
        // A whole XOR row connects even separate monomials; it must not be
        // split into two indicators with a stronger zero set.
        working
            .constraints
            .push(variable(paths[0].clone()).xor(&variable(paths[2].clone())));
        assert!(factor_phase_sums(&working).is_none());
        working.constraints.clear();
        working.coefficient = KernelScalar::Select {
            condition: variable(paths[2].clone()),
            when_true: Box::new(rational(3)),
            when_false: Box::new(rational(5)),
        };
        assert!(factor_phase_sums(&working).is_none());
        working.coefficient = rational(1);
        working.phase.add_boolean(
            &variable(paths[1].clone()).and(&variable(paths[2].clone())),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        assert!(factor_phase_sums(&working).is_none());
    }

    #[test]
    fn guarded_factorization_preserves_all_pointwise_weights_and_equations() {
        let names = [
            KernelVariable::PathKet { term: 0, path: 0 },
            KernelVariable::PathBra { term: 1, path: 0 },
            KernelVariable::PathKet { term: 0, path: 1 },
            KernelVariable::InputKet(0),
        ];
        let vars = names.clone().map(variable);
        let anf = |mask: usize, a: &KernelBooleanPolynomial, b: &KernelBooleanPolynomial| {
            [
                KernelBooleanPolynomial::one(),
                a.clone(),
                b.clone(),
                a.and(b),
            ]
            .into_iter()
            .enumerate()
            .fold(KernelBooleanPolynomial::zero(), |p, (bit, term)| {
                if mask & (1 << bit) == 0 {
                    p
                } else {
                    p.xor(&term)
                }
            })
        };
        for f in 0..16 {
            for g in 0..16 {
                let mut source = WorkingTerm {
                    paths: names[..3].iter().cloned().collect(),
                    constraints: vec![anf(f, &vars[0], &vars[1]), anf(g, &vars[2], &vars[3])],
                    coefficient: rational(3),
                    phase: KernelPhasePolynomial::default(),
                };
                for (index, term) in [
                    vars[0].and(&vars[1]).and(&vars[3]),
                    vars[2].and(&vars[3]),
                    vars[3].clone(),
                ]
                .into_iter()
                .enumerate()
                {
                    source.phase.add_boolean(
                        &term,
                        crate::symbolic::PhaseCoefficient::rational(ratio(index as i64 + 1, 8)),
                    );
                }
                let factors = factor_phase_sums(&source).unwrap();
                assert_eq!(factors.len(), 3);
                assert_eq!(
                    factors
                        .iter()
                        .map(|factor| factor.paths.len())
                        .sum::<usize>(),
                    3
                );
                for assignment in 0..16 {
                    let mono = |m: &KernelMonomial| {
                        m.variables().all(|v| {
                            assignment & (1 << names.iter().position(|n| n == v).unwrap()) != 0
                        })
                    };
                    let guard = |term: &WorkingTerm| {
                        term.constraints
                            .iter()
                            .all(|row| !row.terms().fold(false, |value, m| value ^ mono(m)))
                    };
                    assert_eq!(guard(&source), factors.iter().all(guard));
                    let phase = |term: &WorkingTerm| {
                        term.phase
                            .terms()
                            .filter(|(m, _)| mono(m))
                            .fold(integer(0), |p, (_, c)| p + c.as_rational().unwrap())
                    };
                    assert_eq!(
                        phase(&source),
                        factors.iter().map(phase).sum::<BigRational>()
                    );
                    assert_eq!(factors[0].coefficient, rational(3));
                    assert!(
                        factors[1..]
                            .iter()
                            .all(|factor| factor.coefficient == rational(1))
                    );
                }
                let mut refused = source;
                refused
                    .constraints
                    .resize(65, KernelBooleanPolynomial::zero());
                if refused
                    .constraints
                    .iter()
                    .any(|row| row.variables().iter().any(KernelVariable::is_bound_path))
                {
                    assert!(factor_phase_sums(&refused).is_none());
                }
            }
        }
    }

    #[test]
    fn guarded_factorization_charges_combined_phase_and_guard_syntax() {
        let a = KernelVariable::PathKet { term: 0, path: 0 };
        let b = KernelVariable::PathBra { term: 0, path: 0 };
        let mut source = WorkingTerm {
            paths: BTreeSet::from([a.clone(), b]),
            constraints: vec![variable(a)],
            coefficient: rational(3),
            phase: KernelPhasePolynomial::default(),
        };
        for i in 0..5000 {
            source.phase.add_boolean(
                &variable(KernelVariable::InputKet(i)),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        let factors = factor_phase_sums(&source).unwrap();
        assert_eq!(factors.len(), 3);
        assert_eq!(factors[0].phase, source.phase);
        assert_eq!(factors[0].coefficient, source.coefficient);
        assert_eq!(
            factors
                .iter()
                .flat_map(|factor| factor.constraints.iter())
                .collect::<Vec<_>>(),
            source.constraints.iter().collect::<Vec<_>>()
        );
        assert_eq!(
            factors
                .iter()
                .flat_map(|factor| factor.paths.iter().cloned())
                .collect::<BTreeSet<_>>(),
            source.paths
        );
        let mut high_degree = source;
        high_degree.phase = KernelPhasePolynomial::default();
        let common = (0..7).fold(KernelBooleanPolynomial::one(), |p, i| {
            p.and(&variable(KernelVariable::InputBra(i)))
        });
        for i in 0..4096 {
            high_degree.phase.add_boolean(
                &common.and(&variable(KernelVariable::InputKet(i))),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        // Fewer terms than the admitted source, but >32768 actual cells.
        assert!(factor_phase_sums(&high_degree).is_none());
    }

    #[test]
    fn factorization_shares_split_and_product_budgets_and_refuses_partial_results() {
        for (splits, products) in [(2, MAX_FACTOR_PRODUCTS), (MAX_RESIDUAL_SPLITS, 2)] {
            let mut aggregate = reduce_kernel(&kernel(vec![term(7)])).unwrap();
            let mut atoms = 1;
            let mut budget = ReductionBudget {
                splits,
                products,
                phase_cells: MAX_FACTOR_PHASE_CELLS,
            };
            assert!(
                accumulate_reduction(
                    reduce_term(&eighth_turn_residual(3)),
                    &mut aggregate,
                    &mut atoms,
                    &mut budget,
                    0
                )
                .is_none()
            );
        }
        let mut budget = ReductionBudget {
            splits: 0,
            products: 1,
            phase_cells: MAX_FACTOR_PHASE_CELLS,
        };
        let single = reduce_kernel(&kernel(vec![term(3)])).unwrap();
        assert!(multiply_aggregates(single.clone(), single.clone(), &mut budget).is_some());
        assert_eq!(budget.products, 0);
        assert!(multiply_aggregates(single.clone(), single, &mut budget).is_none());
    }

    #[test]
    fn factor_phase_copy_budget_refuses_before_convolution() {
        let mut phased = term(1);
        phased.phase.ket.add_boolean(
            &variable(KernelVariable::InputKet(0)),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        let source = reduce_kernel(&kernel(vec![phased])).unwrap();
        let mut budget = ReductionBudget {
            splits: 0,
            products: 10,
            phase_cells: 3,
        };
        // Each of the two operands contributes one phase term and one variable.
        assert!(multiply_aggregates(source.clone(), source.clone(), &mut budget).is_none());
        budget.phase_cells = 4;
        assert!(multiply_aggregates(source.clone(), source.clone(), &mut budget).is_some());
        assert_eq!(budget.phase_cells, 0);
        assert!(multiply_aggregates(source.clone(), source, &mut budget).is_none());
    }

    #[test]
    fn residual_depth_refusal_does_not_return_a_partial_aggregate() {
        let too_large = kernel(vec![
            term(7),
            weighted_eighth_turn_residual(MAX_SPLIT_DEPTH + 1),
        ]);
        assert!(reduce_kernel(&too_large).is_none());
        assert!(!exact_aggregate_match(&too_large, &kernel(vec![term(7)])));
    }

    #[test]
    fn residual_split_budget_is_shared_across_component_terms() {
        assert!(reduce_kernel(&kernel(vec![weighted_eighth_turn_residual(8)])).is_some());
        assert!(
            reduce_kernel(&kernel(vec![
                weighted_eighth_turn_residual(8),
                eighth_turn_residual(1)
            ]))
            .is_none()
        );
    }

    #[test]
    fn phase_lift_budget_uses_modular_denominator_degree() {
        let half = crate::symbolic::PhaseCoefficient::rational(ratio(1, 2));
        let quarter = crate::symbolic::PhaseCoefficient::rational(ratio(1, 4));
        let eighth = crate::symbolic::PhaseCoefficient::rational(ratio(1, 8));

        assert_eq!(lifted_boolean_term_bound(1_000, &half), Some(1_000));
        assert_eq!(lifted_boolean_term_bound(446, &quarter), Some(99_681));
        assert_eq!(lifted_boolean_term_bound(447, &quarter), None);
        assert_eq!(lifted_boolean_term_bound(50, &eighth), Some(20_875));
        assert_eq!(lifted_boolean_term_bound(100, &eighth), None);
    }

    #[test]
    fn constraint_span_recovers_a_small_pivot_before_refusing_large_expansion() {
        let path = KernelVariable::PathKet { term: 0, path: 0 };
        let output = variable(KernelVariable::QuantumOutputKet(0));
        let expression = (0..100).fold(KernelBooleanPolynomial::zero(), |sum, index| {
            sum.xor(
                &variable(KernelVariable::InputKet(index))
                    .and(&variable(KernelVariable::InputKet(index + 100))),
            )
        });
        let mut left = term(1);
        left.ket_paths.insert(path.clone());
        left.ket_guard = vec![
            variable(path.clone()).xor(&expression),
            output.xor(&expression),
        ];
        left.phase.ket.add_boolean(
            &variable(path),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        assert!(
            lifted_boolean_term_bound(
                expression.term_count(),
                &crate::symbolic::PhaseCoefficient::rational(ratio(1, 8))
            )
            .is_none()
        );
        let mut right = term(1);
        right.ket_guard = vec![output.xor(&expression)];
        right.phase.ket.add_boolean(
            &output,
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        assert!(exact_aggregate_match(
            &kernel(vec![left]),
            &kernel(vec![right])
        ));
    }

    #[test]
    fn stalled_nonlinear_rows_expose_unique_paths_without_shannon_enumeration() {
        let mut left = term(1);
        let mut right = term(1);
        for index in 0..9 {
            let path = KernelVariable::PathKet {
                term: 0,
                path: index,
            };
            let a = variable(KernelVariable::InputKet(3 * index));
            let b = variable(KernelVariable::InputKet(3 * index + 1));
            let c = variable(KernelVariable::InputKet(3 * index + 2));
            let equation = a.and(&variable(path.clone())).xor(&b);
            left.ket_guard.push(equation.clone());
            left.ket_guard
                .push(equation.xor(&variable(path.clone())).xor(&c));
            left.phase.ket.add_boolean(
                &variable(path.clone()),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
            );
            left.ket_paths.insert(path);
            right.ket_guard.push(a.and(&c).xor(&b));
            right
                .phase
                .ket
                .add_boolean(&c, crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)));
        }
        // Each original row contains its path only nonlinearly or also in
        // a nonlinear monomial. Row addition exposes v=c for all nine paths.
        assert!(matches!(reduce_term(&left), Reduction::Exact(_)));
        assert!(exact_aggregate_match(
            &kernel(vec![left]),
            &kernel(vec![right])
        ));
    }

    #[test]
    fn bounded_phase_recovery_preserves_selectors_multiplicity_and_weight_dependence() {
        let value = KernelVariable::PathKet { term: 0, path: 0 };
        let fourier = KernelVariable::PathBra { term: 0, path: 0 };
        let definition = (0..100).fold(KernelBooleanPolynomial::zero(), |sum, index| {
            sum.xor(
                &variable(KernelVariable::InputKet(2 * index))
                    .and(&variable(KernelVariable::InputKet(2 * index + 1))),
            )
        });
        let mut left = term(1);
        left.ket_paths.insert(value.clone());
        left.bra_paths.insert(fourier.clone());
        left.ket_guard
            .push(variable(value.clone()).xor(&definition));
        left.phase.ket.add_boolean(
            &variable(value.clone()),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        left.phase.ket.add_boolean(
            &variable(value).and(&variable(fourier.clone())),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
        let mut right = term(2);
        right.ket_guard.push(definition);
        // sum_w (-1)^(wv) imposes v=0 before v's large definition needs
        // arithmetic lifting. The remaining exact selector is F=0. This is
        // now a bounded recovery case; unrestricted phase-first recovery
        // remains disabled after its earlier real-case runtime regression.
        assert!(exact_aggregate_match(
            &kernel(vec![left.clone()]),
            &kernel(vec![right.clone()])
        ));
        let mut with_absent = left.clone();
        with_absent
            .ket_paths
            .extend((1..=3).map(|path| KernelVariable::PathKet { term: 0, path }));
        right.weight.ket = rational(16);
        assert!(exact_aggregate_match(
            &kernel(vec![with_absent]),
            &kernel(vec![right])
        ));
        let mut too_many_paths = left.clone();
        too_many_paths.ket_paths.extend(
            (1..=MAX_DEFERRED_PHASE_PATHS).map(|path| KernelVariable::PathKet { term: 0, path }),
        );
        assert!(matches!(reduce_term(&too_many_paths), Reduction::Residual));
        let mut exhausted_probes = left.clone();
        exhausted_probes.ket_paths.extend(
            (1..=MAX_DEFERRED_PHASE_PROBES).map(|path| KernelVariable::PathKet { term: 0, path }),
        );
        assert!(matches!(
            reduce_term(&exhausted_probes),
            Reduction::Residual
        ));
        let mut too_many_terms = left.clone();
        for index in 0..MAX_DEFERRED_PHASE_TERMS {
            too_many_terms.phase.ket.add_boolean(
                &variable(KernelVariable::InputKet(1000 + index)),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        assert!(matches!(reduce_term(&too_many_terms), Reduction::Residual));
        // A weight depending on w prevents that Fourier rule. It must not be
        // dropped simply because the direct v substitution does not fit.
        left.weight.bra = KernelScalar::Select {
            condition: variable(fourier),
            when_true: Box::new(rational(3)),
            when_false: Box::new(rational(5)),
        };
        assert!(matches!(reduce_term(&left), Reduction::Residual));
    }

    #[test]
    fn a_refused_early_span_probe_does_not_block_late_small_exact_recovery() {
        let mut left = term(1);
        for index in 0..400 {
            let path = KernelVariable::PathKet {
                term: 0,
                path: index,
            };
            let definition = (0..65).fold(KernelBooleanPolynomial::zero(), |sum, offset| {
                let input = 2 * (65 * index + offset);
                sum.xor(
                    &variable(KernelVariable::InputKet(input))
                        .and(&variable(KernelVariable::InputKet(input + 1))),
                )
            });
            left.ket_guard.push(variable(path.clone()).xor(&definition));
            left.ket_paths.insert(path);
        }
        let path = KernelVariable::PathKet { term: 0, path: 400 };
        let output = variable(KernelVariable::QuantumOutputKet(0));
        let definition = (0..100).fold(KernelBooleanPolynomial::zero(), |sum, offset| {
            sum.xor(
                &variable(KernelVariable::InputBra(2 * offset))
                    .and(&variable(KernelVariable::InputBra(2 * offset + 1))),
            )
        });
        left.ket_guard.extend([
            variable(path.clone()).xor(&definition),
            output.xor(&definition),
        ]);
        left.ket_paths.insert(path.clone());
        left.phase.ket.add_boolean(
            &variable(path),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        assert!(matches!(
            normalize_constraint_span(&mut left.ket_guard.clone()),
            ConstraintNormalization::BudgetExceeded
        ));
        let mut right = term(1);
        right.ket_guard.push(output.xor(&definition));
        right.phase.ket.add_boolean(
            &output,
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
        // The 400 cheap unique definitions disappear without a matrix. Only
        // then does the small remaining span expose the safe literal pivot.
        assert!(exact_aggregate_match(
            &kernel(vec![left]),
            &kernel(vec![right])
        ));
    }

    #[test]
    fn initial_alias_compaction_must_reenter_original_representation_budget() {
        let bound = KernelVariable::PathKet { term: 0, path: 0 };
        let free = KernelVariable::InputKet(0);
        let guard = variable(KernelVariable::InputBra(0));
        let mut source = WorkingTerm {
            paths: BTreeSet::from([bound.clone()]),
            constraints: vec![
                variable(bound.clone()).xor(&variable(free.clone())),
                guard.clone(),
            ],
            coefficient: rational(3),
            phase: KernelPhasePolynomial::default(),
        };
        for index in 1..=50_001 {
            let x = variable(KernelVariable::InputKet(index));
            source.phase.add_boolean(
                &variable(bound.clone()).and(&x),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
            );
            source.phase.add_boolean(
                &variable(free.clone()).and(&x),
                crate::symbolic::PhaseCoefficient::rational(ratio(7, 8)),
            );
        }
        assert_eq!(source.phase.term_count(), 100_002);
        assert!(!source.within_budget());
        assert!(source.initial_alias_compaction_within_budget());
        let Reduction::Exact(result) = reduce_working_term(source.clone()) else {
            panic!("unique bound alias must compact before the original cap");
        };
        assert_eq!(result.phase.term_count(), 0);
        assert_eq!(result.coefficient, rational(3));
        assert_eq!(result.constraints, vec![guard]);

        // Merely equal free-looking coordinates cannot be identified or
        // canceled: the oversized phase must still refuse after the probe.
        source.paths.clear();
        assert!(matches!(
            reduce_working_term(source.clone()),
            Reduction::Residual
        ));
        // A high-degree encoding can exceed the independent syntax entrance
        // even when it is below the compaction-only 200000-term admission.
        let mut high = KernelBooleanPolynomial::one();
        for index in 50_002..50_010 {
            high = high.and(&variable(KernelVariable::InputKet(index)));
        }
        source.phase = KernelPhasePolynomial::default();
        for index in 1..=100_001 {
            source.phase.add_boolean(
                &high.and(&variable(KernelVariable::InputBra(index))),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        assert!(!source.initial_alias_compaction_within_budget());
        assert!(matches!(reduce_working_term(source), Reduction::Residual));
    }

    #[test]
    fn literal_alias_batch_preserves_every_free_kernel_entry_and_weight() {
        fn entries(
            source: &WorkingTerm,
            free: &[(KernelVariable, bool)],
        ) -> BTreeMap<KernelPhasePolynomial, BigRational> {
            let paths = source.paths.iter().cloned().collect::<Vec<_>>();
            let mut result = BTreeMap::new();
            for bits in 0..(1usize << paths.len()) {
                let mut instance = source.clone();
                for (variable, value) in free.iter().cloned().chain(
                    paths
                        .iter()
                        .enumerate()
                        .map(|(index, path)| (path.clone(), bits & (1 << index) != 0)),
                ) {
                    instance.substitute(&variable, &KernelBooleanPolynomial::from(value));
                }
                if instance.constraints.iter().any(|value| !value.is_zero()) {
                    assert!(
                        instance
                            .constraints
                            .iter()
                            .all(|v| v.is_zero() || v.is_one())
                    );
                    continue;
                }
                let KernelScalar::Rational(weight) = normalize_scalar(instance.coefficient) else {
                    panic!("the fully assigned test weight must be rational")
                };
                *result.entry(instance.phase).or_insert_with(|| integer(0)) += weight;
            }
            result.retain(|_, value| value != &integer(0));
            result
        }

        let ket = KernelVariable::PathKet { term: 0, path: 0 };
        let bra = KernelVariable::PathBra { term: 0, path: 0 };
        let other = KernelVariable::PathKet { term: 1, path: 0 };
        let free = [
            KernelVariable::InputKet(0),
            KernelVariable::InputBra(0),
            KernelVariable::QuantumOutputKet(0),
            KernelVariable::QuantumOutputBra(0),
            KernelVariable::ClassicalOutput(0),
        ];
        let product = variable(ket.clone()).and(&variable(other.clone()));
        let condition = variable(other.clone()).and(&variable(free[4].clone()));
        let mut phase = KernelPhasePolynomial::default();
        for (value, coefficient) in [
            (product.clone(), ratio(1, 8)),
            (variable(bra.clone()), ratio(1, 8)),
            (variable(free[0].clone()), ratio(-1, 4)),
        ] {
            phase.add_boolean(
                &value,
                crate::symbolic::PhaseCoefficient::rational(coefficient),
            );
        }
        let source = WorkingTerm {
            paths: BTreeSet::from([ket.clone(), bra.clone(), other.clone()]),
            constraints: vec![
                affine([ket.clone(), bra.clone()]),
                affine([bra.clone(), other.clone()]),
                affine([other.clone(), free[0].clone()]),
                affine([ket.clone(), free[1].clone()]),
                variable(free[2].clone()).xor(&condition),
                affine([free[3].clone(), free[1].clone()]),
                product.xor(&variable(bra.clone())),
            ],
            coefficient: KernelScalar::Select {
                condition: affine([ket, bra]),
                when_true: Box::new(rational(13)),
                when_false: Box::new(KernelScalar::Select {
                    condition,
                    when_true: Box::new(rational(3)),
                    when_false: Box::new(rational(5)),
                }),
            },
            phase,
        };
        let mut renamed = source.clone();
        renamed.eliminate_literal_aliases();
        assert!(renamed.paths.is_empty());
        assert_eq!(renamed.phase.term_count(), 0);
        assert!(
            renamed
                .constraints
                .contains(&affine([free[0].clone(), free[1].clone()]))
        );
        for bits in 0..(1usize << free.len()) {
            let assignment = free
                .iter()
                .enumerate()
                .map(|(index, variable)| (variable.clone(), bits & (1 << index) != 0))
                .collect::<Vec<_>>();
            assert_eq!(
                entries(&source, &assignment),
                entries(&renamed, &assignment)
            );
        }
    }

    #[test]
    fn literal_alias_cycles_keep_one_binder_and_do_not_hide_contradictions() {
        let paths = [
            KernelVariable::PathKet { term: 0, path: 0 },
            KernelVariable::PathBra { term: 0, path: 0 },
            KernelVariable::PathKet { term: 1, path: 0 },
        ];
        let mut source = term(1);
        source
            .ket_paths
            .extend([paths[0].clone(), paths[2].clone()]);
        source.bra_paths.insert(paths[1].clone());
        source.ket_guard = vec![
            affine([paths[0].clone(), paths[1].clone()]),
            affine([paths[1].clone(), paths[2].clone()]),
            affine([paths[2].clone(), paths[0].clone()]),
        ];
        assert!(exact_aggregate_match(
            &kernel(vec![source.clone()]),
            &kernel(vec![term(2)])
        ));
        assert!(!exact_aggregate_match(
            &kernel(vec![source.clone()]),
            &kernel(vec![term(1)])
        ));
        source
            .ket_guard
            .push(affine([paths[0].clone(), paths[2].clone()]).complement());
        assert!(matches!(reduce_term(&source), Reduction::Zero));

        let mut unbound = WorkingTerm {
            paths: BTreeSet::new(),
            constraints: vec![affine([paths[0].clone(), paths[1].clone()])],
            coefficient: rational(1),
            phase: KernelPhasePolynomial::default(),
        };
        let original = unbound.constraints.clone();
        unbound.eliminate_literal_aliases();
        assert_eq!(unbound.constraints, original);
    }

    #[test]
    fn sparse_unique_pivots_do_not_require_an_initial_dense_matrix() {
        let mut left = term(1);
        for index in 0..2240 {
            let path = KernelVariable::PathKet {
                term: 0,
                path: index,
            };
            left.ket_paths.insert(path.clone());
            left.ket_guard
                .push(variable(path).xor(&variable(KernelVariable::InputKet(index))));
        }
        assert!(left.ket_guard.len() * left.ket_paths.len() * 2 > MAX_AFFINE_MATRIX_CELLS);
        let mut working = WorkingTerm {
            constraints: left.ket_guard.clone(),
            paths: left.ket_paths.clone(),
            coefficient: rational(1),
            phase: KernelPhasePolynomial::default(),
        };
        let before = working.constraints.clone();
        assert!(matches!(
            working.normalize_constraints(),
            ConstraintNormalization::BudgetExceeded
        ));
        assert_eq!(working.constraints, before);
        // The failed optional normalization left the original complete
        // equations available, each with exactly one bound solution.
        assert!(exact_aggregate_match(
            &kernel(vec![left]),
            &kernel(vec![term(1)])
        ));
    }

    #[test]
    fn alternative_pivot_probes_are_bounded_read_only_and_preflighted() {
        let p = KernelVariable::PathKet { term: 0, path: 0 };
        let q = KernelVariable::PathKet { term: 0, path: 1 };
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(
            &variable(p.clone()),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 1 << 20)),
        );
        let working = WorkingTerm {
            paths: BTreeSet::from([p.clone(), q.clone()]),
            constraints: vec![
                variable(p.clone()).xor(&affine((0..17).map(KernelVariable::InputKet))),
                variable(q.clone()).xor(&affine((17..35).map(KernelVariable::InputKet))),
            ],
            coefficient: rational(1),
            phase,
        };
        let before = working.clone();
        let first = working.best_constraint_pivot().unwrap();
        assert_eq!(first.0, p);
        assert!(!working.substitution_within_budget(&first.0, &first.1));
        let mut probes = 1;
        assert!(working.budget_safe_constraint_pivot(&mut probes).is_none());
        assert_eq!(probes, 0);
        let mut probes = 2;
        let alternative = working.budget_safe_constraint_pivot(&mut probes).unwrap();
        assert_eq!(alternative.0, q);
        assert_eq!(
            alternative.1,
            affine((17..35).map(KernelVariable::InputKet))
        );
        assert_eq!(probes, 0);
        assert!(working.budget_safe_constraint_pivot(&mut probes).is_none());
        assert_eq!(working.constraints, before.constraints);
        assert_eq!(working.paths, before.paths);
        assert_eq!(working.phase, before.phase);
        assert_eq!(working.coefficient, before.coefficient);
    }

    #[test]
    fn oversized_pivot_does_not_hide_a_later_zero_fourier_sum() {
        let p = KernelVariable::PathKet { term: 0, path: 0 };
        let q = KernelVariable::PathKet { term: 0, path: 1 };
        let mut source = term(1);
        source.ket_paths = BTreeSet::from([p.clone(), q.clone()]);
        source.ket_guard =
            vec![variable(p.clone()).xor(&affine((0..17).map(KernelVariable::InputKet)))];
        source.phase.ket.add_boolean(
            &variable(p),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 1 << 20)),
        );
        source.phase.ket.add_boolean(
            &variable(q.clone()),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
        // For every free input, the independent q sum is 1 + (-1) = 0.
        assert!(matches!(reduce_term(&source), Reduction::Zero));
        source
            .phase
            .ket
            .substitute(&q, &KernelBooleanPolynomial::zero());
        // An unused q contributes 2, not 0; the unsafe p remains a refusal.
        assert!(matches!(reduce_term(&source), Reduction::Residual));
    }

    #[test]
    fn oversized_omega_does_not_hide_a_later_zero_fourier_sum() {
        let p = KernelVariable::PathKet { term: 0, path: 0 };
        let q = KernelVariable::PathKet { term: 0, path: 1 };
        let mut source = term(1);
        source.ket_paths = BTreeSet::from([p.clone(), q.clone()]);
        source.phase.ket.add_boolean(
            &variable(p.clone()),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 4)),
        );
        for input in 0..447 {
            source.phase.ket.add_boolean(
                &variable(p.clone()).and(&variable(KernelVariable::InputKet(input))),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
            );
        }
        source.phase.ket.add_boolean(
            &variable(q.clone()),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
        );
        assert!(matches!(reduce_term(&source), Reduction::Zero));
        source
            .phase
            .ket
            .substitute(&q, &KernelBooleanPolynomial::zero());
        assert!(matches!(reduce_term(&source), Reduction::Residual));
    }

    #[test]
    fn omega_rule_rejects_large_parity_before_lifting() {
        let mut residual = term(1);
        let path = KernelVariable::PathKet { term: 0, path: 0 };
        let path_polynomial = KernelBooleanPolynomial::variable(path.clone());
        residual.ket_paths.insert(path);
        residual.phase.ket.add_boolean(
            &path_polynomial,
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 4)),
        );
        for input in 0..447 {
            let product = path_polynomial.and(&KernelBooleanPolynomial::variable(
                KernelVariable::InputKet(input),
            ));
            residual.phase.ket.add_boolean(
                &product,
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
            );
        }

        assert!(matches!(reduce_term(&residual), Reduction::Residual));
    }

    #[test]
    fn affine_rref_refuses_a_matrix_beyond_its_work_budget() {
        let width = 3_163usize;
        assert!(width * width > MAX_AFFINE_MATRIX_CELLS);
        let mut residual = term(1);
        residual.ket_guard = (0..width)
            .map(|input| variable(KernelVariable::InputKet(input)))
            .collect();

        assert!(matches!(reduce_term(&residual), Reduction::Residual));
    }
}
