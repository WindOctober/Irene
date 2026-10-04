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

mod checkpoint;
mod checkpoint_factors;
mod collection;
mod constraint_rows;
mod constraints;
mod exact_affine_pivot;
mod exact_guard_pivot;
mod exact_smt;
mod exact_trig;
mod factor_match;
mod factor_normalize;
mod factor_pair;
mod factor_rectangle;
mod factor_refine;
mod factor_relation;
mod factored;
mod factorization;
mod free_split;
#[cfg(test)]
mod local_reducer_tests;
mod pair_period;
mod path_sum;
mod phase_schedule;
mod phase_unit;
mod product_cases;
mod product_form;
mod scalar;
mod shannon;
mod small_sum;

use collection::{
    ExactAggregate, ExactEntry, ExactTerm, accumulate_exact_term, aggregate_difference,
};
use free_split::{remove_common_phase, restrict_aggregate};
use scalar::{normalize_scalar, scalar_conditions_within_budget, scalar_within_budget};
mod phase_basis;

mod conditioning;
mod graph;
mod vacuous;
mod witness;
mod xor_basis;
mod xor_blocks;
mod zero_product;

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
    factor_refine::tensor(source, MAX_FACTOR_PHASE_CELLS, |l, r| {
        multiply_aggregates(l, r, budget)
    })
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
    free_split::prove_zero(
        difference,
        budget,
        depth,
        MAX_FREE_SPLIT_DEPTH,
        &mut |source| witness::constant_is_zero(source, algebra),
    )
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
            shannon::claim_split(&mut budget.splits, depth, depth_limit)?;
            let variable = term.residual_split_variable()?;
            return shannon::visit_bound_cofactors(
                &term,
                &variable,
                |replacement| term.substitution_within_budget(&variable, replacement),
                |child| {
                    accumulate_reduction_with_depth(
                        reduce_working_term(child),
                        aggregate,
                        atoms,
                        budget,
                        depth + 1,
                        depth_limit,
                    )
                },
            );
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
    factorization::factor(term, guard_phase_cells)
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
    factorization::multiply(
        left,
        right,
        &mut budget.products,
        &mut budget.phase_cells,
        |term| match reduce_working_term(term) {
            Reduction::Zero => Some(None),
            Reduction::Exact(exact) => Some(Some(exact)),
            _ => None,
        },
    )
}

fn reduce_term(term: &KernelTerm) -> Reduction {
    reduce_working_term(working_term(term))
}

fn working_term(term: &KernelTerm) -> WorkingTerm {
    let mut working = WorkingTerm::from_kernel(term);
    working.coefficient = normalize_scalar(working.coefficient);
    working
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
            let profile = term.phase_sum_profile(&variable);
            if let Some(additions) = profile.omega_additions()
                && !term
                    .phase_rewrite_within_budget(&variable, additions.iter().map(|(p, c)| (p, c)))
            {
                debug_term("omega-lift-budget-postponed", &term);
                local_budget_refused = true;
                continue;
            }
            let Some(factor) = profile.apply(&mut term, &variable) else {
                continue;
            };
            term.remove_summed_path(&variable, factor);
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
                if let Some(checkpoint) = checkpoint {
                    debug_term("whole-term-checkpoint", &term);
                    *checkpoint = self::checkpoint::capture(term);
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

fn integer(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn ratio(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

#[cfg(test)]
mod tests;
