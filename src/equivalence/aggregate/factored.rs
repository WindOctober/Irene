//! EQ-only certificates for products of independently bound phase sums.
//!
//! Keep the common selector, real scalar and phase, and prove a complete
//! bijection of the remaining exact factors. Never infer NEQ from failure or
//! drop a factor that refused reduction. No full product is expanded.

use super::*;

mod rectangle;
mod small_sum;

const MAX_FACTORS: usize = 128;
const MAX_FACTOR_ATOMS: usize = 256;
const MAX_STORED_ATOMS: usize = 4096;
const MAX_MATCH_PROBES: usize = 128;
const MAX_PRODUCT_SPLIT_DEPTH: usize = 4;
const MAX_INPUT_PATHS: usize = 256;
const MAX_INPUT_PHASE_TERMS: usize = 65536;
const MAX_INPUT_CELLS: usize = MAX_FACTOR_PHASE_CELLS;
// A three-bit orientation can expand a small R into eight copies in L.
// Keep its admission separate from atom count and charge actual syntax at
// every proof-tree node against the unchanged shared phase-cell budget.
const MAX_ORIENTATION_LEFT_TERMS: usize = 512;

#[derive(Clone)]
struct Product {
    common: ExactAggregate,
    factors: Vec<ExactAggregate>,
}

pub(super) fn matches(left: &Reduction, right: &Reduction) -> bool {
    if let (Reduction::Sum(sum), Reduction::Exact(exact))
    | (Reduction::Exact(exact), Reduction::Sum(sum)) = (left, right)
    {
        return collapsed_product_equal(sum, exact);
    }
    let (Reduction::Sum(left), Reduction::Sum(right)) = (left, right) else {
        return false;
    };
    if !eligible(left) || !eligible(right) {
        return false;
    }
    let mut reduction = ReductionBudget {
        splits: 4095,
        products: MAX_FACTOR_PRODUCTS,
        phase_cells: MAX_FACTOR_PHASE_CELLS,
    };
    let Some(left) = product(left, &mut reduction) else {
        return false;
    };
    let Some(right) = product(right, &mut reduction) else {
        return false;
    };
    compare_products(left, right, &mut reduction)
}

/// Consume COMPLETE disconnected factors already constructed by the bounded
/// phase compactor. Each local input is small; no monolithic phase is rebuilt
/// or readmitted through an enlarged original factor entrance. All final
/// reduction/storage/matching limits and the zero-product obligation remain.
pub(super) fn matches_components(left: Vec<WorkingTerm>, right: Vec<WorkingTerm>) -> bool {
    matches_components_refined(left, right, false)
}

/// Keep the certified rectangle schedule after an oversized component was
/// exactly compacted. This flag selects a proof algorithm, never a premise.
pub(super) fn matches_components_refined(
    left: Vec<WorkingTerm>,
    right: Vec<WorkingTerm>,
    prefer_rectangles: bool,
) -> bool {
    fn admitted(factors: &[WorkingTerm]) -> bool {
        if factors.is_empty() || factors.len() > MAX_FACTORS + 1 || !factors[0].paths.is_empty() {
            return false;
        }
        let mut names = BTreeSet::new();
        let mut total_cells = 0usize;
        for factor in factors {
            if factor.paths.len() > MAX_SPLIT_DEPTH
                || factor.constraints.len() > 64
                || !factor.within_budget()
                || factor
                    .paths
                    .iter()
                    .any(|v| !v.is_bound_path() || !names.insert(v.clone()))
            {
                return false;
            }
            let mut cells = 0usize;
            let mut inspect = |m: &KernelMonomial| {
                cells += 1 + m.variables().count();
                cells <= 100000
                    && m.variables()
                        .all(|v| !v.is_bound_path() || factor.paths.contains(v))
            };
            if !factor
                .constraints
                .iter()
                .all(|row| row.terms().all(&mut inspect))
                || !factor.phase.terms().all(|(m, _)| inspect(m))
                || !scalar_conditions_within_budget(&factor.coefficient, |row| {
                    row.terms().all(&mut inspect)
                })
            {
                return false;
            }
            if cells > 32768 && !small_sum::admitted(factor) {
                return false;
            }
            total_cells += cells + factor.paths.len();
            if total_cells > 750000 || names.len() > MAX_INPUT_PATHS {
                return false;
            }
        }
        true
    }
    if !admitted(&left) || !admitted(&right) {
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            for (side, factors) in [("left", &left), ("right", &right)] {
                eprintln!(
                    "aggregate component entrance refused {side}: {:?}",
                    factors
                        .iter()
                        .take(MAX_FACTORS + 2)
                        .map(|f| (f.paths.len(), f.constraints.len(), f.phase.term_count()))
                        .collect::<Vec<_>>()
                );
            }
        }
        return false;
    }
    let mut reduction = ReductionBudget {
        splits: 4095,
        products: MAX_FACTOR_PRODUCTS,
        phase_cells: MAX_FACTOR_PHASE_CELLS,
    };
    let Some(left) = product_from_factors_using(left, &mut reduction, true, prefer_rectangles)
    else {
        return false;
    };
    let Some(right) = product_from_factors_using(right, &mut reduction, true, prefer_rectangles)
    else {
        return false;
    };
    compare_products(left, right, &mut reduction)
}

fn compare_products(left: Product, right: Product, reduction: &mut ReductionBudget) -> bool {
    let mut free_splits = MAX_FREE_SPLITS;
    let mut algebra = witness::ConstantBudget::default();
    let mut probes = MAX_MATCH_PROBES;
    equal_products(
        left,
        right,
        reduction,
        &mut free_splits,
        &mut algebra,
        &mut probes,
        0,
    )
}

/// All leaves, not selected points: reconstruct a single phase function by
/// Boolean interpolation only when every leaf has the SAME positive rational
/// magnitude. Preserve the source's identical selector outside this proof.
fn collapse_phase_unit(
    source: &ExactAggregate,
    reduction: &mut ReductionBudget,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
) -> Option<ExactAggregate> {
    if source.len() != 1 {
        return None;
    }
    charge_cells(source, &mut reduction.phase_cells)?;
    let (entry, coefficients) = source.first_key_value()?;
    let mut variables = BTreeSet::new();
    for (phase, scalar) in coefficients {
        variables.extend(phase.variables());
        if !scalar_conditions_within_budget(scalar, |condition| {
            variables.extend(condition.variables());
            variables.len() <= 8
        }) {
            return None;
        }
    }
    if variables.len() > 8 || variables.iter().any(KernelVariable::is_bound_path) {
        return None;
    }
    let unguarded = BTreeMap::from([(
        ExactEntry {
            constraints: Vec::new(),
        },
        coefficients.clone(),
    )]);
    let (scalar, phase) = interpolate_phase_unit(
        unguarded,
        &variables.into_iter().collect::<Vec<_>>(),
        reduction,
        free,
        algebra,
    )?;
    let mut result = ExactAggregate::new();
    accumulate_exact_term(
        ExactTerm {
            constraints: entry.constraints.clone(),
            coefficient: KernelScalar::Rational(scalar),
            phase,
        },
        &mut result,
        &mut 0,
    )?;
    Some(result)
}

fn interpolate_phase_unit(
    source: ExactAggregate,
    variables: &[KernelVariable],
    reduction: &mut ReductionBudget,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
) -> Option<(BigRational, KernelPhasePolynomial)> {
    charge_cells(&source, &mut reduction.phase_cells)?;
    let Some((variable, rest)) = variables.split_first() else {
        let (scalar, turns) = witness::constant_monomial(&source, algebra)?;
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(
            &KernelBooleanPolynomial::one(),
            crate::symbolic::PhaseCoefficient::rational(turns),
        );
        return Some((scalar, phase));
    };
    *free = free.checked_sub(1)?;
    let (a, mut p) = interpolate_phase_unit(
        restrict_aggregate(&source, variable, false)?,
        rest,
        reduction,
        free,
        algebra,
    )?;
    let (b, q) = interpolate_phase_unit(
        restrict_aggregate(&source, variable, true)?,
        rest,
        reduction,
        free,
        algebra,
    )?;
    if a != b {
        return None;
    }
    // p + x*(q-p), modulo full turns, equals the entire phase function
    // on both Boolean branches. Multiplication uses only the literal x.
    charge_phase(&p, reduction)?;
    charge_phase(&q, reduction)?;
    let difference = KernelPhasePolynomial::difference(&q, &p);
    let literal = KernelBooleanPolynomial::variable(variable.clone());
    for (monomial, coefficient) in difference.terms() {
        reduction.phase_cells = reduction
            .phase_cells
            .checked_sub(2 + monomial.variables().count())?;
        p.add_boolean(
            &literal.and(&KernelBooleanPolynomial::from_monomial(monomial.clone())),
            coefficient.clone(),
        );
    }
    Some((a, p))
}

/// A residual product can equal an already-exact side without expanding its
/// convolution. Every small factor must completely collapse to a unit; no
/// zero factor is canceled and no residual/partial sum enters this route.
fn collapsed_product_equal(sum: &WorkingTerm, exact: &ExactTerm) -> bool {
    if !eligible(sum) {
        return false;
    }
    let Some(factors) = factor_phase_sums(sum) else {
        return false;
    };
    if factors.len() > MAX_FACTORS + 1 {
        return false;
    }
    let mut reduction = ReductionBudget {
        splits: MAX_RESIDUAL_SPLITS,
        products: MAX_FACTOR_PRODUCTS,
        phase_cells: MAX_FACTOR_PHASE_CELLS,
    };
    let mut free = MAX_FREE_SPLITS;
    let mut algebra = witness::ConstantBudget::default();
    let mut factors = factors.into_iter();
    let Some(common) = factors.next() else {
        return false;
    };
    let selector = common.constraints.clone();
    let mut product = ExactAggregate::new();
    if accumulate_reduction(
        reduce_working_term(common),
        &mut product,
        &mut 0,
        &mut reduction,
        0,
    )
    .is_none()
    {
        return false;
    }
    for mut factor in factors {
        if factor.paths.len() > MAX_SPLIT_DEPTH {
            return false;
        }
        factor.constraints.extend(selector.iter().cloned());
        let mut aggregate = ExactAggregate::new();
        if accumulate_reduction(
            reduce_working_term(factor),
            &mut aggregate,
            &mut 0,
            &mut reduction,
            0,
        )
        .is_none()
            || aggregate.values().map(BTreeMap::len).sum::<usize>() > MAX_FACTOR_ATOMS
        {
            return false;
        }
        let Some(unit) = collapse_phase_unit(&aggregate, &mut reduction, &mut free, &mut algebra)
        else {
            return false;
        };
        let Some(updated) = multiply_aggregates(product, unit, &mut reduction) else {
            return false;
        };
        product = updated;
    }
    let mut other = ExactAggregate::new();
    if accumulate_exact_term(exact.clone(), &mut other, &mut 0).is_none() {
        return false;
    }
    equal(&product, &other, &mut free, &mut algebra)
}

fn equal_products(
    left: Product,
    right: Product,
    reduction: &mut ReductionBudget,
    free_splits: &mut usize,
    algebra: &mut witness::ConstantBudget,
    probes: &mut usize,
    depth: usize,
) -> bool {
    let mut relevant = BTreeSet::new();
    if bijection(
        &left,
        &right,
        reduction,
        free_splits,
        algebra,
        (probes, &mut relevant),
    ) {
        return true;
    }
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate factored incomplete: depth={depth} probes={probes} free_splits={free_splits} phase_cells={} products={}",
            reduction.phase_cells, reduction.products
        );
    }
    if depth >= MAX_PRODUCT_SPLIT_DEPTH || *free_splits == 0 {
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
    *free_splits -= 1;
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!("aggregate factored cofactor: depth={depth} variable={variable:?}");
    }
    for value in [false, true] {
        let Some(l) = restrict_product(&left, &variable, value, reduction) else {
            return false;
        };
        let Some(r) = restrict_product(&right, &variable, value, reduction) else {
            return false;
        };
        if !equal_products(l, r, reduction, free_splits, algebra, probes, depth + 1) {
            return false;
        }
    }
    true
}

fn restrict_product(
    source: &Product,
    variable: &KernelVariable,
    value: bool,
    budget: &mut ReductionBudget,
) -> Option<Product> {
    let mut common = restrict_aggregate(&source.common, variable, value)?;
    let mut factors = Vec::new();
    for factor in &source.factors {
        charge_cells(factor, &mut budget.phase_cells)?;
        for factor in refine_tensor(restrict_aggregate(factor, variable, value)?, budget)? {
            if factor.is_empty() {
                return Some(Product {
                    common: ExactAggregate::new(),
                    factors: Vec::new(),
                });
            }
            let (factor, scalar, phase) = normalize_factor(factor)?;
            charge_cells(&factor, &mut budget.phase_cells)?;
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
            common = multiply_aggregates(common, unit, budget)?;
            // A fully reduced one-atom factor belongs in the common term.
            // Multiply it in with its selector; do not discard an indicator
            // merely because its scalar/phase normalized to one.
            if factor.values().map(BTreeMap::len).sum::<usize>() == 1 {
                common = multiply_aggregates(common, factor, budget)?;
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

fn bijection(
    left: &Product,
    right: &Product,
    reduction: &mut ReductionBudget,
    free_splits: &mut usize,
    algebra: &mut witness::ConstantBudget,
    search: (&mut usize, &mut BTreeSet<KernelVariable>),
) -> bool {
    let (probes, relevant) = search;
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate factored candidates: left={} right={} phase_cells={} products={}",
            left.factors.len(),
            right.factors.len(),
            reduction.phase_cells,
            reduction.products
        );
    }
    if right.factors.len() < left.factors.len() || right.factors.len() > left.factors.len() + 1 {
        return false;
    }
    let mut common = left.common.clone();
    let mut unit_scalar = integer(1);
    let mut unit_phase = KernelPhasePolynomial::default();
    let mut remaining = right.factors.iter().collect::<Vec<_>>();
    for (position, factor) in left.factors.iter().enumerate() {
        let mut matched = remaining.iter().position(|other| *other == factor);
        if matched.is_none()
            && remaining.len() > left.factors.len() - position
            && let Some((a, b, unit)) =
                matching_pair_unit(factor, &remaining, reduction, free_splits, algebra, probes)
        {
            if collect_unit(&unit, &mut unit_scalar, &mut unit_phase, reduction).is_none() {
                return false;
            }
            // Each right factor is consumed exactly once; the final
            // obligation still contains the entire original right product.
            remaining.remove(b);
            remaining.remove(a);
            continue;
        }
        if matched.is_none() {
            // Input support is usually a stable anchor across phase
            // orientation changes. Rank proposals, but never accept or
            // reject equality from support alone; prove every chosen pair.
            let support = |sum: &ExactAggregate| {
                sum.values()
                    .flat_map(BTreeMap::keys)
                    .flat_map(KernelPhasePolynomial::variables)
                    .collect::<BTreeSet<_>>()
            };
            let variables = support(factor);
            let mut candidates = remaining
                .iter()
                .enumerate()
                .map(|(index, other)| {
                    let other_variables = support(other);
                    let difference = variables
                        .symmetric_difference(&other_variables)
                        .collect::<Vec<_>>();
                    let inputs = difference
                        .iter()
                        .filter(|variable| {
                            matches!(
                                variable,
                                KernelVariable::InputKet(_) | KernelVariable::InputBra(_)
                            )
                        })
                        .count();
                    ((inputs, difference.len(), index), index, *other)
                })
                .collect::<Vec<_>>();
            candidates.sort_by_key(|(rank, _, _)| *rank);
            for (_, index, other) in candidates {
                if *probes == 0 {
                    return false;
                }
                *probes -= 1;
                if equal(factor, other, free_splits, algebra) {
                    matched = Some(index);
                    break;
                }
                if let Some(unit) =
                    matching_unit(factor, other, reduction, free_splits, algebra, probes)
                {
                    if collect_unit(&unit, &mut unit_scalar, &mut unit_phase, reduction).is_none() {
                        return false;
                    }
                    matched = Some(index);
                    break;
                }
            }
        }
        let Some(index) = matched else {
            relevant.extend(
                factor
                    .values()
                    .flat_map(BTreeMap::keys)
                    .flat_map(KernelPhasePolynomial::variables),
            );
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "aggregate factored refusal: unmatched factor; position={position} atoms={} phase_terms={} remaining_factors={} free_splits={free_splits} probes={probes} phase_cells={} products={}",
                    factor.values().map(BTreeMap::len).sum::<usize>(),
                    factor
                        .values()
                        .flat_map(BTreeMap::keys)
                        .map(KernelPhasePolynomial::term_count)
                        .sum::<usize>(),
                    remaining.len(),
                    reduction.phase_cells,
                    reduction.products
                );
            }
            return false;
        };
        remaining.remove(index);
    }
    if unit_scalar != integer(1) || unit_phase.term_count() != 0 {
        let mut unit = ExactAggregate::new();
        if accumulate_exact_term(
            ExactTerm {
                constraints: Vec::new(),
                coefficient: KernelScalar::Rational(unit_scalar),
                phase: unit_phase,
            },
            &mut unit,
            &mut 0,
        )
        .is_none()
        {
            return false;
        }
        let Some(updated) = multiply_aggregates(common, unit, reduction) else {
            return false;
        };
        common = updated;
    }
    let common_equal = equal(&common, &right.common, free_splits, algebra);
    if !common_equal && std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate factored zero-product start: phase_cells={} free_splits={free_splits}",
            reduction.phase_cells
        );
    }
    let proved = common_equal
        || aggregate_difference(common, right.common.clone()).is_some_and(|difference| {
            let Some(difference) = forget_common_selector(difference).and_then(remove_common_phase)
            else {
                return false;
            };
            let mut factors = vec![difference];
            factors.extend(right.factors.iter().cloned());
            zero_product(factors, free_splits, algebra, &mut reduction.phase_cells, 0)
        });
    if proved && std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!("aggregate factored match: complete factor bijection verified");
    }
    proved && remaining.is_empty()
}

/// One left factor may represent two right factors. Rank at most 16 pair
/// proposals, then prove the FULL product equation, optionally up to an
/// explicitly certified nonzero unit. Support/counts alone prove nothing.
fn matching_pair_unit(
    factor: &ExactAggregate,
    remaining: &[&ExactAggregate],
    reduction: &mut ReductionBudget,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
    probes: &mut usize,
) -> Option<(usize, usize, ExactAggregate)> {
    if *probes == 0 || remaining.len() > MAX_FACTORS {
        return None;
    }
    charge_cells(factor, &mut reduction.phase_cells)?;
    for sum in remaining {
        charge_cells(sum, &mut reduction.phase_cells)?;
    }
    let support = |sum: &ExactAggregate| {
        sum.values()
            .flat_map(BTreeMap::keys)
            .flat_map(KernelPhasePolynomial::variables)
            .collect::<BTreeSet<_>>()
    };
    let target = support(factor);
    let supports = remaining.iter().map(|sum| support(sum)).collect::<Vec<_>>();
    let mut candidates = Vec::new();
    for a in 0..remaining.len() {
        for b in a + 1..remaining.len() {
            reduction.phase_cells = reduction
                .phase_cells
                .checked_sub(1 + target.len() + supports[a].len() + supports[b].len())?;
            let union = supports[a]
                .union(&supports[b])
                .cloned()
                .collect::<BTreeSet<_>>();
            let difference = target.symmetric_difference(&union).collect::<Vec<_>>();
            let inputs = difference
                .iter()
                .filter(|v| matches!(v, KernelVariable::InputKet(_) | KernelVariable::InputBra(_)))
                .count();
            candidates.push(((inputs, difference.len(), a, b), a, b));
        }
    }
    candidates.sort_by_key(|(rank, _, _)| *rank);
    for (_, a, b) in candidates.into_iter().take(16) {
        *probes = probes.checked_sub(1)?;
        let product = multiply_aggregates(remaining[a].clone(), remaining[b].clone(), reduction)?;
        if equal(factor, &product, free, algebra) {
            let mut unit = ExactAggregate::new();
            accumulate_exact_term(
                ExactTerm {
                    constraints: Vec::new(),
                    coefficient: KernelScalar::Rational(integer(1)),
                    phase: KernelPhasePolynomial::default(),
                },
                &mut unit,
                &mut 0,
            )?;
            return Some((a, b, unit));
        }
        if let Some(unit) = matching_unit(factor, &product, reduction, free, algebra, probes) {
            return Some((a, b, unit));
        }
    }
    None
}

/// Collect only certified, unguarded, nonzero rational/exponential units.
/// Associativity lets us multiply their product into the large common term
/// once. No selector or non-unit factor may enter this accumulator.
fn collect_unit(
    unit: &ExactAggregate,
    scalar: &mut BigRational,
    phase: &mut KernelPhasePolynomial,
    budget: &mut ReductionBudget,
) -> Option<()> {
    if unit.len() != 1 {
        return None;
    }
    let (entry, coefficients) = unit.first_key_value()?;
    if !entry.constraints.is_empty() || coefficients.len() != 1 {
        return None;
    }
    let (next_phase, KernelScalar::Rational(next_scalar)) = coefficients.first_key_value()? else {
        return None;
    };
    if *next_scalar == integer(0)
        || next_scalar.numer().bits() > 4096
        || next_scalar.denom().bits() > 4096
    {
        return None;
    }
    charge_cells(unit, &mut budget.phase_cells)?;
    let next = &*scalar * next_scalar;
    if next.numer().bits() > 4096 || next.denom().bits() > 4096 {
        return None;
    }
    add_phase(phase, next_phase)?;
    *scalar = next;
    Some(())
}

/// Propose a nonzero monomial unit from atom pivots, then prove the WHOLE
/// factor equation left = unit * right. Pivot syntax alone proves nothing.
/// The unit is multiplied into the left common coefficient, so phases and
/// scales remain accounted for after matching. All probes share one budget.
fn matching_unit(
    left: &ExactAggregate,
    right: &ExactAggregate,
    reduction: &mut ReductionBudget,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
    probes: &mut usize,
) -> Option<ExactAggregate> {
    if let Some(unit) = conditional_binomial_unit(left, right, reduction) {
        *probes = probes.checked_sub(1)?;
        return Some(unit);
    }
    if let Some(unit) = relative_phase_unit(left, right, reduction, free, algebra) {
        *probes = probes.checked_sub(1)?;
        let transformed = multiply_aggregates(right.clone(), unit.clone(), reduction)?;
        // Replay the reconstructed unit against the entire original pair,
        // including every selector, even after exhaustive interpolation.
        if equal(left, &transformed, free, algebra) {
            return Some(unit);
        }
    }
    for (left_phase, left_scalar) in left.values().flat_map(BTreeMap::iter).take(4) {
        let KernelScalar::Rational(left_scalar) = left_scalar else {
            continue;
        };
        for (right_phase, right_scalar) in right.values().flat_map(BTreeMap::iter).take(4) {
            let KernelScalar::Rational(right_scalar) = right_scalar else {
                continue;
            };
            if *left_scalar == integer(0)
                || *right_scalar == integer(0)
                || left_scalar.numer().bits() > 4096
                || left_scalar.denom().bits() > 4096
                || right_scalar.numer().bits() > 4096
                || right_scalar.denom().bits() > 4096
            {
                continue;
            }
            let phase = KernelPhasePolynomial::difference(left_phase, right_phase);
            let scalar = left_scalar / right_scalar;
            if phase.term_count() == 0 && scalar == integer(1) {
                continue;
            }
            *probes = probes.checked_sub(1)?;
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
            let transformed = multiply_aggregates(right.clone(), unit.clone(), reduction)?;
            if equal(left, &transformed, free, algebra) {
                return Some(unit);
            }
        }
    }
    None
}

/// Exhaustive bounded relative-unit interpolation. On every Boolean leaf,
/// either BOTH values are zero, or both are nonzero rational/root monomials
/// whose ratio has a common positive magnitude. Zero leaves do not license
/// cancellation: they are explicitly checked on both sides and merely leave
/// the unit unconstrained there. A caller also replays the full equation.
fn relative_phase_unit(
    left: &ExactAggregate,
    right: &ExactAggregate,
    reduction: &mut ReductionBudget,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
) -> Option<ExactAggregate> {
    let mut admission = 4096;
    for source in [left, right] {
        if source.values().map(BTreeMap::len).sum::<usize>() > 32 {
            return None;
        }
        charge_cells(source, &mut admission)?;
        charge_cells(source, &mut reduction.phase_cells)?;
        for (entry, coefficients) in source {
            if entry
                .constraints
                .iter()
                .any(|row| row.variables().iter().any(KernelVariable::is_bound_path))
                || coefficients
                    .keys()
                    .any(|phase| phase.variables().iter().any(KernelVariable::is_bound_path))
                || coefficients.values().any(|scalar| {
                    !scalar_conditions_within_budget(scalar, |row| {
                        row.variables()
                            .iter()
                            .all(|variable| !variable.is_bound_path())
                    })
                })
            {
                return None;
            }
        }
    }
    // Removing an identical selector from BOTH sides strengthens the
    // equality obligation; it does not identify differently guarded terms.
    let common = left
        .keys()
        .next()?
        .constraints
        .iter()
        .filter(|row| {
            left.keys()
                .chain(right.keys())
                .all(|entry| entry.constraints.contains(row))
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    let unguard = |source: &ExactAggregate| -> Option<ExactAggregate> {
        let mut result = ExactAggregate::new();
        for (entry, coefficients) in source {
            let constraints = entry
                .constraints
                .iter()
                .filter(|row| !common.contains(*row))
                .cloned()
                .collect::<Vec<_>>();
            for (phase, coefficient) in coefficients {
                accumulate_exact_term(
                    ExactTerm {
                        constraints: constraints.clone(),
                        coefficient: coefficient.clone(),
                        phase: phase.clone(),
                    },
                    &mut result,
                    &mut 0,
                )?;
            }
        }
        Some(result)
    };
    let left = unguard(left)?;
    let right = unguard(right)?;
    let mut variables = BTreeSet::new();
    for source in [&left, &right] {
        for (entry, coefficients) in source {
            for row in &entry.constraints {
                variables.extend(row.variables());
            }
            for (phase, scalar) in coefficients {
                variables.extend(phase.variables());
                if !scalar_conditions_within_budget(scalar, |row| {
                    variables.extend(row.variables());
                    variables.len() <= 8
                }) {
                    return None;
                }
            }
        }
    }
    if variables.len() > 8 || variables.iter().any(KernelVariable::is_bound_path) {
        return None;
    }
    let (scalar, phase) = interpolate_relative_unit(
        left,
        right,
        &variables.into_iter().collect::<Vec<_>>(),
        reduction,
        free,
        algebra,
    )?;
    let mut unit = ExactAggregate::new();
    accumulate_exact_term(
        ExactTerm {
            constraints: Vec::new(),
            coefficient: KernelScalar::Rational(scalar.unwrap_or_else(|| integer(1))),
            phase,
        },
        &mut unit,
        &mut 0,
    )?;
    Some(unit)
}

fn interpolate_relative_unit(
    left: ExactAggregate,
    right: ExactAggregate,
    variables: &[KernelVariable],
    reduction: &mut ReductionBudget,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
) -> Option<(Option<BigRational>, KernelPhasePolynomial)> {
    charge_cells(&left, &mut reduction.phase_cells)?;
    charge_cells(&right, &mut reduction.phase_cells)?;
    let Some((variable, rest)) = variables.split_first() else {
        let Some((a, p)) = witness::constant_monomial(&left, algebra) else {
            return (witness::constant_is_zero(&left, algebra)
                && witness::constant_is_zero(&right, algebra))
            .then_some((None, KernelPhasePolynomial::default()));
        };
        let (b, q) = witness::constant_monomial(&right, algebra)?;
        let scalar = a / b;
        if scalar.numer().bits() > 4096 || scalar.denom().bits() > 4096 {
            return None;
        }
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(
            &KernelBooleanPolynomial::one(),
            crate::symbolic::PhaseCoefficient::rational(p - q),
        );
        return Some((Some(scalar), phase));
    };
    *free = free.checked_sub(1)?;
    let (a, mut p) = interpolate_relative_unit(
        restrict_aggregate(&left, variable, false)?,
        restrict_aggregate(&right, variable, false)?,
        rest,
        reduction,
        free,
        algebra,
    )?;
    let (b, q) = interpolate_relative_unit(
        restrict_aggregate(&left, variable, true)?,
        restrict_aggregate(&right, variable, true)?,
        rest,
        reduction,
        free,
        algebra,
    )?;
    if matches!((&a, &b), (Some(a), Some(b)) if a != b) {
        return None;
    }
    charge_phase(&p, reduction)?;
    charge_phase(&q, reduction)?;
    let difference = KernelPhasePolynomial::difference(&q, &p);
    let literal = KernelBooleanPolynomial::variable(variable.clone());
    for (monomial, coefficient) in difference.terms() {
        reduction.phase_cells = reduction
            .phase_cells
            .checked_sub(2 + monomial.variables().count())?;
        p.add_boolean(
            &literal.and(&KernelBooleanPolynomial::from_monomial(monomial.clone())),
            coefficient.clone(),
        );
    }
    Some((a.or(b), p))
}

/// For Boolean f and L=(1-2f)R, exactly
/// 1+exp(2*pi*i*L) = exp(-2*pi*i*f*R) (1+exp(2*pi*i*R)).
/// Check the complete phase identity, coefficients and selector, not just
/// a pivot. No division by a possibly zero binomial occurs.
fn conditional_binomial_unit(
    left: &ExactAggregate,
    right: &ExactAggregate,
    budget: &mut ReductionBudget,
) -> Option<ExactAggregate> {
    fn binomial(sum: &ExactAggregate) -> Option<(&ExactEntry, &KernelPhasePolynomial)> {
        if sum.len() != 1 {
            return None;
        }
        let (entry, coefficients) = sum.first_key_value()?;
        if coefficients.len() != 2
            || coefficients.first_key_value()?.0.term_count() != 0
            || coefficients
                .values()
                .any(|coefficient| *coefficient != KernelScalar::Rational(integer(1)))
        {
            return None;
        }
        Some((entry, coefficients.last_key_value()?.0))
    }
    let (left_entry, left_phase) = binomial(left)?;
    let (right_entry, right_phase) = binomial(right)?;
    if left_entry != right_entry || right_phase.term_count() > 256 {
        return None;
    }
    if let Some(phase) = parity_orientation_phase(left_phase, right_phase, budget)
        .or_else(|| large_parity_orientation_phase(left_phase, right_phase, budget))
        .or_else(|| orientation_phase(left_phase, right_phase, budget, 0))
    {
        let mut unit = ExactAggregate::new();
        accumulate_exact_term(
            ExactTerm {
                constraints: Vec::new(),
                coefficient: KernelScalar::Rational(integer(1)),
                phase,
            },
            &mut unit,
            &mut 0,
        )?;
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!("aggregate factored cofactored orientation verified");
        }
        return Some(unit);
    }
    let difference = KernelPhasePolynomial::difference(left_phase, right_phase);
    let variables = difference
        .variables()
        .into_iter()
        .take(8)
        .collect::<Vec<_>>();
    if variables.iter().any(KernelVariable::is_bound_path) {
        return None;
    }
    // At most eight literals and 28 two-literal parities.
    for index in 0..variables.len() {
        for other in index..variables.len() {
            let mut flip = KernelBooleanPolynomial::variable(variables[index].clone());
            if other != index {
                flip = flip.xor(&KernelBooleanPolynomial::variable(variables[other].clone()));
            }
            let unit_phase = negative_gated_phase(right_phase, &flip, budget)?;
            let mut expected = right_phase.clone();
            add_phase(&mut expected, &unit_phase)?;
            add_phase(&mut expected, &unit_phase)?;
            if expected != *left_phase {
                continue;
            }
            let mut unit = ExactAggregate::new();
            accumulate_exact_term(
                ExactTerm {
                    constraints: Vec::new(),
                    coefficient: KernelScalar::Rational(integer(1)),
                    phase: unit_phase,
                },
                &mut unit,
                &mut 0,
            )?;
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!("aggregate factored conditional orientation verified");
            }
            return Some(unit);
        }
    }
    None
}

/// Propose just one three-literal parity when those coordinates dominate a
/// large expanded phase. Frequency only schedules the proposal: the entire
/// modular identity L=R-2*f*R must hold before its unit can be returned.
fn parity_orientation_phase(
    left: &KernelPhasePolynomial,
    right: &KernelPhasePolynomial,
    budget: &mut ReductionBudget,
) -> Option<KernelPhasePolynomial> {
    if left.term_count() > MAX_ORIENTATION_LEFT_TERMS
        || right.term_count() > 256
        || left.term_count() < right.term_count().saturating_mul(4)
    {
        return None;
    }
    for phase in [left, right] {
        charge_phase(phase, budget)?;
    }
    let difference = KernelPhasePolynomial::difference(left, right);
    let mut counts = BTreeMap::<KernelVariable, usize>::new();
    for (monomial, _) in difference.terms() {
        for variable in monomial.variables() {
            if variable.is_bound_path() {
                return None;
            }
            *counts.entry(variable.clone()).or_default() += 1;
        }
    }
    let maximum = *counts.values().max()?;
    let variables = counts
        .into_iter()
        .filter(|(_, count)| *count * 2 >= maximum)
        .map(|(variable, _)| variable)
        .take(4)
        .collect::<Vec<_>>();
    if variables.len() != 3 {
        return None;
    }
    let flip = variables
        .into_iter()
        .fold(KernelBooleanPolynomial::zero(), |sum, variable| {
            sum.xor(&KernelBooleanPolynomial::variable(variable))
        });
    let unit = negative_gated_phase(right, &flip, budget)?;
    let mut expected = right.clone();
    add_phase(&mut expected, &unit)?;
    add_phase(&mut expected, &unit)?;
    (*left == expected).then_some(unit)
}

fn charge_phase(phase: &KernelPhasePolynomial, budget: &mut ReductionBudget) -> Option<()> {
    budget.phase_cells = budget.phase_cells.checked_sub(1)?;
    for (monomial, _) in phase.terms() {
        budget.phase_cells = budget
            .phase_cells
            .checked_sub(1 + monomial.variables().count())?;
    }
    Some(())
}

/// A distinct bounded proposal for an expanded parity-controlled orientation.
/// Unlike the four-deep cofactor tree, this checks ONE whole polynomial
/// identity. Support frequencies only propose up to six literal XOR inputs.
/// No ordinary phase/tree cap is lifted and all work is charged as before.
fn large_parity_orientation_phase(
    left: &KernelPhasePolynomial,
    right: &KernelPhasePolynomial,
    budget: &mut ReductionBudget,
) -> Option<KernelPhasePolynomial> {
    if !(513..=2048).contains(&left.term_count()) || right.term_count() > 256 {
        return None;
    }
    let mut cells = 32768usize;
    for phase in [left, right] {
        for (m, c) in phase.terms() {
            cells = cells.checked_sub(1 + m.variables().count())?;
            if m.variables().any(KernelVariable::is_bound_path) {
                return None;
            }
            let r = c.as_rational()?;
            if r.numer().bits() > 256 || r.denom().bits() > 256 {
                return None;
            }
        }
        charge_phase(phase, budget)?;
    }
    let difference = KernelPhasePolynomial::difference(left, right);
    let mut counts = BTreeMap::<KernelVariable, usize>::new();
    for (m, _) in difference.terms() {
        for v in m.variables() {
            *counts.entry(v.clone()).or_default() += 1;
        }
    }
    let maximum = *counts.values().max()?;
    let variables = counts
        .iter()
        .filter(|(_, count)| **count * 2 >= maximum)
        .take(7)
        .map(|(v, _)| v.clone())
        .collect::<Vec<_>>();
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate large parity proposal: left={} right={} variables={variables:?} remaining={}",
            left.term_count(),
            right.term_count(),
            budget.phase_cells
        );
    }
    if !(1..=6).contains(&variables.len()) {
        return None;
    }
    let flip = variables
        .into_iter()
        .fold(KernelBooleanPolynomial::zero(), |p, v| {
            p.xor(&KernelBooleanPolynomial::variable(v))
        });
    let unit = negative_gated_phase_bounded(right, &flip, budget, 6)?;
    // Replay ALL coefficients. This is L=(1-2*f)R, not an inference from
    // size, dominant support or any free-coordinate sample.
    let mut expected = right.clone();
    add_phase(&mut expected, &unit)?;
    add_phase(&mut expected, &unit)?;
    (*left == expected).then_some(unit)
}

/// A complete bounded proof tree for binomial orientation. Each leaf proves
/// L=R or L=-R as a full phase polynomial; the returned unit is respectively
/// 0 or -R. Recombine the two FREE cofactors by Shannon interpolation,
/// never summing or discarding a branch. No atom/selector cancellation.
fn orientation_phase(
    left: &KernelPhasePolynomial,
    right: &KernelPhasePolynomial,
    budget: &mut ReductionBudget,
    depth: usize,
) -> Option<KernelPhasePolynomial> {
    if left.term_count() > MAX_ORIENTATION_LEFT_TERMS || right.term_count() > 256 {
        return None;
    }
    for phase in [left, right] {
        charge_phase(phase, budget)?;
    }
    if left == right {
        return Some(KernelPhasePolynomial::default());
    }
    let negative = KernelPhasePolynomial::difference(&KernelPhasePolynomial::default(), right);
    if *left == negative {
        return Some(negative);
    }
    if depth >= 4 {
        return None;
    }
    let difference = KernelPhasePolynomial::difference(left, right);
    let mut counts = BTreeMap::<KernelVariable, usize>::new();
    for (monomial, _) in difference.terms() {
        for variable in monomial.variables() {
            if variable.is_bound_path() {
                return None;
            }
            *counts.entry(variable.clone()).or_default() += 1;
        }
    }
    let (variable, _) = counts.into_iter().max_by_key(|(_, count)| *count)?;
    let mut units = Vec::new();
    for value in [false, true] {
        let mut l = left.clone();
        let mut r = right.clone();
        let replacement = KernelBooleanPolynomial::from(value);
        l.substitute(&variable, &replacement);
        r.substitute(&variable, &replacement);
        units.push(orientation_phase(&l, &r, budget, depth + 1)?);
    }
    let delta = KernelPhasePolynomial::difference(&units[0], &units[1]);
    let gate = negative_gated_phase(&delta, &KernelBooleanPolynomial::variable(variable), budget)?;
    let mut result = units.remove(0);
    add_phase(&mut result, &gate)?;
    Some(result)
}

fn negative_gated_phase(
    phase: &KernelPhasePolynomial,
    flip: &KernelBooleanPolynomial,
    budget: &mut ReductionBudget,
) -> Option<KernelPhasePolynomial> {
    negative_gated_phase_bounded(phase, flip, budget, 3)
}

fn negative_gated_phase_bounded(
    phase: &KernelPhasePolynomial,
    flip: &KernelBooleanPolynomial,
    budget: &mut ReductionBudget,
    max_flip: usize,
) -> Option<KernelPhasePolynomial> {
    // Original callers propose <=3 ANF monomials (<=7 lift products).
    // The separately admitted large-parity proposal uses <=6 (<=63).
    // Charge the entire upper bound before constructing each product.
    let flip_variables = flip
        .terms()
        .map(|monomial| monomial.variables().count())
        .sum::<usize>();
    if max_flip > 6
        || flip.term_count() > max_flip
        || phase.term_count() > 256
        || flip_variables > max_flip
    {
        return None;
    }
    // A literal has one product, not the three needed for a two-term XOR.
    // Each lifted product contains only source variables and variables of
    // flip. Collisions/Boolean idempotence can only reduce this upper bound.
    let products_per_term = (1usize << flip.term_count()) - 1;
    let mut result = KernelPhasePolynomial::default();
    for (monomial, coefficient) in phase.terms() {
        let cost = products_per_term * (1 + flip_variables + monomial.variables().count());
        budget.phase_cells = budget.phase_cells.checked_sub(cost)?;
        result.add_boolean(
            &flip.and(&KernelBooleanPolynomial::from_monomial(monomial.clone())),
            coefficient.scaled(BigInt::from(-1)),
        );
    }
    Some(result)
}

/// After a COMPLETE factor bijection, equality reduces to
/// (C_left-C_right) * product(F_i) = 0. Never cancel/divide by an F_i:
/// it may vanish exactly where the common coefficients disagree.
fn zero_product(
    factors: Vec<ExactAggregate>,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
    cells: &mut usize,
    depth: usize,
) -> bool {
    let mut normalized = Vec::new();
    for factor in factors {
        if charge_cells(&factor, cells).is_none() {
            return false;
        }
        let Some(factor) = remove_common_phase(factor) else {
            return false;
        };
        if factor.is_empty() || witness::constant_is_zero(&factor, algebra) {
            return true;
        }
        normalized.push(factor);
    }
    if depth >= MAX_FREE_SPLIT_DEPTH || *free == 0 {
        return false;
    }
    // The first factor is the coefficient difference. Start with its
    // support so irrelevant coordinates in other factors do not dominate.
    let mut selected = None;
    for factor in &normalized {
        let mut variables = BTreeMap::<KernelVariable, usize>::new();
        for (entry, coefficients) in factor {
            for row in &entry.constraints {
                for variable in row.variables() {
                    *variables.entry(variable).or_default() += 1;
                }
            }
            for (phase, scalar) in coefficients {
                for (monomial, _) in phase.terms() {
                    for variable in monomial.variables() {
                        *variables.entry(variable.clone()).or_default() += 1;
                    }
                }
                if !scalar_conditions_within_budget(scalar, |row| {
                    for variable in row.variables() {
                        *variables.entry(variable).or_default() += 1;
                    }
                    true
                }) {
                    return false;
                }
            }
        }
        // Repeated coordinates often gate the whole coefficient difference.
        // Choose the most frequent one, preserving the old least-variable
        // tie order. This is scheduling only: BOTH whole-product cofactors
        // must still vanish, and no possibly zero factor is canceled.
        if let Some((variable, _)) = variables
            .into_iter()
            .min_by_key(|(variable, count)| (std::cmp::Reverse(*count), variable.clone()))
        {
            selected = Some(variable);
            break;
        }
    }
    let Some(variable) = selected else {
        return false;
    };
    if variable.is_bound_path() {
        return false;
    }
    *free -= 1;
    for value in [false, true] {
        let Some(children) = normalized
            .iter()
            .map(|factor| restrict_aggregate(factor, &variable, value))
            .collect::<Option<Vec<_>>>()
        else {
            return false;
        };
        if !zero_product(children, free, algebra, cells, depth + 1) {
            return false;
        }
    }
    true
}

fn charge_cells(sum: &ExactAggregate, cells: &mut usize) -> Option<()> {
    for (entry, coefficients) in sum {
        for row in &entry.constraints {
            for monomial in row.terms() {
                *cells = cells.checked_sub(1 + monomial.variables().count())?;
            }
        }
        for phase in coefficients.keys() {
            // Charge even constant atoms so repeated constant products are
            // bounded independently of their empty variable support.
            *cells = cells.checked_sub(1)?;
            for (monomial, _) in phase.terms() {
                *cells = cells.checked_sub(1 + monomial.variables().count())?;
            }
        }
    }
    Some(())
}

fn eligible(term: &WorkingTerm) -> bool {
    if !(term.paths.len() <= MAX_INPUT_PATHS
        && term.phase.term_count() <= MAX_INPUT_PHASE_TERMS
        && term.constraints.len() <= 64
        && term.paths.iter().all(KernelVariable::is_bound_path)
        && term.within_budget())
    {
        return false;
    }
    let mut cells = 0usize;
    let mut inspect = |monomial: &KernelMonomial| {
        cells += 1;
        for variable in monomial.variables() {
            cells += 1;
            if cells > MAX_INPUT_CELLS
                || (variable.is_bound_path() && !term.paths.contains(variable))
            {
                return false;
            }
        }
        cells <= MAX_INPUT_CELLS
    };
    term.constraints
        .iter()
        .all(|row| row.terms().all(&mut inspect))
        && term.phase.terms().all(|(m, _)| inspect(m))
        && scalar_conditions_within_budget(&term.coefficient, |row| row.terms().all(&mut inspect))
}

fn equal(
    left: &ExactAggregate,
    right: &ExactAggregate,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
) -> bool {
    left == right
        || aggregate_difference(left.clone(), right.clone()).is_some_and(|difference| {
            zero_by_free_splitting_with_algebra(difference, free, algebra, 0)
        })
}

fn product(term: &WorkingTerm, budget: &mut ReductionBudget) -> Option<Product> {
    let factors = factor_phase_sums(term)?;
    product_from_factors(factors, budget)
}

fn product_from_factors(
    factors: Vec<WorkingTerm>,
    budget: &mut ReductionBudget,
) -> Option<Product> {
    product_from_factors_using(factors, budget, false, false)
}

fn product_from_factors_using(
    factors: Vec<WorkingTerm>,
    budget: &mut ReductionBudget,
    shared_small: bool,
    prefer_rectangles: bool,
) -> Option<Product> {
    if factors.len() > MAX_FACTORS + 1 {
        return None;
    }
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate factored groups: {:?}",
            factors
                .iter()
                .map(|factor| factor.paths.len())
                .collect::<Vec<_>>()
        );
    }
    // Keep all previously admitted component proofs on their old schedule.
    // This extra representation is relevant only to the new large-input route.
    let rectangles = prefer_rectangles
        || shared_small
            && factors.iter().any(|f| {
                f.phase
                    .terms()
                    .map(|(m, _)| 1 + m.variables().count())
                    .sum::<usize>()
                    > 32768
            });
    let mut factors = factors.into_iter();
    let Reduction::Exact(mut common) = reduce_working_term(factors.next()?) else {
        return None;
    };
    let selector = common.constraints.clone();
    let mut unit = ExactAggregate::new();
    let mut unit_atoms = 0;
    accumulate_exact_term(
        ExactTerm {
            constraints: selector.clone(),
            coefficient: KernelScalar::Rational(integer(1)),
            phase: KernelPhasePolynomial::default(),
        },
        &mut unit,
        &mut unit_atoms,
    )?;
    let mut normalized = Vec::new();
    let mut stored_atoms = 0usize;
    let mut cells_remaining = MAX_FACTOR_PHASE_CELLS;
    for mut factor in factors {
        if factor.paths.len() > MAX_SPLIT_DEPTH {
            return None;
        }
        let mut cells = 0usize;
        let large = shared_small && {
            let mut inspect = |m: &KernelMonomial| {
                cells = cells.saturating_add(1 + m.variables().count());
                true
            };
            factor
                .constraints
                .iter()
                .all(|r| r.terms().all(&mut inspect));
            factor.phase.terms().all(|(m, _)| inspect(m));
            scalar_conditions_within_budget(&factor.coefficient, |r| r.terms().all(&mut inspect));
            cells > 32768
        };
        // Duplicating the same indicator is exact: [G]^k=[G]. This lets
        // each factor use G without dropping G from the final product.
        // Select the representation BEFORE adding these common guards so
        // every previously admitted small factor retains its old scheduler.
        factor.constraints.extend(selector.iter().cloned());
        let (sum, atoms) = if large {
            // Large syntax never enters ordinary reduction by this entrance.
            // Every small-bound leaf must finish in the SAME proof budget.
            if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "aggregate shared small sum entrance: paths={} cells={cells} remaining={}",
                    factor.paths.len(),
                    budget.phase_cells
                );
            }
            let result = small_sum::sum(&factor, budget);
            if result.is_none() && std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                eprintln!(
                    "aggregate shared small sum refused: remaining={}",
                    budget.phase_cells
                );
            }
            let sum = result?;
            let atoms = sum.values().map(BTreeMap::len).sum::<usize>();
            (sum, atoms)
        } else {
            let mut sum = ExactAggregate::new();
            let mut atoms = 0;
            accumulate_reduction(reduce_working_term(factor), &mut sum, &mut atoms, budget, 0)?;
            (sum, atoms)
        };
        if atoms > MAX_FACTOR_ATOMS {
            return None;
        }
        // Charge retained selectors and phase syntax before normalizing and
        // replaying a factor. Atom count alone does not bound their storage.
        charge_cells(&sum, &mut cells_remaining)?;
        let refined = if rectangles {
            let mut source = Some(sum);
            rectangle::factor(&mut source, budget).or_else(|| refine_tensor(source?, budget))?
        } else {
            refine_tensor(sum, budget)?
        };
        for sum in refined {
            let (sum, scalar, phase) = normalize_factor(sum)?;
            common.coefficient =
                normalize_scalar(common.coefficient.multiply(KernelScalar::Rational(scalar)));
            add_phase(&mut common.phase, &phase)?;
            if !scalar_within_budget(&common.coefficient) {
                return None;
            }
            stored_atoms =
                stored_atoms.checked_add(sum.values().map(BTreeMap::len).sum::<usize>())?;
            if stored_atoms > MAX_STORED_ATOMS {
                return None;
            }
            charge_cells(&sum, &mut cells_remaining)?;
            if sum == unit {
                continue;
            }
            if sum.values().map(BTreeMap::len).sum::<usize>() == 1 {
                // A one-atom factor belongs in the common term, including
                // its OWN selector (which may be stronger than the original
                // common selector after reducing a guarded bound factor).
                let (entry, values) = sum.into_iter().next()?;
                let (phase, scalar) = values.into_iter().next()?;
                common.constraints.extend(entry.constraints);
                common.coefficient = normalize_scalar(common.coefficient.multiply(scalar));
                add_phase(&mut common.phase, &phase)?;
                continue;
            }
            normalized.push(sum);
            if normalized.len() > MAX_FACTORS {
                return None;
            }
        }
    }
    let mut aggregate = ExactAggregate::new();
    let mut atoms = 0;
    let common = WorkingTerm {
        paths: BTreeSet::new(),
        constraints: common.constraints,
        coefficient: common.coefficient,
        phase: common.phase,
    };
    accumulate_reduction(
        reduce_working_term(common),
        &mut aggregate,
        &mut atoms,
        budget,
        0,
    )?;
    Some(Product {
        common: aggregate,
        factors: normalized,
    })
}

/// Refine a small factor only after the existing tensor routine reconstructs
/// its entire unguarded aggregate. Reattach its OWN selector to both children;
/// idempotence preserves it even if it is stronger than the common selector.
fn refine_tensor(
    source: ExactAggregate,
    budget: &mut ReductionBudget,
) -> Option<Vec<ExactAggregate>> {
    let count = source.values().map(BTreeMap::len).sum::<usize>();
    if count < 4 {
        return Some(vec![source]);
    }
    let Some([left, right]) =
        factor_free_tensor(&source, budget).or_else(|| factor_binomials(&source, budget))
    else {
        return Some(vec![source]);
    };
    let size = |factor: &ExactAggregate| factor.values().map(BTreeMap::len).sum::<usize>();
    if size(&left) < 2 || size(&right) < 2 || size(&left) >= count || size(&right) >= count {
        return Some(vec![source]);
    }
    let selector = source.keys().next()?.constraints.clone();
    let mut result = Vec::new();
    for factor in [left, right] {
        let mut guarded = ExactAggregate::new();
        let mut atoms = 0;
        for (entry, coefficients) in factor {
            for (phase, coefficient) in coefficients {
                let mut constraints = entry.constraints.clone();
                constraints.extend(selector.iter().cloned());
                accumulate_reduction(
                    reduce_working_term(WorkingTerm {
                        constraints,
                        coefficient,
                        phase,
                        paths: BTreeSet::new(),
                    }),
                    &mut guarded,
                    &mut atoms,
                    budget,
                    0,
                )?;
            }
        }
        result.push(guarded);
    }
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "aggregate factored tensor refinement: {count} -> {:?}",
            result.iter().map(size).collect::<Vec<_>>()
        );
    }
    Some(result)
}

/// A four-atom product need not follow the syntactic ket/bra partition.
/// Try at most six rectangles around one nonzero atom; accept ONLY exact
/// reconstruction, with every selector and all relative phases retained.
fn factor_binomials(
    source: &ExactAggregate,
    budget: &mut ReductionBudget,
) -> Option<[ExactAggregate; 2]> {
    if source.len() != 1 {
        return None;
    }
    let (entry, coefficients) = source.first_key_value()?;
    if coefficients.len() != 4 {
        return None;
    }
    let atoms = coefficients.iter().collect::<Vec<_>>();
    let (pivot_phase, KernelScalar::Rational(pivot_scalar)) = atoms[0] else {
        return None;
    };
    if *pivot_scalar == integer(0)
        || pivot_scalar.numer().bits() > 4096
        || pivot_scalar.denom().bits() > 4096
    {
        return None;
    }
    for row in 1..4 {
        for column in 1..4 {
            if row == column {
                continue;
            }
            let KernelScalar::Rational(column_scalar) = atoms[column].1 else {
                return None;
            };
            let mut left = ExactAggregate::new();
            let mut left_atoms = 0;
            for index in [0, row] {
                accumulate_exact_term(
                    ExactTerm {
                        constraints: entry.constraints.clone(),
                        coefficient: atoms[index].1.clone(),
                        phase: atoms[index].0.clone(),
                    },
                    &mut left,
                    &mut left_atoms,
                )?;
            }
            let mut right = ExactAggregate::new();
            let mut right_atoms = 0;
            for (coefficient, phase) in [
                (integer(1), KernelPhasePolynomial::default()),
                (
                    column_scalar / pivot_scalar,
                    KernelPhasePolynomial::difference(atoms[column].0, pivot_phase),
                ),
            ] {
                accumulate_exact_term(
                    ExactTerm {
                        constraints: entry.constraints.clone(),
                        coefficient: KernelScalar::Rational(coefficient),
                        phase,
                    },
                    &mut right,
                    &mut right_atoms,
                )?;
            }
            if multiply_aggregates(left.clone(), right.clone(), budget)? == *source {
                return Some([left, right]);
            }
        }
    }
    None
}

fn add_phase(
    destination: &mut KernelPhasePolynomial,
    source: &KernelPhasePolynomial,
) -> Option<()> {
    if destination.term_count().saturating_add(source.term_count()) > MAX_PHASE_TERMS {
        return None;
    }
    for (monomial, coefficient) in source.terms() {
        destination.add_boolean(
            &KernelBooleanPolynomial::from_monomial(monomial.clone()),
            coefficient.clone(),
        );
    }
    Some(())
}

/// Extract only an explicitly nonzero rational times an exponential. Try at
/// most eight atom pivots and choose a sufficient canonical representative.
/// Replay the exact inverse transformation and require the original formal
/// aggregate back; unit extraction is not trusted without reconstruction.
fn normalize_factor(
    source: ExactAggregate,
) -> Option<(ExactAggregate, BigRational, KernelPhasePolynomial)> {
    let mut best: Option<(ExactAggregate, BigRational, KernelPhasePolynomial)> = None;
    for (common, pivot) in source.values().flat_map(BTreeMap::iter).take(8) {
        let KernelScalar::Rational(scalar) = pivot else {
            continue;
        };
        if scalar == &integer(0) || scalar.numer().bits() > 4096 || scalar.denom().bits() > 4096 {
            continue;
        }
        let mut normalized = ExactAggregate::new();
        let mut atoms = 0;
        for (entry, coefficients) in &source {
            for (phase, coefficient) in coefficients {
                accumulate_exact_term(
                    ExactTerm {
                        constraints: entry.constraints.clone(),
                        phase: KernelPhasePolynomial::difference(phase, common),
                        coefficient: normalize_scalar(
                            coefficient
                                .clone()
                                .multiply(KernelScalar::Rational(scalar.recip())),
                        ),
                    },
                    &mut normalized,
                    &mut atoms,
                )?;
            }
        }
        if best
            .as_ref()
            .is_none_or(|(current, _, _)| normalized < *current)
        {
            best = Some((normalized, scalar.clone(), common.clone()));
        }
    }
    let (normalized, scalar, common) = best?;
    let mut replay = ExactAggregate::new();
    let mut atoms = 0;
    for (entry, coefficients) in &normalized {
        for (phase, coefficient) in coefficients {
            let mut phase = phase.clone();
            add_phase(&mut phase, &common)?;
            accumulate_exact_term(
                ExactTerm {
                    constraints: entry.constraints.clone(),
                    phase,
                    coefficient: normalize_scalar(
                        coefficient
                            .clone()
                            .multiply(KernelScalar::Rational(scalar.clone())),
                    ),
                },
                &mut replay,
                &mut atoms,
            )?;
        }
    }
    (replay == source).then_some((normalized, scalar, common))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::PhaseCoefficient;

    fn collapse(source: &ExactAggregate) -> Option<ExactAggregate> {
        let mut free = MAX_FREE_SPLITS;
        collapse_phase_unit(
            source,
            &mut ReductionBudget {
                splits: 255,
                products: MAX_FACTOR_PRODUCTS,
                phase_cells: MAX_FACTOR_PHASE_CELLS,
            },
            &mut free,
            &mut witness::ConstantBudget::default(),
        )
    }

    #[test]
    fn phase_unit_interpolation_checks_every_cofactor_and_retains_selector() {
        let x = KernelVariable::InputKet(0);
        let y = KernelVariable::InputBra(0);
        let selector = vec![KernelBooleanPolynomial::variable(
            KernelVariable::ClassicalOutput(0),
        )];
        // All 256 functions from two bits to the four quarter-turn roots.
        // Build from independent minterm selectors; verify the returned
        // polynomial against the original integer table, not its own replay.
        for table in 0..256usize {
            let mut source = ExactAggregate::new();
            for assignment in 0..4 {
                let mut condition = KernelBooleanPolynomial::one();
                for (bit, variable) in [x.clone(), y.clone()].into_iter().enumerate() {
                    let literal = KernelBooleanPolynomial::variable(variable);
                    condition = condition.and(&if assignment & (1 << bit) != 0 {
                        literal
                    } else {
                        literal.complement()
                    });
                }
                let mut phase = KernelPhasePolynomial::default();
                phase.add_boolean(
                    &KernelBooleanPolynomial::one(),
                    PhaseCoefficient::rational(ratio(((table >> (2 * assignment)) & 3) as i64, 4)),
                );
                accumulate_exact_term(
                    ExactTerm {
                        constraints: selector.clone(),
                        phase,
                        coefficient: KernelScalar::Select {
                            condition,
                            when_true: Box::new(KernelScalar::Rational(integer(3))),
                            when_false: Box::new(KernelScalar::Rational(integer(0))),
                        },
                    },
                    &mut source,
                    &mut 0,
                )
                .unwrap();
            }
            let unit = collapse(&source).unwrap();
            assert_eq!(unit.len(), 1);
            let (entry, values) = unit.first_key_value().unwrap();
            assert_eq!(entry.constraints, selector);
            assert_eq!(values.len(), 1);
            // Accumulation may move a half turn to the signed scalar.
            let (phase, KernelScalar::Rational(scalar)) = values.first_key_value().unwrap() else {
                panic!("not a unit");
            };
            for assignment in 0..4 {
                let mut phase = phase.clone();
                for (bit, variable) in [&x, &y].into_iter().enumerate() {
                    phase.substitute(
                        variable,
                        &KernelBooleanPolynomial::from(assignment & (1 << bit) != 0),
                    );
                }
                let mut expected =
                    PhaseCoefficient::rational(ratio(((table >> (2 * assignment)) & 3) as i64, 4));
                if *scalar == integer(-3) {
                    expected = PhaseCoefficient::rational(ratio(
                        ((table >> (2 * assignment)) & 3) as i64 + 2,
                        4,
                    ));
                } else {
                    assert_eq!(*scalar, integer(3));
                }
                assert_eq!(phase.coefficient(&KernelMonomial::one()), expected);
                assert!(phase.variables().is_empty());
            }
        }
    }

    #[test]
    fn phase_unit_interpolation_refuses_zero_variable_magnitude_and_budget() {
        let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
        for true_value in [0, 2] {
            let source = BTreeMap::from([(
                ExactEntry {
                    constraints: vec![x.clone()],
                },
                BTreeMap::from([(
                    KernelPhasePolynomial::default(),
                    KernelScalar::Select {
                        condition: x.clone(),
                        when_true: Box::new(KernelScalar::Rational(integer(true_value))),
                        when_false: Box::new(KernelScalar::Rational(integer(1))),
                    },
                )]),
            )]);
            // Even an inactive selector branch is checked: no zero-factor
            // division or assumption that the selector makes a unit nonzero.
            assert!(collapse(&source).is_none());
        }
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(&x, PhaseCoefficient::rational(ratio(1, 8)));
        let source = BTreeMap::from([(
            ExactEntry {
                constraints: Vec::new(),
            },
            BTreeMap::from([(phase.clone(), KernelScalar::Rational(integer(1)))]),
        )]);
        assert!(collapse(&source).is_some());
        let mut free = MAX_FREE_SPLITS;
        assert!(
            collapse_phase_unit(
                &source,
                &mut ReductionBudget {
                    splits: 255,
                    products: MAX_FACTOR_PRODUCTS,
                    phase_cells: 0
                },
                &mut free,
                &mut witness::ConstantBudget::default()
            )
            .is_none()
        );
        assert!(
            collapse_phase_unit(
                &source,
                &mut ReductionBudget {
                    splits: 255,
                    products: MAX_FACTOR_PRODUCTS,
                    phase_cells: MAX_FACTOR_PHASE_CELLS
                },
                &mut 0,
                &mut witness::ConstantBudget::default()
            )
            .is_none()
        );
        for index in 1..9 {
            phase.add_boolean(
                &KernelBooleanPolynomial::variable(KernelVariable::InputKet(index)),
                PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        let oversized = BTreeMap::from([(
            ExactEntry {
                constraints: Vec::new(),
            },
            BTreeMap::from([(phase, KernelScalar::Rational(integer(1)))]),
        )]);
        assert!(collapse(&oversized).is_none());
        let mut unsupported = KernelPhasePolynomial::default();
        unsupported.add_boolean(
            &KernelBooleanPolynomial::one(),
            PhaseCoefficient::rational(ratio(1, 3)),
        );
        let unsupported = BTreeMap::from([(
            ExactEntry {
                constraints: Vec::new(),
            },
            BTreeMap::from([(unsupported, KernelScalar::Rational(integer(1)))]),
        )]);
        assert!(collapse(&unsupported).is_none());
    }

    #[test]
    fn collapsed_product_preserves_all_multiplicities_phases_and_guards() {
        let guard = KernelBooleanPolynomial::variable(KernelVariable::InputBra(0));
        let mut sum = WorkingTerm {
            constraints: vec![guard.clone()],
            paths: BTreeSet::new(),
            coefficient: KernelScalar::Rational(integer(3)),
            phase: KernelPhasePolynomial::default(),
        };
        for index in 0..2 {
            let v = KernelVariable::PathKet {
                term: 0,
                path: 2 * index,
            };
            let w = KernelVariable::PathKet {
                term: 0,
                path: 2 * index + 1,
            };
            sum.paths.extend([v.clone(), w.clone()]);
            sum.phase.add_boolean(
                &KernelBooleanPolynomial::variable(v).and(&KernelBooleanPolynomial::variable(w)),
                PhaseCoefficient::rational(ratio(1, 2)),
            );
        }
        let mut exact = ExactTerm {
            constraints: vec![guard],
            coefficient: KernelScalar::Rational(integer(12)),
            phase: KernelPhasePolynomial::default(),
        };
        assert!(collapsed_product_equal(&sum, &exact));
        assert!(matches(
            &Reduction::Exact(exact.clone()),
            &Reduction::Sum(Box::new(sum.clone()))
        ));
        exact.coefficient = KernelScalar::Rational(integer(6));
        assert!(!collapsed_product_equal(&sum, &exact));
        exact.coefficient = KernelScalar::Rational(integer(12));
        exact.constraints.clear();
        assert!(!collapsed_product_equal(&sum, &exact));
        exact.constraints = sum.constraints.clone();
        exact.phase.add_boolean(
            &KernelBooleanPolynomial::variable(KernelVariable::InputKet(0)),
            PhaseCoefficient::rational(ratio(1, 4)),
        );
        assert!(!collapsed_product_equal(&sum, &exact));
    }

    #[test]
    fn single_atom_bound_factor_keeps_its_new_selector_in_common() {
        let v = KernelVariable::PathKet { term: 0, path: 0 };
        let w = KernelVariable::PathKet { term: 0, path: 1 };
        let u = KernelVariable::PathBra { term: 0, path: 0 };
        let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(
            &KernelBooleanPolynomial::variable(v.clone())
                .and(&KernelBooleanPolynomial::variable(w.clone())),
            PhaseCoefficient::rational(ratio(1, 2)),
        );
        phase.add_boolean(
            &KernelBooleanPolynomial::variable(u.clone()),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
        let source = WorkingTerm {
            paths: BTreeSet::from([v, w.clone(), u]),
            constraints: vec![x.and(&KernelBooleanPolynomial::variable(w)).xor(&x)],
            coefficient: KernelScalar::Rational(integer(1)),
            phase,
        };
        let mut budget = ReductionBudget {
            splits: MAX_RESIDUAL_SPLITS,
            products: MAX_FACTOR_PRODUCTS,
            phase_cells: MAX_FACTOR_PHASE_CELLS,
        };
        let product = product(&source, &mut budget).unwrap();
        assert_eq!(
            product.common.first_key_value().unwrap().0.constraints,
            vec![x]
        );
        assert_eq!(product.factors.len(), 1);
        let mut expanded = product.common;
        for factor in product.factors {
            expanded = multiply_aggregates(expanded, factor, &mut budget).unwrap();
        }
        // Exact value is 2*[x=0]*(1+zeta_8), not an unguarded constant.
        let at_one = restrict_aggregate(&expanded, &KernelVariable::InputKet(0), true).unwrap();
        assert!(at_one.is_empty());
        let at_zero = restrict_aggregate(&expanded, &KernelVariable::InputKet(0), false).unwrap();
        let mut expected = ExactAggregate::new();
        for turns in [ratio(0, 1), ratio(1, 8)] {
            let mut phase = KernelPhasePolynomial::default();
            phase.add_boolean(
                &KernelBooleanPolynomial::one(),
                PhaseCoefficient::rational(turns),
            );
            accumulate_exact_term(
                ExactTerm {
                    constraints: Vec::new(),
                    coefficient: KernelScalar::Rational(integer(2)),
                    phase,
                },
                &mut expected,
                &mut 0,
            )
            .unwrap();
        }
        assert_eq!(at_zero, expected);
    }

    fn independent(count: usize, bra: bool) -> WorkingTerm {
        let mut source = WorkingTerm {
            paths: BTreeSet::new(),
            constraints: vec![KernelBooleanPolynomial::variable(KernelVariable::InputBra(
                0,
            ))],
            coefficient: KernelScalar::Rational(integer(1)),
            phase: KernelPhasePolynomial::default(),
        };
        for index in 0..count {
            let path = if bra {
                KernelVariable::PathBra {
                    term: 17,
                    path: count - index,
                }
            } else {
                KernelVariable::PathKet {
                    term: 0,
                    path: index,
                }
            };
            source.paths.insert(path.clone());
            source.phase.add_boolean(
                &KernelBooleanPolynomial::variable(path).and(&KernelBooleanPolynomial::variable(
                    KernelVariable::InputKet(index),
                )),
                PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        source
    }

    fn residual(term: WorkingTerm) -> Reduction {
        Reduction::Sum(Box::new(term))
    }

    #[test]
    fn complete_component_consumption_keeps_weights_guards_and_ownership() {
        let left = independent(4, false);
        let right = independent(4, true);
        let l = factor_phase_sums(&left).unwrap();
        let r = factor_phase_sums(&right).unwrap();
        assert!(matches_components(l.clone(), r.clone()));
        let mut wrong = r.clone();
        wrong.pop();
        assert!(!matches_components(l.clone(), wrong));
        let mut wrong = r.clone();
        wrong[0].coefficient = KernelScalar::Rational(integer(3));
        assert!(!matches_components(l.clone(), wrong));
        let mut wrong = r.clone();
        wrong[0]
            .constraints
            .push(KernelBooleanPolynomial::variable(KernelVariable::InputBra(
                99,
            )));
        assert!(!matches_components(l.clone(), wrong));
        let mut wrong = r.clone();
        wrong.push(wrong[1].clone());
        assert!(!matches_components(l.clone(), wrong));
        let mut wrong = r.clone();
        let undeclared = KernelVariable::PathKet { term: 999, path: 0 };
        wrong[1]
            .constraints
            .push(KernelBooleanPolynomial::variable(undeclared));
        assert!(!matches_components(l.clone(), wrong));
        let mut wrong = r.clone();
        wrong[0]
            .paths
            .insert(KernelVariable::PathBra { term: 999, path: 0 });
        assert!(!matches_components(l.clone(), wrong));
        let mut oversized = r.clone();
        oversized[1]
            .constraints
            .resize(65, KernelBooleanPolynomial::zero());
        assert!(!matches_components(l.clone(), oversized));
        assert!(!matches_components(l, Vec::new()));
    }

    #[test]
    fn product_certificate_avoids_exponential_convolution_and_checks_all_factors() {
        let left = independent(20, false);
        let right = independent(20, true);
        assert!(reduce_reductions(std::iter::once(residual(left.clone()))).is_none());
        assert!(matches(&residual(left.clone()), &residual(right.clone())));
        assert!(!matches(
            &residual(left.clone()),
            &residual(independent(19, true))
        ));
        let mut wrong = right.clone();
        wrong.coefficient = KernelScalar::Rational(integer(2));
        assert!(!matches(&residual(left.clone()), &residual(wrong)));
        let mut wrong = right;
        wrong.constraints[0] = wrong.constraints[0].complement();
        assert!(!matches(&residual(left), &residual(wrong)));
    }

    #[test]
    fn extracted_units_are_replayed_and_vacuous_factors_keep_multiplicity() {
        let mut left = independent(12, false);
        left.paths
            .insert(KernelVariable::PathKet { term: 0, path: 99 });
        left.coefficient = KernelScalar::Rational(ratio(1, 2));
        let right = independent(12, true);
        assert!(matches(&residual(left.clone()), &residual(right.clone())));
        left.coefficient = KernelScalar::Rational(integer(1));
        assert!(!matches(&residual(left), &residual(right)));
    }

    #[test]
    fn factored_refusal_is_read_only_and_never_an_omitted_factor() {
        let left = independent(10, false);
        let before_paths = left.paths.clone();
        let before_phase = left.phase.clone();
        let mut budget = ReductionBudget {
            splits: 0,
            products: MAX_FACTOR_PRODUCTS,
            phase_cells: MAX_FACTOR_PHASE_CELLS,
        };
        assert!(product(&left, &mut budget).is_none());
        assert_eq!(left.paths, before_paths);
        assert_eq!(left.phase, before_phase);
        assert!(!matches(&Reduction::Residual, &residual(left.clone())));
        let mut invalid = left;
        invalid
            .paths
            .remove(&KernelVariable::PathKet { term: 0, path: 0 });
        assert!(!eligible(&invalid));
        assert!(!matches(&residual(invalid.clone()), &residual(invalid)));
    }

    fn atom_sum(
        selector: Vec<KernelBooleanPolynomial>,
        phases: Vec<KernelPhasePolynomial>,
    ) -> ExactAggregate {
        let mut sum = ExactAggregate::new();
        let mut atoms = 0;
        for phase in phases {
            accumulate_exact_term(
                ExactTerm {
                    constraints: selector.clone(),
                    coefficient: KernelScalar::Rational(integer(1)),
                    phase,
                },
                &mut sum,
                &mut atoms,
            )
            .unwrap();
        }
        sum
    }

    fn phase(variable: KernelVariable, denominator: i64) -> KernelPhasePolynomial {
        let mut phase = KernelPhasePolynomial::default();
        phase.add_boolean(
            &KernelBooleanPolynomial::variable(variable),
            PhaseCoefficient::rational(ratio(1, denominator)),
        );
        phase
    }

    fn test_budget() -> ReductionBudget {
        ReductionBudget {
            splits: 4095,
            products: MAX_FACTOR_PRODUCTS,
            phase_cells: MAX_FACTOR_PHASE_CELLS,
        }
    }

    #[test]
    fn relative_unit_interpolation_checks_zero_leaves_scale_and_every_phase() {
        let variables = [
            KernelVariable::InputKet(0),
            KernelVariable::InputBra(0),
            KernelVariable::ClassicalOutput(0),
            KernelVariable::ClassicalOutput(1),
        ];
        let [x, y, c, d] = variables.clone().map(KernelBooleanPolynomial::variable);
        let mut p = KernelPhasePolynomial::default();
        for (row, turns) in [(&y, ratio(1, 2)), (&c, ratio(3, 4)), (&d, ratio(1, 2))] {
            p.add_boolean(row, PhaseCoefficient::rational(turns));
        }
        // L=[x=y]+[x=y XOR c](-1)^(y+d)(-i)^c.
        let mut left = atom_sum(vec![x.xor(&y)], vec![KernelPhasePolynomial::default()]);
        for (entry, coefficients) in atom_sum(vec![x.xor(&y).xor(&c)], vec![p]) {
            for (phase, coefficient) in coefficients {
                accumulate_exact_term(
                    ExactTerm {
                        constraints: entry.constraints.clone(),
                        coefficient,
                        phase,
                    },
                    &mut left,
                    &mut 0,
                )
                .unwrap();
            }
        }
        // R=(1+(-1)^(x+d)i^c)(1+(-1)^(y+d)i^c).
        let factors = [&x, &y].map(|row| {
            let mut p = KernelPhasePolynomial::default();
            p.add_boolean(&row.xor(&d), PhaseCoefficient::rational(ratio(1, 2)));
            p.add_boolean(&c, PhaseCoefficient::rational(ratio(1, 4)));
            atom_sum(vec![], vec![KernelPhasePolynomial::default(), p])
        });
        let right = multiply_aggregates(factors[0].clone(), factors[1].clone(), &mut test_budget())
            .unwrap();
        let unit = relative_phase_unit(
            &left,
            &right,
            &mut test_budget(),
            &mut 4095,
            &mut witness::ConstantBudget::default(),
        )
        .unwrap();
        let reconstructed =
            multiply_aggregates(right.clone(), unit.clone(), &mut test_budget()).unwrap();
        assert!(equal(
            &left,
            &reconstructed,
            &mut 4095,
            &mut witness::ConstantBudget::default()
        ));
        // Independent integer bit formula for the ratio on all nonzero
        // entries: magnitude 1/2, quarter-turn exponent -c*(1+2*(y+d)).
        // R is zero precisely when c=0 and either x!=d or y!=d.
        for assignment in 0..16 {
            let bits = std::array::from_fn::<_, 4, _>(|i| (assignment >> i) & 1);
            let mut at_point = unit.clone();
            for (variable, bit) in variables.iter().zip(bits) {
                at_point = restrict_aggregate(&at_point, variable, bit != 0).unwrap();
            }
            if bits[2] == 0 && (bits[0] != bits[3] || bits[1] != bits[3]) {
                continue;
            }
            let (magnitude, turns) =
                witness::constant_monomial(&at_point, &mut witness::ConstantBudget::default())
                    .unwrap();
            assert_eq!(magnitude, ratio(1, 2));
            let exponent: i64 = -(bits[2] as i64) * (1 + 2 * (bits[1] + bits[3]) as i64);
            assert_eq!(
                PhaseCoefficient::rational(turns),
                PhaseCoefficient::rational(ratio(exponent, 4))
            );
        }
        let propose = |l: &ExactAggregate, r: &ExactAggregate| {
            relative_phase_unit(
                l,
                r,
                &mut test_budget(),
                &mut 4095,
                &mut witness::ConstantBudget::default(),
            )
        };
        let mut wrong_scale = left.clone();
        for coefficients in wrong_scale.values_mut() {
            for scalar in coefficients.values_mut() {
                *scalar = scalar.clone().multiply(KernelScalar::Select {
                    condition: c.clone(),
                    when_true: Box::new(KernelScalar::Rational(integer(2))),
                    when_false: Box::new(KernelScalar::Rational(integer(1))),
                });
            }
        }
        assert!(propose(&wrong_scale, &right).is_none()); // agrees at all-zero
        let mut missing = left.clone();
        missing.pop_last();
        assert!(propose(&missing, &right).is_none());
        let zero = ExactAggregate::new();
        assert!(propose(&left, &zero).is_none());
        assert!(propose(&zero, &right).is_none());
        let mut exhausted = test_budget();
        exhausted.phase_cells = 0;
        assert!(
            relative_phase_unit(
                &left,
                &right,
                &mut exhausted,
                &mut 4095,
                &mut witness::ConstantBudget::default()
            )
            .is_none()
        );
        assert!(
            relative_phase_unit(
                &left,
                &right,
                &mut test_budget(),
                &mut 0,
                &mut witness::ConstantBudget::default()
            )
            .is_none()
        );
        // Common selectors may be removed only as a stronger proof. A
        // different selector on one side remains and prevents the identity.
        let guard = atom_sum(
            vec![KernelBooleanPolynomial::variable(KernelVariable::InputKet(
                50,
            ))],
            vec![KernelPhasePolynomial::default()],
        );
        let guarded_left = multiply_aggregates(left, guard.clone(), &mut test_budget()).unwrap();
        let guarded_right = multiply_aggregates(right.clone(), guard, &mut test_budget()).unwrap();
        assert!(propose(&guarded_left, &guarded_right).is_some());
        assert!(propose(&guarded_left, &right).is_none());
        let too_many = atom_sum(
            vec![],
            vec![{
                let mut p = KernelPhasePolynomial::default();
                for i in 0..9 {
                    p.add_boolean(
                        &KernelBooleanPolynomial::variable(KernelVariable::InputKet(i)),
                        PhaseCoefficient::rational(ratio(1, 8)),
                    );
                }
                p
            }],
        );
        assert!(propose(&too_many, &too_many).is_none());
    }

    #[test]
    fn paired_factor_matching_checks_complete_product_units_and_consumption() {
        let guard = vec![KernelBooleanPolynomial::variable(
            KernelVariable::ClassicalOutput(0),
        )];
        let unit = atom_sum(vec![], vec![KernelPhasePolynomial::default()]);
        let a = atom_sum(
            guard.clone(),
            vec![
                KernelPhasePolynomial::default(),
                phase(KernelVariable::InputKet(0), 4),
            ],
        );
        let b = atom_sum(
            guard.clone(),
            vec![
                KernelPhasePolynomial::default(),
                phase(KernelVariable::InputBra(0), 8),
            ],
        );
        let c = atom_sum(
            guard,
            vec![
                KernelPhasePolynomial::default(),
                phase(KernelVariable::InputKet(1), 2),
            ],
        );
        let ab = multiply_aggregates(a.clone(), b.clone(), &mut test_budget()).unwrap();
        let right = Product {
            common: unit.clone(),
            factors: vec![c.clone(), b.clone(), a.clone()],
        };
        let left = Product {
            common: unit.clone(),
            factors: vec![ab.clone(), c],
        };
        let check = |left: &Product, right: &Product| {
            bijection(
                left,
                right,
                &mut test_budget(),
                &mut 4095,
                &mut witness::ConstantBudget::default(),
                (&mut 128, &mut BTreeSet::new()),
            )
        };
        assert!(check(&left, &right));
        let mut wrong = left.clone();
        wrong.factors[0].values_mut().next().unwrap().pop_last();
        assert!(!check(&wrong, &right));
        let mut missing = right.clone();
        missing.factors.pop();
        assert!(!check(&left, &missing));
        let scale = atom_sum(vec![], vec![phase(KernelVariable::InputKet(2), 8)]);
        let mut scaled = left;
        scaled.factors[0] = multiply_aggregates(ab, scale.clone(), &mut test_budget()).unwrap();
        assert!(!check(&scaled, &right));
        let mut compensated = right.clone();
        compensated.common = scale;
        assert!(check(&scaled, &compensated));
        assert!(
            matching_pair_unit(
                &scaled.factors[0],
                &[&a, &b],
                &mut test_budget(),
                &mut 4095,
                &mut witness::ConstantBudget::default(),
                &mut 0
            )
            .is_none()
        );
        let mut budget = test_budget();
        budget.phase_cells = 0;
        assert!(
            matching_pair_unit(
                &scaled.factors[0],
                &[&a, &b],
                &mut budget,
                &mut 4095,
                &mut witness::ConstantBudget::default(),
                &mut 128
            )
            .is_none()
        );
    }

    #[test]
    fn product_cofactors_retain_zero_factors_and_require_both_branches() {
        let x = phase(KernelVariable::InputKet(0), 2);
        let unit = atom_sum(vec![], vec![KernelPhasePolynomial::default()]);
        let factor = atom_sum(vec![], vec![KernelPhasePolynomial::default(), x.clone()]);
        // (-1)^x (1+(-1)^x) = 1+(-1)^x, but the common units
        // differ. The x=1 branch is zero, not a cancelled nonzero factor.
        let left = Product {
            common: atom_sum(vec![], vec![x]),
            factors: vec![factor.clone()],
        };
        let right = Product {
            common: unit.clone(),
            factors: vec![factor],
        };
        let check = |left, right, depth| {
            let mut free = MAX_FREE_SPLITS;
            let mut probes = MAX_MATCH_PROBES;
            equal_products(
                left,
                right,
                &mut test_budget(),
                &mut free,
                &mut witness::ConstantBudget::default(),
                &mut probes,
                depth,
            )
        };
        assert!(check(left.clone(), right.clone(), MAX_PRODUCT_SPLIT_DEPTH));
        let difference = aggregate_difference(left.common.clone(), right.common.clone()).unwrap();
        let mut cells = MAX_FACTOR_PHASE_CELLS;
        assert!(!zero_product(
            vec![difference, left.factors[0].clone()],
            &mut 0,
            &mut witness::ConstantBudget::default(),
            &mut cells,
            0
        ));
        assert!(check(left, right.clone(), 0));
        // Both sides agree at x=0; they differ at x=1. One good
        // cofactor alone must never be enough to prove equality.
        let wrong = Product {
            common: unit.clone(),
            factors: vec![unit],
        };
        let mut right = right;
        right.common.values_mut().for_each(|atoms| {
            atoms
                .values_mut()
                .for_each(|coefficient| *coefficient = KernelScalar::Rational(ratio(1, 2)))
        });
        assert!(!check(wrong, right, 0));
    }

    #[test]
    fn tensor_refinement_replays_and_retains_its_own_selector() {
        let guard = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(7));
        let left = atom_sum(
            vec![guard.clone()],
            vec![
                KernelPhasePolynomial::default(),
                phase(KernelVariable::InputKet(0), 8),
            ],
        );
        let right = atom_sum(
            vec![guard.clone()],
            vec![
                KernelPhasePolynomial::default(),
                phase(KernelVariable::InputBra(0), 8),
            ],
        );
        let mut budget = test_budget();
        let original = multiply_aggregates(left, right, &mut budget).unwrap();
        let factors = refine_tensor(original.clone(), &mut budget).unwrap();
        assert_eq!(factors.len(), 2);
        for factor in &factors {
            assert!(
                factor
                    .keys()
                    .all(|entry| entry.constraints.contains(&guard))
            );
            assert!(
                restrict_aggregate(factor, &KernelVariable::QuantumOutputKet(7), true)
                    .unwrap()
                    .is_empty()
            );
        }
        assert_eq!(
            multiply_aggregates(factors[0].clone(), factors[1].clone(), &mut budget).unwrap(),
            original
        );
        let (normalized, scalar, phase) = normalize_factor(original.clone()).unwrap();
        let mut unit = ExactAggregate::new();
        accumulate_exact_term(
            ExactTerm {
                constraints: vec![],
                coefficient: KernelScalar::Rational(scalar),
                phase,
            },
            &mut unit,
            &mut 0,
        )
        .unwrap();
        assert_eq!(
            multiply_aggregates(normalized, unit, &mut budget).unwrap(),
            original
        );
    }

    #[test]
    fn all_two_bit_projector_phase_pairs_match_independent_truth_tables() {
        // Independent two-bit truth tables use four bits (00,01,10,11).
        // The proof still sees ANF/phase syntax, never these expected tables.
        let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
        let y = KernelBooleanPolynomial::variable(KernelVariable::InputKet(1));
        let monomials = [
            KernelBooleanPolynomial::one(),
            x.clone(),
            y.clone(),
            x.and(&y),
        ];
        let tables = [0b1111u8, 0b1010, 0b1100, 0b1000];
        let make = |mask: usize| {
            let mut polynomial = KernelBooleanPolynomial::zero();
            let mut table = 0u8;
            for index in 0..4 {
                if mask & (1 << index) != 0 {
                    polynomial = polynomial.xor(&monomials[index]);
                    table ^= tables[index];
                }
            }
            let mut phase = KernelPhasePolynomial::default();
            phase.add_boolean(&polynomial, PhaseCoefficient::rational(ratio(1, 2)));
            (phase, table)
        };
        for f in 0..16 {
            for g in 0..16 {
                let (f_phase, f_table) = make(f);
                let (g_phase, g_table) = make(g);
                let factor = atom_sum(vec![], vec![KernelPhasePolynomial::default(), f_phase]);
                let left = Product {
                    common: atom_sum(vec![], vec![g_phase]),
                    factors: vec![factor.clone()],
                };
                let right = Product {
                    common: atom_sum(vec![], vec![KernelPhasePolynomial::default()]),
                    factors: vec![factor],
                };
                let mut free = MAX_FREE_SPLITS;
                let mut probes = MAX_MATCH_PROBES;
                let actual = equal_products(
                    left,
                    right,
                    &mut test_budget(),
                    &mut free,
                    &mut witness::ConstantBudget::default(),
                    &mut probes,
                    0,
                );
                let expected = (g_table & !f_table & 0b1111) == 0;
                assert_eq!(actual, expected, "f={f:04b} g={g:04b}");
            }
        }
    }

    #[test]
    fn dominant_difference_coordinate_exposes_a_zero_factor_without_cancellation() {
        let y = KernelVariable::QuantumOutputBra(99);
        let mut gated = KernelPhasePolynomial::default();
        for index in 0..20 {
            gated.add_boolean(
                &KernelBooleanPolynomial::variable(y.clone()).and(
                    &KernelBooleanPolynomial::variable(KernelVariable::InputKet(index)),
                ),
                PhaseCoefficient::rational(ratio(1, 2)),
            );
        }
        let one = atom_sum(vec![], vec![KernelPhasePolynomial::default()]);
        let difference = aggregate_difference(one, atom_sum(vec![], vec![gated])).unwrap();
        let check = |denominator| {
            let factor = atom_sum(
                vec![],
                vec![
                    KernelPhasePolynomial::default(),
                    phase(y.clone(), denominator),
                ],
            );
            let mut free = MAX_FREE_SPLITS;
            let mut cells = MAX_FACTOR_PHASE_CELLS;
            let result = zero_product(
                vec![difference.clone(), factor],
                &mut free,
                &mut witness::ConstantBudget::default(),
                &mut cells,
                0,
            );
            if denominator == 2 {
                assert_eq!(free, MAX_FREE_SPLITS - 1);
            }
            result
        };
        // [1-(-1)^(y*g)] [1+(-1)^y] is zero: at y=0 the first
        // factor vanishes, at y=1 the second does. Lexical splitting on
        // twenty earlier inputs cannot reach y within depth twelve.
        assert!(check(2));
        // Replacing (-1)^y by i^y is nonzero at y=1 and any odd input
        // parity: 2*(1+i). Identical support is not a zero certificate.
        assert!(!check(4));
    }

    #[test]
    fn mixed_private_cofactors_refine_products_and_retain_single_atom_guards() {
        let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
        let y = KernelBooleanPolynomial::variable(KernelVariable::InputBra(0));
        let mut xy = KernelPhasePolynomial::default();
        xy.add_boolean(&x.and(&y), PhaseCoefficient::rational(ratio(1, 2)));
        let a = atom_sum(vec![], vec![KernelPhasePolynomial::default(), xy]);
        let b = atom_sum(
            vec![],
            vec![
                KernelPhasePolynomial::default(),
                phase(KernelVariable::InputKet(1), 2),
            ],
        );
        let unit = atom_sum(vec![], vec![KernelPhasePolynomial::default()]);
        let mut budget = test_budget();
        let left = Product {
            common: unit.clone(),
            factors: vec![multiply_aggregates(a.clone(), b.clone(), &mut budget).unwrap()],
        };
        let right = Product {
            common: unit.clone(),
            factors: vec![a, b],
        };
        let mut free = MAX_FREE_SPLITS;
        let mut probes = MAX_MATCH_PROBES;
        assert!(equal_products(
            left,
            right,
            &mut budget,
            &mut free,
            &mut witness::ConstantBudget::default(),
            &mut probes,
            0
        ));
        let guard = KernelBooleanPolynomial::variable(KernelVariable::InputKet(7));
        let source = Product {
            common: unit,
            factors: vec![atom_sum(
                vec![guard.clone()],
                vec![phase(KernelVariable::InputBra(2), 8)],
            )],
        };
        let restricted =
            restrict_product(&source, &KernelVariable::InputBra(2), false, &mut budget).unwrap();
        assert!(restricted.factors.is_empty());
        assert!(
            restricted
                .common
                .keys()
                .all(|entry| entry.constraints.contains(&guard))
        );
        assert!(
            restrict_aggregate(&restricted.common, &KernelVariable::InputKet(7), true)
                .unwrap()
                .is_empty()
        );
    }

    #[test]
    fn binomial_refinement_checks_every_cell_and_keeps_mixed_private_phases() {
        let guard = KernelBooleanPolynomial::variable(KernelVariable::InputKet(7));
        let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
        let y = KernelBooleanPolynomial::variable(KernelVariable::InputBra(0));
        let mut mixed = KernelPhasePolynomial::default();
        mixed.add_boolean(&x.and(&y), PhaseCoefficient::rational(ratio(1, 8)));
        let left = atom_sum(
            vec![guard.clone()],
            vec![KernelPhasePolynomial::default(), mixed],
        );
        let right = atom_sum(
            vec![guard.clone()],
            vec![
                KernelPhasePolynomial::default(),
                phase(KernelVariable::InputKet(1), 8),
            ],
        );
        let mut budget = test_budget();
        let source = multiply_aggregates(left, right, &mut budget).unwrap();
        assert!(factor_free_tensor(&source, &mut budget).is_none());
        let [a, b] = factor_binomials(&source, &mut budget).unwrap();
        assert!(
            a.keys()
                .chain(b.keys())
                .all(|entry| entry.constraints.contains(&guard))
        );
        assert_eq!(multiply_aggregates(a, b, &mut budget).unwrap(), source);
        let mut wrong = source;
        *wrong
            .values_mut()
            .next()
            .unwrap()
            .last_entry()
            .unwrap()
            .get_mut() = KernelScalar::Rational(integer(2));
        assert!(factor_binomials(&wrong, &mut budget).is_none());
        let mut exhausted = test_budget();
        exhausted.products = 0;
        assert!(factor_binomials(&wrong, &mut exhausted).is_none());
    }

    #[test]
    fn factor_unit_matching_transfers_phase_and_rejects_missing_compensation() {
        let one = atom_sum(vec![], vec![KernelPhasePolynomial::default()]);
        let unit = atom_sum(vec![], vec![phase(KernelVariable::InputBra(0), 2)]);
        let factor = atom_sum(
            vec![],
            vec![
                KernelPhasePolynomial::default(),
                phase(KernelVariable::InputKet(0), 8),
            ],
        );
        let left = Product {
            common: one.clone(),
            factors: vec![factor.clone()],
        };
        let right_factor = multiply_aggregates(factor, unit.clone(), &mut test_budget()).unwrap();
        let right = Product {
            common: unit,
            factors: vec![right_factor],
        };
        let check = |left, right| {
            let mut free = MAX_FREE_SPLITS;
            let mut probes = MAX_MATCH_PROBES;
            equal_products(
                left,
                right,
                &mut test_budget(),
                &mut free,
                &mut witness::ConstantBudget::default(),
                &mut probes,
                0,
            )
        };
        assert!(check(left.clone(), right.clone()));
        assert!(!check(
            left,
            Product {
                common: one,
                ..right
            }
        ));
    }

    #[test]
    fn conditional_binomial_orientation_replays_all_flip_assignments() {
        let a = KernelVariable::QuantumOutputKet(1);
        let b = KernelVariable::QuantumOutputBra(1);
        let flip = KernelBooleanPolynomial::variable(a.clone())
            .xor(&KernelBooleanPolynomial::variable(b.clone()));
        let mut right_phase = phase(KernelVariable::InputKet(0), 2);
        right_phase.add_boolean(
            &KernelBooleanPolynomial::one(),
            PhaseCoefficient::rational(ratio(1, 1024)),
        );
        right_phase.add_boolean(
            &KernelBooleanPolynomial::variable(a.clone()),
            PhaseCoefficient::rational(ratio(1, 4)),
        );
        let mut budget = test_budget();
        let unit_phase = negative_gated_phase(&right_phase, &flip, &mut budget).unwrap();
        let mut left_phase = right_phase.clone();
        add_phase(&mut left_phase, &unit_phase).unwrap();
        add_phase(&mut left_phase, &unit_phase).unwrap();
        let guard = KernelBooleanPolynomial::variable(KernelVariable::InputBra(7));
        let left = atom_sum(
            vec![guard.clone()],
            vec![KernelPhasePolynomial::default(), left_phase.clone()],
        );
        let right = atom_sum(
            vec![guard.clone()],
            vec![KernelPhasePolynomial::default(), right_phase],
        );
        let unit = conditional_binomial_unit(&left, &right, &mut budget).unwrap();
        let replay = multiply_aggregates(right.clone(), unit, &mut budget).unwrap();
        for x in [false, true] {
            for y in [false, true] {
                // Independent literal cofactors check the whole guarded sum.
                let restrict = |source| {
                    restrict_aggregate(&restrict_aggregate(source, &a, x).unwrap(), &b, y).unwrap()
                };
                assert_eq!(restrict(&left), restrict(&replay));
            }
        }
        let mut bad_phase = left_phase;
        bad_phase.add_boolean(
            &KernelBooleanPolynomial::one(),
            PhaseCoefficient::rational(ratio(1, 16)),
        );
        let wrong = atom_sum(
            vec![guard],
            vec![KernelPhasePolynomial::default(), bad_phase],
        );
        assert!(conditional_binomial_unit(&wrong, &right, &mut budget).is_none());
        let mut exhausted = test_budget();
        exhausted.phase_cells = 0;
        assert!(conditional_binomial_unit(&left, &right, &mut exhausted).is_none());
    }

    #[test]
    fn orientation_tree_handles_nonlinear_flips_and_refuses_one_bad_branch() {
        let a = KernelVariable::QuantumOutputKet(0);
        let b = KernelVariable::QuantumOutputBra(0);
        let flip = KernelBooleanPolynomial::variable(a.clone())
            .and(&KernelBooleanPolynomial::variable(b.clone()))
            .complement();
        let right_phase = phase(KernelVariable::InputKet(0), 8);
        let mut budget = test_budget();
        let unit = negative_gated_phase(&right_phase, &flip, &mut budget).unwrap();
        let mut left_phase = right_phase.clone();
        add_phase(&mut left_phase, &unit).unwrap();
        add_phase(&mut left_phase, &unit).unwrap();
        let proved = orientation_phase(&left_phase, &right_phase, &mut budget, 0).unwrap();
        for x in [false, true] {
            for y in [false, true] {
                for input in [false, true] {
                    let specialize = |mut phase: KernelPhasePolynomial| {
                        for (variable, value) in [
                            (a.clone(), x),
                            (b.clone(), y),
                            (KernelVariable::InputKet(0), input),
                        ] {
                            phase.substitute(&variable, &KernelBooleanPolynomial::from(value));
                        }
                        phase
                    };
                    assert_eq!(specialize(proved.clone()), specialize(unit.clone()));
                }
            }
        }
        assert!(orientation_phase(&left_phase, &right_phase, &mut budget, 4).is_none());
        left_phase.add_boolean(
            &KernelBooleanPolynomial::variable(a).and(&KernelBooleanPolynomial::variable(b)),
            PhaseCoefficient::rational(ratio(1, 16)),
        );
        assert!(orientation_phase(&left_phase, &right_phase, &mut budget, 0).is_none());
    }

    #[test]
    fn wide_orientation_proves_all_eight_branches_with_bounded_syntax() {
        let variables = [
            KernelVariable::QuantumOutputKet(0),
            KernelVariable::QuantumOutputBra(0),
            KernelVariable::QuantumOutputBra(1),
        ];
        let flip = variables
            .iter()
            .fold(KernelBooleanPolynomial::zero(), |sum, var| {
                sum.xor(&KernelBooleanPolynomial::variable(var.clone()))
            });
        let make = |count| {
            let mut right = KernelPhasePolynomial::default();
            for index in 0..count {
                right.add_boolean(
                    &KernelBooleanPolynomial::variable(KernelVariable::InputKet(index)),
                    PhaseCoefficient::rational(ratio(1, 64)),
                );
            }
            let mut left = right.clone();
            for (monomial, coefficient) in right.terms() {
                left.add_boolean(
                    &flip.and(&KernelBooleanPolynomial::from_monomial(monomial.clone())),
                    coefficient.scaled(BigInt::from(-2)),
                );
            }
            (left, right)
        };
        let (left, right) = make(64);
        assert_eq!(left.term_count(), MAX_ORIENTATION_LEFT_TERMS);
        let mut budget = test_budget();
        let unit = orientation_phase(&left, &right, &mut budget, 0).unwrap();
        let proposed = parity_orientation_phase(&left, &right, &mut test_budget()).unwrap();
        assert_eq!(proposed, unit);
        let negative = KernelPhasePolynomial::difference(&KernelPhasePolynomial::default(), &right);
        for bits in 0u8..8 {
            let mut actual = unit.clone();
            let mut oriented = left.clone();
            for (index, variable) in variables.iter().enumerate() {
                let value = KernelBooleanPolynomial::from(bits & (1 << index) != 0);
                actual.substitute(variable, &value);
                oriented.substitute(variable, &value);
            }
            // Check the entire remaining 64-coordinate polynomial, not a
            // sample of those inputs. The expected parity is computed here
            // directly from the eight literal assignments.
            let odd = bits.count_ones() % 2 != 0;
            assert_eq!(
                actual,
                if odd {
                    negative.clone()
                } else {
                    KernelPhasePolynomial::default()
                }
            );
            assert_eq!(oriented, if odd { negative.clone() } else { right.clone() });
        }
        let mut wrong = left.clone();
        let corner = variables
            .iter()
            .fold(KernelBooleanPolynomial::one(), |term, var| {
                term.and(&KernelBooleanPolynomial::variable(var.clone()))
            });
        // Reuse an existing monomial: stay within 512 terms, but corrupt
        // exactly the all-one orientation branch.
        wrong.add_boolean(
            &corner.and(&KernelBooleanPolynomial::variable(
                KernelVariable::InputKet(0),
            )),
            PhaseCoefficient::rational(ratio(1, 128)),
        );
        assert_eq!(wrong.term_count(), left.term_count());
        assert!(parity_orientation_phase(&wrong, &right, &mut test_budget()).is_none());
        assert!(orientation_phase(&wrong, &right, &mut test_budget(), 0).is_none());
        let (oversized, oversized_right) = make(65);
        assert!(orientation_phase(&oversized, &oversized_right, &mut test_budget(), 0).is_none());
        let mut exhausted = test_budget();
        exhausted.phase_cells = 1;
        assert!(orientation_phase(&left, &right, &mut exhausted, 0).is_none());
        assert!(parity_orientation_phase(&left, &right, &mut exhausted).is_none());
    }

    #[test]
    fn large_parity_orientation_checks_all_sixty_four_branches_and_whole_polynomials() {
        let variables = (0..6)
            .map(KernelVariable::QuantumOutputBra)
            .collect::<Vec<_>>();
        let flip = variables
            .iter()
            .fold(KernelBooleanPolynomial::zero(), |p, v| {
                p.xor(&KernelBooleanPolynomial::variable(v.clone()))
            });
        let mut right = KernelPhasePolynomial::default();
        for i in 0..24 {
            right.add_boolean(
                &KernelBooleanPolynomial::variable(KernelVariable::InputKet(i)),
                PhaseCoefficient::rational(ratio(1, 4096)),
            );
        }
        let mut left = right.clone();
        for (m, c) in right.terms() {
            left.add_boolean(
                &flip.and(&KernelBooleanPolynomial::from_monomial(m.clone())),
                c.scaled(BigInt::from(-2)),
            );
        }
        assert_eq!(left.term_count(), 1536);
        assert!(orientation_phase(&left, &right, &mut test_budget(), 0).is_none());
        let mut budget = test_budget();
        let unit = large_parity_orientation_phase(&left, &right, &mut budget).unwrap();
        let needed = MAX_FACTOR_PHASE_CELLS - budget.phase_cells;
        let selector = vec![KernelBooleanPolynomial::variable(KernelVariable::InputBra(
            99,
        ))];
        let l = atom_sum(
            selector.clone(),
            vec![KernelPhasePolynomial::default(), left.clone()],
        );
        let r = atom_sum(
            selector.clone(),
            vec![KernelPhasePolynomial::default(), right.clone()],
        );
        let certified = conditional_binomial_unit(&l, &r, &mut test_budget()).unwrap();
        assert_eq!(certified, atom_sum(Vec::new(), vec![unit.clone()]));
        assert!(
            conditional_binomial_unit(
                &l,
                &atom_sum(
                    Vec::new(),
                    vec![KernelPhasePolynomial::default(), right.clone()]
                ),
                &mut test_budget()
            )
            .is_none()
        );
        let mut wrong_weight = r.clone();
        *wrong_weight
            .values_mut()
            .next()
            .unwrap()
            .values_mut()
            .next()
            .unwrap() = KernelScalar::Rational(integer(2));
        assert!(conditional_binomial_unit(&l, &wrong_weight, &mut test_budget()).is_none());
        let lp = Product {
            common: atom_sum(selector.clone(), vec![KernelPhasePolynomial::default()]),
            factors: vec![l],
        };
        let rp = Product {
            common: atom_sum(selector.clone(), vec![unit.clone()]),
            factors: vec![r],
        };
        assert!(compare_products(lp.clone(), rp.clone(), &mut test_budget()));
        let mut uncompensated = rp;
        uncompensated.common = atom_sum(selector, vec![KernelPhasePolynomial::default()]);
        assert!(!compare_products(lp, uncompensated, &mut test_budget()));
        for bits in 0u32..64 {
            let specialize = |mut p: KernelPhasePolynomial| {
                for (i, v) in variables.iter().enumerate() {
                    p.substitute(v, &KernelBooleanPolynomial::from(bits & (1 << i) != 0));
                }
                p
            };
            let negative =
                KernelPhasePolynomial::difference(&KernelPhasePolynomial::default(), &right);
            assert_eq!(
                specialize(unit.clone()),
                if bits.count_ones() % 2 != 0 {
                    negative.clone()
                } else {
                    KernelPhasePolynomial::default()
                }
            );
            assert_eq!(
                specialize(left.clone()),
                if bits.count_ones() % 2 != 0 {
                    negative
                } else {
                    right.clone()
                }
            );
        }
        let mut wrong = left.clone();
        wrong.add_term(
            KernelMonomial::from_variables(
                variables
                    .iter()
                    .cloned()
                    .chain([KernelVariable::InputKet(0)]),
            ),
            PhaseCoefficient::rational(ratio(1, 4096)),
        );
        assert_eq!(wrong.term_count(), 1536);
        assert!(large_parity_orientation_phase(&wrong, &right, &mut test_budget()).is_none());
        let mut short = test_budget();
        short.phase_cells = needed - 1;
        assert!(large_parity_orientation_phase(&left, &right, &mut short).is_none());
        let mut exact = test_budget();
        exact.phase_cells = needed;
        assert!(large_parity_orientation_phase(&left, &right, &mut exact).is_some());
        assert_eq!(exact.phase_cells, 0);
        let mut bound = left.clone();
        bound.add_term(
            KernelMonomial::variable(KernelVariable::PathKet { term: 0, path: 0 }),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
        assert!(large_parity_orientation_phase(&bound, &right, &mut test_budget()).is_none());
        let mut oversized = left;
        for i in 100..2200 {
            oversized.add_term(
                KernelMonomial::variable(KernelVariable::InputKet(i)),
                PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        assert!(large_parity_orientation_phase(&oversized, &right, &mut test_budget()).is_none());
    }

    #[test]
    fn literal_gate_charges_its_actual_single_product_bound() {
        let flip = KernelBooleanPolynomial::variable(KernelVariable::InputBra(0));
        let mut source = KernelPhasePolynomial::default();
        let mut expected = KernelPhasePolynomial::default();
        for index in 0..64 {
            let variable = KernelBooleanPolynomial::variable(KernelVariable::InputKet(index));
            source.add_boolean(&variable, PhaseCoefficient::rational(ratio(1, 8)));
            expected.add_boolean(
                &variable.and(&flip),
                PhaseCoefficient::rational(ratio(-1, 8)),
            );
        }
        let mut budget = test_budget();
        budget.phase_cells = 64 * 3; // 64 products, each one monomial + two variables.
        assert_eq!(
            negative_gated_phase(&source, &flip, &mut budget),
            Some(expected)
        );
        assert_eq!(budget.phase_cells, 0);
        budget.phase_cells = 64 * 3 - 1;
        assert!(negative_gated_phase(&source, &flip, &mut budget).is_none());
        assert_eq!(source.term_count(), 64);
    }

    #[test]
    fn larger_factor_inputs_still_require_bounded_total_syntax() {
        let mut term = independent(1, false);
        let path = KernelBooleanPolynomial::variable(term.paths.first().unwrap().clone());
        term.phase = KernelPhasePolynomial::default();
        for index in 0..30000 {
            let mut monomial = path.clone();
            for offset in 0..7 {
                monomial = monomial.and(&KernelBooleanPolynomial::variable(
                    KernelVariable::InputKet(7 * index + offset),
                ));
            }
            term.phase
                .add_boolean(&monomial, PhaseCoefficient::rational(ratio(1, 8)));
            if index == 4999 {
                assert!(term.phase.term_count() > 4096);
                assert!(eligible(&term));
            }
        }
        assert!(term.phase.term_count() < MAX_INPUT_PHASE_TERMS);
        assert!(
            !eligible(&term),
            "total syntax, not atom count alone, must be bounded"
        );
        let mut too_many_paths = independent(1, false);
        for path in 0..=MAX_INPUT_PATHS {
            too_many_paths
                .paths
                .insert(KernelVariable::PathKet { term: 0, path });
        }
        assert!(!eligible(&too_many_paths));
    }

    #[test]
    fn wide_input_admission_keeps_an_independent_phase_count_limit() {
        let mut term = independent(1, false);
        let path = KernelBooleanPolynomial::variable(term.paths.first().unwrap().clone());
        term.phase = KernelPhasePolynomial::default();
        for index in 0..=MAX_INPUT_PHASE_TERMS {
            term.phase.add_boolean(
                &path.and(&KernelBooleanPolynomial::variable(
                    KernelVariable::InputKet(index),
                )),
                PhaseCoefficient::rational(ratio(1, 8)),
            );
            if index == 34999 || index + 1 == MAX_INPUT_PHASE_TERMS {
                assert!(eligible(&term));
            }
        }
        // Low-degree syntax still fits 250000 cells, so this refusal is
        // independently due to the 65536 phase-term limit.
        assert_eq!(term.phase.term_count(), MAX_INPUT_PHASE_TERMS + 1);
        assert!(!eligible(&term));
    }

    #[test]
    fn many_small_factors_keep_storage_and_count_refusal_independent() {
        let left = independent(80, false);
        let right = independent(80, true);
        assert!(matches(&residual(left.clone()), &residual(right)));
        let too_many = independent(MAX_FACTORS + 1, false);
        assert!(eligible(&too_many));
        assert!(product(&too_many, &mut test_budget()).is_none());
        assert!(!matches(&residual(left), &residual(too_many)));
    }

    #[test]
    fn unit_collection_equals_sequential_multiplication_and_rejects_guards() {
        let mut scalar = integer(1);
        let mut phase_sum = KernelPhasePolynomial::default();
        let mut budget = test_budget();
        let mut expected = atom_sum(vec![], vec![KernelPhasePolynomial::default()]);
        for index in 0..24 {
            let mut unit = atom_sum(vec![], vec![phase(KernelVariable::InputKet(index), 8)]);
            *unit
                .values_mut()
                .next()
                .unwrap()
                .values_mut()
                .next()
                .unwrap() = KernelScalar::Rational(if index % 2 == 0 {
                integer(-2)
            } else {
                ratio(1, 2)
            });
            collect_unit(&unit, &mut scalar, &mut phase_sum, &mut budget).unwrap();
            expected = multiply_aggregates(expected, unit, &mut budget).unwrap();
        }
        let mut actual = ExactAggregate::new();
        accumulate_exact_term(
            ExactTerm {
                constraints: vec![],
                coefficient: KernelScalar::Rational(scalar.clone()),
                phase: phase_sum.clone(),
            },
            &mut actual,
            &mut 0,
        )
        .unwrap();
        assert_eq!(actual, expected);
        let guarded = atom_sum(
            vec![KernelBooleanPolynomial::variable(KernelVariable::InputKet(
                0,
            ))],
            vec![KernelPhasePolynomial::default()],
        );
        assert!(collect_unit(&guarded, &mut scalar, &mut phase_sum, &mut budget).is_none());
        assert!(
            collect_unit(
                &ExactAggregate::new(),
                &mut scalar,
                &mut phase_sum,
                &mut budget
            )
            .is_none()
        );
        let mut zero_budget = test_budget();
        zero_budget.phase_cells = 0;
        assert!(collect_unit(&actual, &mut scalar, &mut phase_sum, &mut zero_budget).is_none());
    }
}
