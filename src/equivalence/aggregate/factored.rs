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
const MAX_MATCH_PROBES: usize = 128;
const MAX_INPUT_PATHS: usize = 256;
const MAX_INPUT_PHASE_TERMS: usize = 65536;
const MAX_INPUT_CELLS: usize = MAX_FACTOR_PHASE_CELLS;

use super::product_form::Product;

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

fn collapse_phase_unit(
    source: &ExactAggregate,
    reduction: &mut ReductionBudget,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
) -> Option<ExactAggregate> {
    super::phase_unit::collapse(source, &mut reduction.phase_cells, free, algebra)
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
    super::product_cases::prove(
        left,
        right,
        &mut ProductCases {
            reduction,
            free_splits,
            algebra,
            probes,
        },
        depth,
    )
}

struct ProductCases<'a> {
    reduction: &'a mut ReductionBudget,
    free_splits: &'a mut usize,
    algebra: &'a mut witness::ConstantBudget,
    probes: &'a mut usize,
}
impl super::product_cases::Proof for ProductCases<'_> {
    fn matches(
        &mut self,
        left: &Product,
        right: &Product,
        relevant: &mut BTreeSet<KernelVariable>,
    ) -> bool {
        bijection(
            left,
            right,
            self.reduction,
            self.free_splits,
            self.algebra,
            (self.probes, relevant),
        )
    }
    fn free_splits(&mut self) -> &mut usize {
        self.free_splits
    }
    fn charge(&mut self, sum: &ExactAggregate) -> Option<()> {
        charge_cells(sum, &mut self.reduction.phase_cells)
    }
    fn refine(&mut self, sum: ExactAggregate) -> Option<Vec<ExactAggregate>> {
        refine_tensor(sum, self.reduction)
    }
    fn multiply(&mut self, left: ExactAggregate, right: ExactAggregate) -> Option<ExactAggregate> {
        multiply_aggregates(left, right, self.reduction)
    }
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
    super::factor_match::matches(
        left,
        right,
        &mut FactorMatch {
            reduction,
            free_splits,
            algebra,
            probes,
        },
        relevant,
    )
}
struct FactorMatch<'a> {
    reduction: &'a mut ReductionBudget,
    free_splits: &'a mut usize,
    algebra: &'a mut witness::ConstantBudget,
    probes: &'a mut usize,
}
impl super::factor_match::Proof for FactorMatch<'_> {
    fn probes(&mut self) -> &mut usize {
        self.probes
    }
    fn phase_cells(&mut self) -> &mut usize {
        &mut self.reduction.phase_cells
    }
    fn equal(&mut self, l: &ExactAggregate, r: &ExactAggregate) -> bool {
        equal(l, r, self.free_splits, self.algebra)
    }
    fn unit(&mut self, l: &ExactAggregate, r: &ExactAggregate) -> Option<ExactAggregate> {
        matching_unit(
            l,
            r,
            self.reduction,
            self.free_splits,
            self.algebra,
            self.probes,
        )
    }
    fn pair(
        &mut self,
        f: &ExactAggregate,
        rest: &[&ExactAggregate],
    ) -> Option<(usize, usize, ExactAggregate)> {
        matching_pair_unit(
            f,
            rest,
            self.reduction,
            self.free_splits,
            self.algebra,
            self.probes,
        )
    }
    fn multiply(&mut self, l: ExactAggregate, r: ExactAggregate) -> Option<ExactAggregate> {
        multiply_aggregates(l, r, self.reduction)
    }
    fn zero_product(&mut self, factors: Vec<ExactAggregate>) -> bool {
        zero_product(
            factors,
            self.free_splits,
            self.algebra,
            &mut self.reduction.phase_cells,
            0,
        )
    }
}

fn matching_pair_unit(
    factor: &ExactAggregate,
    remaining: &[&ExactAggregate],
    reduction: &mut ReductionBudget,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
    probes: &mut usize,
) -> Option<(usize, usize, ExactAggregate)> {
    super::factor_pair::find(
        factor,
        remaining,
        &mut FactorMatch {
            reduction,
            free_splits: free,
            algebra,
            probes,
        },
    )
}

fn matching_unit(
    left: &ExactAggregate,
    right: &ExactAggregate,
    reduction: &mut ReductionBudget,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
    probes: &mut usize,
) -> Option<ExactAggregate> {
    let products = &mut reduction.products;
    super::factor_relation::matching_unit(
        left,
        right,
        &mut reduction.phase_cells,
        free,
        algebra,
        probes,
        &mut |unit, cells, free, algebra| {
            factorization::multiply(right.clone(), unit.clone(), products, cells, |term| {
                match reduce_working_term(term) {
                    Reduction::Zero => Some(None),
                    Reduction::Exact(exact) => Some(Some(exact)),
                    _ => None,
                }
            })
            .map(|transformed| equal(left, &transformed, free, algebra))
        },
    )
}

fn zero_product(
    factors: Vec<ExactAggregate>,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
    cells: &mut usize,
    depth: usize,
) -> bool {
    super::zero_product::prove(factors, free, algebra, cells, depth, MAX_FREE_SPLIT_DEPTH)
}

use super::phase_unit::charge_cells;

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
    super::product_form::build(
        factors,
        &mut ProductReduction(budget),
        shared_small,
        prefer_rectangles,
    )
}

struct ProductReduction<'a>(&'a mut ReductionBudget);

impl super::product_form::Reduction for ProductReduction<'_> {
    fn exact(&mut self, term: WorkingTerm) -> Option<ExactTerm> {
        match reduce_working_term(term) {
            Reduction::Exact(term) => Some(term),
            _ => None,
        }
    }

    fn sum(&mut self, factor: WorkingTerm, large: bool) -> Option<(ExactAggregate, usize)> {
        if large {
            // Every leaf must finish within the same shared proof budget.
            let sum = small_sum::sum(&factor, self.0)?;
            let atoms = sum.values().map(BTreeMap::len).sum();
            Some((sum, atoms))
        } else {
            let mut sum = ExactAggregate::new();
            let mut atoms = 0;
            accumulate_reduction(reduce_working_term(factor), &mut sum, &mut atoms, self.0, 0)?;
            Some((sum, atoms))
        }
    }

    fn refine(&mut self, sum: ExactAggregate, rectangles: bool) -> Option<Vec<ExactAggregate>> {
        if rectangles {
            let mut source = Some(sum);
            rectangle::factor(&mut source, self.0).or_else(|| refine_tensor(source?, self.0))
        } else {
            refine_tensor(sum, self.0)
        }
    }

    fn finish(&mut self, term: WorkingTerm) -> Option<ExactAggregate> {
        let mut aggregate = ExactAggregate::new();
        let mut atoms = 0;
        accumulate_reduction(
            reduce_working_term(term),
            &mut aggregate,
            &mut atoms,
            self.0,
            0,
        )?;
        Some(aggregate)
    }
}

fn refine_tensor(
    source: ExactAggregate,
    budget: &mut ReductionBudget,
) -> Option<Vec<ExactAggregate>> {
    super::factor_refine::refine(
        source,
        MAX_FACTOR_PHASE_CELLS,
        budget,
        multiply_aggregates,
        |term, result, atoms, budget| {
            accumulate_reduction(reduce_working_term(term), result, atoms, budget, 0)
        },
    )
}
