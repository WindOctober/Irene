use super::super::product_cases::MAX_PRODUCT_SPLIT_DEPTH;
use super::*;
use crate::symbolic::PhaseCoefficient;

const MAX_ORIENTATION_LEFT_TERMS: usize = 512;
fn relative_phase_unit(
    left: &ExactAggregate,
    right: &ExactAggregate,
    budget: &mut ReductionBudget,
    free: &mut usize,
    algebra: &mut witness::ConstantBudget,
) -> Option<ExactAggregate> {
    super::super::factor_relation::relative_phase_unit(
        left,
        right,
        &mut budget.phase_cells,
        free,
        algebra,
    )
}
fn conditional_binomial_unit(
    left: &ExactAggregate,
    right: &ExactAggregate,
    budget: &mut ReductionBudget,
) -> Option<ExactAggregate> {
    super::super::factor_relation::conditional_binomial_unit(left, right, &mut budget.phase_cells)
}
fn orientation_phase(
    left: &KernelPhasePolynomial,
    right: &KernelPhasePolynomial,
    budget: &mut ReductionBudget,
    depth: usize,
) -> Option<KernelPhasePolynomial> {
    super::super::factor_relation::orientation_phase(left, right, &mut budget.phase_cells, depth)
}
fn negative_gated_phase(
    phase: &KernelPhasePolynomial,
    flip: &KernelBooleanPolynomial,
    budget: &mut ReductionBudget,
) -> Option<KernelPhasePolynomial> {
    super::super::factor_relation::negative_gated_phase(phase, flip, &mut budget.phase_cells)
}
fn parity_orientation_phase(
    left: &KernelPhasePolynomial,
    right: &KernelPhasePolynomial,
    budget: &mut ReductionBudget,
) -> Option<KernelPhasePolynomial> {
    super::super::factor_relation::parity_orientation_phase(left, right, &mut budget.phase_cells)
}
fn large_parity_orientation_phase(
    left: &KernelPhasePolynomial,
    right: &KernelPhasePolynomial,
    budget: &mut ReductionBudget,
) -> Option<KernelPhasePolynomial> {
    super::super::factor_relation::large_parity_orientation_phase(
        left,
        right,
        &mut budget.phase_cells,
    )
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
    let right =
        multiply_aggregates(factors[0].clone(), factors[1].clone(), &mut test_budget()).unwrap();
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
            witness::constant_monomial(&at_point, &mut witness::ConstantBudget::default()).unwrap();
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
            &KernelBooleanPolynomial::variable(y.clone()).and(&KernelBooleanPolynomial::variable(
                KernelVariable::InputKet(index),
            )),
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
        let negative = KernelPhasePolynomial::difference(&KernelPhasePolynomial::default(), &right);
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
