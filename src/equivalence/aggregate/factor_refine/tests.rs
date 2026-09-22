use super::super::scalar::{normalize_scalar, ratio};
use super::super::{ConstraintNormalization, normalize_constraint_span};
use super::*;
use crate::symbolic::PhaseCoefficient;
use num_rational::BigRational;

type Complex = (BigRational, BigRational);
fn complex_mul(a: Complex, b: Complex) -> Complex {
    (&a.0 * &b.0 - &a.1 * &b.1, a.0 * b.1 + a.1 * b.0)
}
fn bit(v: KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v)
}
fn phase(p: KernelBooleanPolynomial) -> KernelPhasePolynomial {
    let mut result = KernelPhasePolynomial::default();
    result.add_boolean(&p, PhaseCoefficient::rational(ratio(1, 4)));
    result
}
fn plus(a: &KernelPhasePolynomial, b: &KernelPhasePolynomial) -> KernelPhasePolynomial {
    let mut result = a.clone();
    super::super::factor_relation::add_phase(&mut result, b).unwrap();
    result
}
fn collect(terms: impl IntoIterator<Item = ExactTerm>) -> ExactAggregate {
    let mut result = ExactAggregate::new();
    for t in terms {
        accumulate_exact_term(t, &mut result, &mut 0).unwrap();
    }
    result
}
// Construct the expanded source directly rather than using the product prover.
fn rectangle(
    p: &KernelPhasePolynomial,
    q: &KernelPhasePolynomial,
    weights: [BigRational; 4],
    guard: &[KernelBooleanPolynomial],
    common: &KernelPhasePolynomial,
) -> ExactAggregate {
    let [a, b, c, d] = weights;
    collect(
        [
            (&a * &c, KernelPhasePolynomial::default()),
            (&b * &c, p.clone()),
            (&a * &d, q.clone()),
            (&b * &d, plus(p, q)),
        ]
        .into_iter()
        .map(|(weight, p)| ExactTerm {
            constraints: guard.to_vec(),
            coefficient: KernelScalar::Rational(weight),
            phase: plus(&p, common),
        }),
    )
}
fn reduce(mut t: WorkingTerm) -> Option<Option<ExactTerm>> {
    assert!(t.paths.is_empty());
    match normalize_constraint_span(&mut t.constraints) {
        ConstraintNormalization::Contradiction => Some(None),
        ConstraintNormalization::BudgetExceeded => None,
        ConstraintNormalization::Normalized => Some(Some(ExactTerm {
            constraints: t.constraints,
            coefficient: normalize_scalar(t.coefficient),
            phase: t.phase,
        })),
    }
}
fn multiply(l: ExactAggregate, r: ExactAggregate) -> Option<ExactAggregate> {
    super::super::factorization::multiply(l, r, &mut 100_000, &mut 250_000, reduce)
}
fn append(t: WorkingTerm, into: &mut ExactAggregate, atoms: &mut usize, _: &mut ()) -> Option<()> {
    if let Some(t) = reduce(t)? {
        accumulate_exact_term(t, into, atoms)?;
    }
    Some(())
}
fn refined(source: ExactAggregate) -> Option<Vec<ExactAggregate>> {
    refine(source, 250_000, &mut (), |l, r, _| multiply(l, r), append)
}
// Independent Q(i) interpretation for every assignment, including failed guards.
fn boolean(p: &KernelBooleanPolynomial, inputs: &BTreeMap<KernelVariable, bool>) -> bool {
    p.as_graph()
        .evaluate::<()>(|v| Ok(inputs[&KernelVariable::from_graph_variable(v)]))
        .unwrap()
}
fn value(sum: &ExactAggregate, inputs: &BTreeMap<KernelVariable, bool>) -> Complex {
    let mut value = (integer(0), integer(0));
    for (entry, coefficients) in sum {
        if entry.constraints.iter().any(|p| boolean(p, inputs)) {
            continue;
        }
        for (p, a) in coefficients {
            let KernelScalar::Rational(a) = a else {
                panic!("non-rational test scalar")
            };
            let mut turns = integer(0);
            for (condition, coefficient) in p.selectors() {
                if boolean(&condition, inputs) {
                    turns += coefficient.as_rational().unwrap();
                }
            }
            let quarters = turns * integer(4);
            assert!(quarters.is_integer());
            match i64::try_from(quarters.to_integer()).unwrap().rem_euclid(4) {
                0 => value.0 += a,
                1 => value.1 += a,
                2 => value.0 -= a,
                3 => value.1 -= a,
                _ => unreachable!(),
            }
        }
    }
    value
}
fn check_all(source: &ExactAggregate, factors: &[ExactAggregate], vars: &[KernelVariable]) {
    for mask in 0..(1usize << vars.len()) {
        let inputs = vars
            .iter()
            .enumerate()
            .map(|(i, v)| (v.clone(), mask & (1 << i) != 0))
            .collect();
        let product = factors.iter().fold((integer(1), integer(0)), |v, f| {
            complex_mul(v, value(f, &inputs))
        });
        assert_eq!(value(source, &inputs), product, "assignment={mask}");
    }
}
fn simple() -> ExactAggregate {
    rectangle(
        &phase(bit(KernelVariable::InputKet(0))),
        &phase(bit(KernelVariable::InputBra(0))),
        [integer(2), integer(3), integer(5), integer(7)],
        &[],
        &KernelPhasePolynomial::default(),
    )
}

#[test]
fn tensor_reconstructs_rational_scales_and_signs_pointwise() {
    for a in [-3, -1, 1, 2] {
        for b in [-2, 1, 3] {
            let source = rectangle(
                &phase(bit(KernelVariable::InputKet(0))),
                &phase(bit(KernelVariable::InputBra(0))),
                [ratio(a, 3), ratio(b, 2), integer(5), integer(-7)],
                &[],
                &KernelPhasePolynomial::default(),
            );
            let pair = tensor(&source, 250_000, multiply).unwrap();
            check_all(
                &source,
                &pair,
                &[KernelVariable::InputKet(0), KernelVariable::InputBra(0)],
            );
            assert_eq!(multiply(pair[0].clone(), pair[1].clone()).unwrap(), source);
        }
    }
}

#[test]
fn tensor_rejects_missing_cell_and_wrong_relative_coefficient() {
    let source = simple();
    let mut missing = source.clone();
    missing.values_mut().next().unwrap().pop_first();
    assert!(tensor(&missing, 250_000, multiply).is_none());
    let mut wrong = source;
    *wrong
        .values_mut()
        .next()
        .unwrap()
        .last_entry()
        .unwrap()
        .get_mut() = KernelScalar::Rational(integer(100));
    assert!(tensor(&wrong, 250_000, multiply).is_none());
}

#[test]
fn shared_guard_parameters_and_nonconstant_pivot_are_preserved() {
    let parameter = bit(KernelVariable::QuantumOutputBra(1));
    let p = phase(bit(KernelVariable::InputKet(0)).and(&parameter));
    let q = phase(bit(KernelVariable::InputBra(0)).and(&parameter));
    let guard = bit(KernelVariable::InputKet(2)).xor(&parameter);
    let source = rectangle(
        &p,
        &q,
        [integer(2), integer(-3), integer(5), integer(7)],
        &[guard.clone()],
        &phase(parameter),
    );
    let factors = refined(source.clone()).unwrap();
    assert_eq!(factors.len(), 2);
    check_all(
        &source,
        &factors,
        &[
            KernelVariable::InputKet(0),
            KernelVariable::InputBra(0),
            KernelVariable::InputKet(2),
            KernelVariable::QuantumOutputBra(1),
        ],
    );
    for factor in &factors {
        assert!(
            factor
                .keys()
                .all(|entry| entry.constraints.contains(&guard))
        );
    }
}

#[test]
fn mixed_private_phases_use_rectangular_reconstruction() {
    let p = phase(bit(KernelVariable::InputKet(0)).and(&bit(KernelVariable::InputBra(0))));
    let q = phase(bit(KernelVariable::InputKet(1)));
    let guard = bit(KernelVariable::ClassicalOutput(0));
    let source = rectangle(
        &p,
        &q,
        [integer(2), integer(3), integer(5), integer(7)],
        &[guard.clone()],
        &KernelPhasePolynomial::default(),
    );
    assert!(tensor(&source, 250_000, multiply).is_none());
    let pair = binomials(&source, multiply).unwrap();
    check_all(
        &source,
        &pair,
        &[
            KernelVariable::InputKet(0),
            KernelVariable::InputBra(0),
            KernelVariable::InputKet(1),
            KernelVariable::ClassicalOutput(0),
        ],
    );
    let factors = refined(source.clone()).unwrap();
    assert_eq!(factors.len(), 2);
    assert_eq!(
        multiply(factors[0].clone(), factors[1].clone()).unwrap(),
        source
    );
}

#[test]
fn rectangle_rejects_perturbed_fourth_corner_and_incomplete_input() {
    let mut source = simple();
    *source
        .values_mut()
        .next()
        .unwrap()
        .last_entry()
        .unwrap()
        .get_mut() = KernelScalar::Rational(integer(101));
    assert!(binomials(&source, multiply).is_none());
    assert_eq!(refined(source.clone()).unwrap(), vec![source.clone()]);
    source.values_mut().next().unwrap().pop_first();
    assert!(binomials(&source, multiply).is_none());
    assert_eq!(refined(source.clone()).unwrap(), vec![source]);
}

#[test]
fn common_guard_is_restored_on_both_refined_factors() {
    let guard = bit(KernelVariable::ClassicalOutput(0));
    let source = rectangle(
        &phase(bit(KernelVariable::InputKet(0))),
        &phase(bit(KernelVariable::InputBra(0))),
        [integer(1), integer(2), integer(3), integer(5)],
        &[guard.clone()],
        &KernelPhasePolynomial::default(),
    );
    let factors = refined(source.clone()).unwrap();
    assert_eq!(factors.len(), 2);
    check_all(
        &source,
        &factors,
        &[
            KernelVariable::InputKet(0),
            KernelVariable::InputBra(0),
            KernelVariable::ClassicalOutput(0),
        ],
    );
    let inputs = BTreeMap::from([
        (KernelVariable::InputKet(0), false),
        (KernelVariable::InputBra(0), false),
        (KernelVariable::ClassicalOutput(0), true),
    ]);
    for f in &factors {
        assert_eq!(value(f, &inputs), (integer(0), integer(0)));
    }
}

#[test]
fn budgets_and_failed_replay_never_supply_partial_factors() {
    let source = simple();
    assert!(tensor(&source, 0, multiply).is_none());
    assert!(tensor(&source, 250_000, |_, _| None).is_none());
    assert!(binomials(&source, |_, _| None).is_none());
    assert_eq!(
        refine(source.clone(), 250_000, &mut (), |_, _, _| None, append).unwrap(),
        vec![source.clone()]
    );
    let mut calls = 0;
    assert!(
        refine(
            source,
            250_000,
            &mut (),
            |l, r, _| multiply(l, r),
            |t, result, atoms, c| {
                calls += 1;
                if calls == 2 {
                    None
                } else {
                    append(t, result, atoms, c)
                }
            }
        )
        .is_none()
    );
}

#[test]
fn multiple_selectors_and_non_algebraic_phases_are_not_tensor_candidates() {
    let mut source = simple();
    source.insert(
        ExactEntry {
            constraints: vec![bit(KernelVariable::ClassicalOutput(0))],
        },
        source.values().next().unwrap().clone(),
    );
    assert!(tensor(&source, 250_000, multiply).is_none());
    assert!(binomials(&source, multiply).is_none());
    assert_eq!(refined(source.clone()).unwrap(), vec![source]);
    let a = bit(KernelVariable::InputKet(0)).as_graph();
    let b = bit(KernelVariable::InputKet(1)).as_graph();
    let c = bit(KernelVariable::InputKet(2)).as_graph();
    let graph = KernelBooleanPolynomial::from_graph(a.and(&b.xor(&c)));
    let p = phase(graph);
    assert!(!p.is_algebraic());
    let source = collect([ExactTerm {
        constraints: vec![],
        coefficient: KernelScalar::Rational(integer(1)),
        phase: p,
    }]);
    assert!(tensor(&source, 250_000, multiply).is_none());
}
