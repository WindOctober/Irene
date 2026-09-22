use super::super::collection::{ExactEntry, ExactTerm, accumulate_exact_term};
use super::super::scalar::{integer, ratio};
use super::super::{KernelBooleanPolynomial, KernelPhasePolynomial, KernelScalar};
use super::*;
use crate::symbolic::PhaseCoefficient;

fn var(v: KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v)
}
fn collect(terms: impl IntoIterator<Item = ExactTerm>) -> ExactAggregate {
    let mut sum = ExactAggregate::new();
    for t in terms {
        accumulate_exact_term(t, &mut sum, &mut 0).unwrap();
    }
    sum.retain(|_, coefficients| !coefficients.is_empty());
    sum
}
fn constant(n: i64) -> ExactAggregate {
    collect([ExactTerm {
        constraints: vec![],
        coefficient: KernelScalar::Rational(integer(n)),
        phase: KernelPhasePolynomial::default(),
    }])
}
fn run(factors: Vec<ExactAggregate>, mut free: usize, depth_limit: usize) -> bool {
    prove(
        factors,
        &mut free,
        &mut witness::ConstantBudget::default(),
        &mut 250_000,
        0,
        depth_limit,
    )
}
fn table(mask: u8) -> ExactAggregate {
    let leaf = |i: u32| Box::new(KernelScalar::Rational(integer(((mask >> i) & 1u8) as i64)));
    let row = |x| {
        Box::new(KernelScalar::Select {
            condition: var(KernelVariable::InputBra(0)),
            when_true: leaf(x + 2),
            when_false: leaf(x),
        })
    };
    collect([ExactTerm {
        constraints: vec![],
        phase: KernelPhasePolynomial::default(),
        coefficient: KernelScalar::Select {
            condition: var(KernelVariable::InputKet(0)),
            when_true: row(1),
            when_false: row(0),
        },
    }])
}
fn phased(turns: i64, denominator: i64, p: &KernelBooleanPolynomial, weight: i64) -> ExactTerm {
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(p, PhaseCoefficient::rational(ratio(turns, denominator)));
    ExactTerm {
        constraints: vec![],
        coefficient: KernelScalar::Rational(integer(weight)),
        phase,
    }
}

#[test]
fn all_two_bit_boolean_factor_pairs_agree_with_independent_truth_tables() {
    // A product is zero at all four assignments iff the truth masks do not
    // overlap. Neither factor individually needs to be identically zero.
    for left in 0u8..16 {
        for right in 0u8..16 {
            assert_eq!(
                run(vec![table(left), table(right)], 32, 4),
                left & right == 0,
                "left={left:04b} right={right:04b}"
            );
        }
    }
}

#[test]
fn phase_interference_can_annihilate_a_nonzero_coefficient_difference() {
    for variable in [
        KernelVariable::InputKet(0),
        KernelVariable::InputBra(0),
        KernelVariable::QuantumOutputKet(0),
        KernelVariable::QuantumOutputBra(0),
        KernelVariable::ClassicalOutput(0),
    ] {
        let x = var(variable);
        let difference = collect([phased(1, 2, &x, 1), phased(0, 1, &x, -1)]);
        let factor = collect([phased(0, 1, &x, 1), phased(1, 2, &x, 1)]);
        assert!(!run(vec![difference.clone()], 4, 4));
        assert!(!run(vec![factor.clone()], 4, 4));
        assert!(run(vec![difference.clone(), factor], 1, 1));
        // x=0 still agrees, but x=1 now gives -2*(1+i), not zero.
        let wrong = collect([phased(0, 1, &x, 1), phased(1, 4, &x, 1)]);
        assert!(!run(vec![difference, wrong], 4, 4));
    }
}

#[test]
fn guard_zero_sets_are_retained_instead_of_cancelled() {
    let x = var(KernelVariable::InputKet(0));
    let guarded = |row| {
        collect([ExactTerm {
            constraints: vec![row],
            coefficient: KernelScalar::Rational(integer(3)),
            phase: KernelPhasePolynomial::default(),
        }])
    };
    assert!(run(vec![guarded(x.clone()), guarded(x.complement())], 1, 1));
    assert!(!run(vec![guarded(x.clone()), guarded(x)], 4, 4));
    assert!(run(vec![guarded(KernelBooleanPolynomial::one())], 1, 1));
}

#[test]
fn all_branches_share_limits_and_a_proved_prefix_is_not_a_certificate() {
    // Each factor is zero at exactly one of the four assignments.
    let factors = || [14, 13, 11, 7].into_iter().map(table).collect();
    assert!(!run(factors(), 2, 4));
    assert!(!run(factors(), 3, 1));
    assert!(run(factors(), 3, 2));
    let source = factors();
    assert!(!prove(
        source.clone(),
        &mut 32,
        &mut witness::ConstantBudget::default(),
        &mut 0,
        0,
        4
    ));
    assert!(run(source, 3, 2));
}

#[test]
fn empty_product_pure_phases_and_unsupported_constants_are_not_zero() {
    assert!(!run(vec![], 4, 4)); // Empty product is one, not zero.
    assert!(!run(vec![constant(1), constant(-1)], 4, 4));
    assert!(run(vec![constant(0), constant(3)], 0, 0));
    let x = var(KernelVariable::InputKet(0));
    assert!(!run(vec![collect([phased(1, 4, &x, 1)])], 4, 4));
    assert!(!run(
        vec![collect([phased(1, 3, &KernelBooleanPolynomial::one(), 1)])],
        4,
        4
    ));
}

#[test]
fn bound_paths_are_not_treated_as_free_cases_and_graph_refusals_are_conservative() {
    for variable in [
        KernelVariable::PathKet { term: 0, path: 0 },
        KernelVariable::PathBra { term: 0, path: 0 },
    ] {
        let y = var(variable);
        let a = collect([phased(0, 1, &y, 1), phased(1, 2, &y, 1)]);
        let b = collect([phased(0, 1, &y, 1), phased(1, 2, &y, -1)]);
        assert!(!run(vec![a, b], 32, 4));
    }
    let v = |i| var(KernelVariable::InputKet(i)).as_graph();
    let graph = KernelBooleanPolynomial::from_graph(v(0).and(&v(1).xor(&v(2))));
    let guarded = BTreeMap::from([(
        ExactEntry {
            constraints: vec![graph],
        },
        BTreeMap::from([(
            KernelPhasePolynomial::default(),
            KernelScalar::Rational(integer(1)),
        )]),
    )]);
    assert!(!run(vec![guarded], 32, 4));
}

#[test]
fn dominant_difference_coordinate_exposes_complementary_zero_factors() {
    let y = var(KernelVariable::QuantumOutputBra(99));
    let mut gated = KernelPhasePolynomial::default();
    for i in 0..20 {
        gated.add_boolean(
            &y.and(&var(KernelVariable::InputKet(i))),
            PhaseCoefficient::rational(ratio(1, 2)),
        );
    }
    let difference = collect([
        phased(0, 1, &y, 1),
        ExactTerm {
            constraints: vec![],
            coefficient: KernelScalar::Rational(integer(-1)),
            phase: gated,
        },
    ]);
    let factor = collect([phased(0, 1, &y, 1), phased(1, 2, &y, 1)]);
    // For y=0 the difference vanishes; for y=1 the other factor vanishes.
    // Earlier independent inputs need not be enumerated.
    assert!(run(vec![difference.clone(), factor], 1, 1));
    let wrong = collect([phased(0, 1, &y, 1), phased(1, 4, &y, 1)]);
    assert!(!run(vec![difference, wrong], 4095, 12));
}
