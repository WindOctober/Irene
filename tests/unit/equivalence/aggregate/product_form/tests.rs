use super::super::scalar::ratio;
use super::super::{KernelBooleanPolynomial, KernelVariable};
use super::*;
use crate::symbolic::PhaseCoefficient;
use num_rational::BigRational;

fn bit(v: &KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v.clone())
}
fn term(weight: i64, eighths: i64) -> WorkingTerm {
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(
        &KernelBooleanPolynomial::one(),
        PhaseCoefficient::rational(ratio(eighths, 8)),
    );
    WorkingTerm {
        paths: BTreeSet::new(),
        constraints: Vec::new(),
        coefficient: KernelScalar::Rational(integer(weight)),
        phase,
    }
}
fn summand(weight: i64) -> WorkingTerm {
    let path = KernelVariable::PathKet { term: 0, path: 0 };
    let mut t = term(weight, 0);
    t.paths.insert(path.clone());
    t.phase
        .add_boolean(&bit(&path), PhaseCoefficient::rational(ratio(1, 8)));
    t
}

// A complete finite sum backend, independent of the production scheduler.
// One shared counter injects refusal at every boundary, including finish.
struct Literal {
    remaining: usize,
    large: Vec<bool>,
    rectangles: Vec<bool>,
}
impl Literal {
    fn new(remaining: usize) -> Self {
        Self {
            remaining,
            large: vec![],
            rectangles: vec![],
        }
    }
    fn step(&mut self) -> Option<()> {
        self.remaining = self.remaining.checked_sub(1)?;
        Some(())
    }
}
fn exact(t: WorkingTerm) -> Option<ExactTerm> {
    if !t.paths.is_empty() {
        return None;
    }
    Some(ExactTerm {
        constraints: t.constraints.into_iter().filter(|g| !g.is_zero()).collect(),
        coefficient: t.coefficient,
        phase: t.phase,
    })
}
fn literal_sum(t: WorkingTerm) -> Option<(ExactAggregate, usize)> {
    if t.paths.len() > 8 {
        return None;
    }
    let mut sum = ExactAggregate::new();
    let mut atoms = 0;
    for bits in 0..1usize << t.paths.len() {
        let mut leaf = t.clone();
        for (i, path) in t.paths.iter().enumerate() {
            let value = if bits & (1 << i) == 0 {
                KernelBooleanPolynomial::zero()
            } else {
                KernelBooleanPolynomial::one()
            };
            leaf.substitute(path, &value);
        }
        leaf.paths.clear();
        accumulate_exact_term(exact(leaf)?, &mut sum, &mut atoms)?;
    }
    Some((sum, atoms))
}
impl Reduction for Literal {
    fn exact(&mut self, t: WorkingTerm) -> Option<ExactTerm> {
        self.step()?;
        exact(t)
    }
    fn sum(&mut self, t: WorkingTerm, shared_small: bool) -> Option<(ExactAggregate, usize)> {
        self.step()?;
        self.large.push(shared_small);
        literal_sum(t)
    }
    fn refine(&mut self, sum: ExactAggregate, rectangles: bool) -> Option<Vec<ExactAggregate>> {
        self.step()?;
        self.rectangles.push(rectangles);
        Some(vec![sum])
    }
    fn finish(&mut self, t: WorkingTerm) -> Option<ExactAggregate> {
        self.step()?;
        Some(literal_sum(t)?.0)
    }
}

// Independent exact evaluation in Q(zeta_8), zeta_8^4 = -1.
type Cyclo = [BigRational; 4];
fn zero() -> Cyclo {
    std::array::from_fn(|_| integer(0))
}
fn one() -> Cyclo {
    [integer(1), integer(0), integer(0), integer(0)]
}
fn multiply(a: Cyclo, b: Cyclo) -> Cyclo {
    let mut out = zero();
    for i in 0..4 {
        for j in 0..4 {
            out[(i + j) % 4] += &a[i] * &b[j] * integer(if i + j >= 4 { -1 } else { 1 });
        }
    }
    out
}
type Point = BTreeMap<KernelVariable, bool>;
fn boolean(p: &KernelBooleanPolynomial, point: &Point) -> bool {
    p.terms()
        .fold(false, |a, m| a ^ m.variables().all(|v| point[v]))
}
fn scalar(s: &KernelScalar, p: &Point) -> BigRational {
    match s {
        KernelScalar::Rational(r) => r.clone(),
        KernelScalar::Mul(a, b) => scalar(a, p) * scalar(b, p),
        KernelScalar::Add(a, b) => scalar(a, p) + scalar(b, p),
        KernelScalar::Neg(a) => -scalar(a, p),
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => scalar(
            if boolean(condition, p) {
                when_true
            } else {
                when_false
            },
            p,
        ),
        _ => panic!("unsupported test scalar"),
    }
}
fn atom(
    guards: &[KernelBooleanPolynomial],
    phase: &KernelPhasePolynomial,
    weight: &KernelScalar,
    p: &Point,
) -> Cyclo {
    let mut out = zero();
    if guards.iter().any(|g| boolean(g, p)) {
        return out;
    }
    let turns: BigRational = phase
        .terms()
        .filter(|(m, _)| m.variables().all(|v| p[v]))
        .map(|(_, c)| c.as_rational().unwrap())
        .sum();
    let scaled = turns * integer(8);
    assert!(scaled.is_integer());
    let exponent: i64 = scaled.to_integer().try_into().unwrap();
    let exponent = exponent.rem_euclid(8) as usize;
    out[exponent % 4] = scalar(weight, p) * integer(if exponent >= 4 { -1 } else { 1 });
    out
}
fn free(input: usize) -> Point {
    Point::from([
        (KernelVariable::InputKet(0), input & 1 != 0),
        (KernelVariable::InputBra(0), input & 2 != 0),
    ])
}
fn evaluate_term(t: &WorkingTerm, input: usize) -> Cyclo {
    let mut out = zero();
    for bits in 0..1usize << t.paths.len() {
        let mut p = free(input);
        p.extend(
            t.paths
                .iter()
                .enumerate()
                .map(|(i, v)| (v.clone(), bits & (1 << i) != 0)),
        );
        let value = atom(&t.constraints, &t.phase, &t.coefficient, &p);
        for i in 0..4 {
            out[i] += &value[i];
        }
    }
    out
}
fn evaluate_sum(sum: &ExactAggregate, input: usize) -> Cyclo {
    let p = free(input);
    let mut out = zero();
    for (entry, coefficients) in sum {
        for (phase, weight) in coefficients {
            let value = atom(&entry.constraints, phase, weight, &p);
            for i in 0..4 {
                out[i] += &value[i];
            }
        }
    }
    out
}
fn assert_product(source: &[WorkingTerm], result: &Product) {
    for input in 0..4 {
        let before = source
            .iter()
            .fold(one(), |v, t| multiply(v, evaluate_term(t, input)));
        let after = result
            .factors
            .iter()
            .fold(evaluate_sum(&result.common, input), |v, f| {
                multiply(v, evaluate_sum(f, input))
            });
        assert_eq!(before, after, "input={input}");
    }
}

#[test]
fn rational_scales_and_phases_are_accumulated_without_expanding_the_product() {
    for a in [-3, -1, 1, 2] {
        for b in [-2, 1, 3] {
            for p in [0, 1, 3, 5] {
                let source = vec![term(a, p), summand(b), term(3, 2)];
                let result = build(source.clone(), &mut Literal::new(100), false, false).unwrap();
                assert_product(&source, &result);
            }
        }
    }
}

#[test]
fn absorbed_one_atom_keeps_its_own_stronger_guard() {
    let mut common = term(2, 1);
    common.constraints.push(bit(&KernelVariable::InputKet(0)));
    let mut guarded = term(-3, 2);
    guarded.constraints.push(bit(&KernelVariable::InputBra(0)));
    let source = vec![common, summand(1), guarded];
    let result = build(source.clone(), &mut Literal::new(100), false, false).unwrap();
    assert_product(&source, &result);
    assert_eq!(evaluate_sum(&result.common, 2), zero());
    assert_ne!(evaluate_sum(&result.common, 0), zero());
}

#[test]
fn unit_factor_can_be_removed_only_with_common_selector_retained() {
    let mut common = term(1, 0);
    common.constraints.push(bit(&KernelVariable::InputKet(0)));
    let source = vec![common, term(1, 0), term(1, 0)];
    let result = build(source.clone(), &mut Literal::new(100), false, false).unwrap();
    assert_product(&source, &result);
    assert_eq!(evaluate_sum(&result.common, 1), zero());
    assert_eq!(evaluate_sum(&result.common, 0), one());
}

#[test]
fn every_refusal_boundary_discards_the_entire_product_including_finalization() {
    let source = vec![term(2, 1), summand(-3), term(3, 2)];
    let mut full = Literal::new(100);
    let result = build(source.clone(), &mut full, false, false).unwrap();
    assert_product(&source, &result);
    let steps = 100 - full.remaining;
    for allowed in 0..steps {
        assert!(build(source.clone(), &mut Literal::new(allowed), false, false).is_none());
    }
    assert!(build(source, &mut Literal::new(steps), false, false).is_some());
}

#[test]
fn empty_unfinished_and_oversized_factors_do_not_produce_partial_products() {
    assert!(build(vec![], &mut Literal::new(100), false, false).is_none());
    assert!(build(vec![summand(1)], &mut Literal::new(100), false, false).is_none());
    let too_many = (0..130).map(|_| term(1, 0)).collect();
    assert!(build(too_many, &mut Literal::new(1000), false, false).is_none());
    let mut late = summand(1);
    late.paths
        .extend((0..9).map(|path| KernelVariable::PathKet { term: 1, path }));
    assert!(
        build(
            vec![term(1, 0), term(2, 1), late],
            &mut Literal::new(100),
            false,
            false
        )
        .is_none()
    );
    // Empty/zero aggregates cannot supply the nonzero normalization pivot.
    assert!(
        build(
            vec![term(1, 0), term(0, 0)],
            &mut Literal::new(100),
            false,
            false
        )
        .is_none()
    );
}

#[test]
fn representation_preferences_do_not_change_the_product_or_bypass_proof_work() {
    for shared in [false, true] {
        for rectangles in [false, true] {
            let source = vec![term(-2, 1), summand(3), term(1, 3)];
            let mut backend = Literal::new(100);
            let result = build(source.clone(), &mut backend, shared, rectangles).unwrap();
            assert_product(&source, &result);
            assert_eq!(backend.large, vec![false, false]);
            assert_eq!(backend.rectangles, vec![rectangles, rectangles]);
        }
    }
}

#[test]
fn a_common_weight_that_vanishes_at_some_inputs_is_never_cancelled() {
    let mut common = term(1, 1);
    common.coefficient = KernelScalar::Select {
        condition: bit(&KernelVariable::InputBra(0)),
        when_true: Box::new(KernelScalar::Rational(integer(0))),
        when_false: Box::new(KernelScalar::Rational(integer(-2))),
    };
    let source = vec![common, summand(3), term(-1, 2)];
    let result = build(source.clone(), &mut Literal::new(100), false, false).unwrap();
    assert_product(&source, &result);
    assert_eq!(evaluate_sum(&result.common, 2), zero());
}
