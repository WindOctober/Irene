use super::super::KernelBooleanPolynomial;
use super::super::factor_relation::add_phase;
use super::super::scalar::ratio;
use super::*;
use crate::symbolic::PhaseCoefficient;
use num_rational::BigRational;

fn bit(v: &KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v.clone())
}
fn sum(
    guard: Vec<KernelBooleanPolynomial>,
    weight: i64,
    phases: Vec<KernelPhasePolynomial>,
) -> ExactAggregate {
    let mut out = ExactAggregate::new();
    for phase in phases {
        accumulate_exact_term(
            ExactTerm {
                constraints: guard.clone(),
                coefficient: KernelScalar::Rational(integer(weight)),
                phase,
            },
            &mut out,
            &mut 0,
        )
        .unwrap();
    }
    out
}
fn phase(v: &KernelVariable, eighths: i64) -> KernelPhasePolynomial {
    let mut p = KernelPhasePolynomial::default();
    p.add_boolean(&bit(v), PhaseCoefficient::rational(ratio(eighths, 8)));
    p
}
fn unit() -> ExactAggregate {
    sum(vec![], 1, vec![KernelPhasePolynomial::default()])
}

// Independent exact evaluation in Q(zeta_8), zeta_8^4 = -1.
type Cyclo = [BigRational; 4];
fn zero() -> Cyclo {
    std::array::from_fn(|_| integer(0))
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

fn multiply_sums(a: &ExactAggregate, b: &ExactAggregate) -> Option<ExactAggregate> {
    let mut out = ExactAggregate::new();
    for (ae, av) in a {
        for (be, bv) in b {
            let mut guards = ae.constraints.clone();
            guards.extend(be.constraints.iter().cloned());
            for (ap, ac) in av {
                for (bp, bc) in bv {
                    let mut phase = ap.clone();
                    add_phase(&mut phase, bp)?;
                    accumulate_exact_term(
                        ExactTerm {
                            constraints: guards.clone(),
                            phase,
                            coefficient: ac.clone().multiply(bc.clone()),
                        },
                        &mut out,
                        &mut 0,
                    )?;
                }
            }
        }
    }
    Some(out)
}
fn eq(a: &ExactAggregate, b: &ExactAggregate) -> bool {
    (0..4).all(|i| evaluate_sum(a, i) == evaluate_sum(b, i))
}
fn binomial(v: KernelVariable, eighths: i64) -> ExactAggregate {
    sum(
        vec![],
        1,
        vec![KernelPhasePolynomial::default(), phase(&v, eighths)],
    )
}
fn constant(n: i64) -> ExactAggregate {
    sum(vec![], n, vec![KernelPhasePolynomial::default()])
}

struct Backend {
    probes: usize,
    cells: usize,
    units: Vec<ExactAggregate>,
    products: usize,
    refuse: bool,
}
impl Default for Backend {
    fn default() -> Self {
        Self {
            probes: 128,
            cells: 1_000_000,
            units: vec![],
            products: 0,
            refuse: false,
        }
    }
}
impl Proof for Backend {
    fn probes(&mut self) -> &mut usize {
        &mut self.probes
    }
    fn phase_cells(&mut self) -> &mut usize {
        &mut self.cells
    }
    fn equal(&mut self, a: &ExactAggregate, b: &ExactAggregate) -> bool {
        eq(a, b)
    }
    fn unit(&mut self, a: &ExactAggregate, b: &ExactAggregate) -> Option<ExactAggregate> {
        self.units
            .iter()
            .find(|u| {
                (0..4)
                    .all(|i| evaluate_sum(a, i) == multiply(evaluate_sum(u, i), evaluate_sum(b, i)))
            })
            .cloned()
    }
    fn multiply(&mut self, a: ExactAggregate, b: ExactAggregate) -> Option<ExactAggregate> {
        self.products += 1;
        if self.refuse {
            None
        } else {
            multiply_sums(&a, &b)
        }
    }
    fn pair(
        &mut self,
        _: &ExactAggregate,
        _: &[&ExactAggregate],
    ) -> Option<(usize, usize, ExactAggregate)> {
        panic!("pair search must not recurse")
    }
    fn zero_product(&mut self, _: Vec<ExactAggregate>) -> bool {
        panic!("not a product proof")
    }
}
fn check(
    f: &ExactAggregate,
    rest: &[&ExactAggregate],
    backend: &mut Backend,
) -> Option<(usize, usize, ExactAggregate)> {
    let found = find(f, rest, backend);
    if let Some((a, b, u)) = &found {
        assert!(a < b && *b < rest.len());
        // Validate every returned certificate independently at every fixture input.
        for input in 0..4 {
            assert_eq!(
                evaluate_sum(f, input),
                multiply(
                    evaluate_sum(u, input),
                    multiply(evaluate_sum(rest[*a], input), evaluate_sum(rest[*b], input))
                )
            );
        }
    }
    found
}
#[test]
fn matches_complete_product_after_shuffling() {
    let a = binomial(KernelVariable::InputKet(0), 1);
    let b = binomial(KernelVariable::InputBra(0), 2);
    let f = multiply_sums(&a, &b).unwrap();
    let decoy = constant(17);
    let found = check(&f, &[&decoy, &b, &a], &mut Backend::default()).unwrap();
    assert_eq!((found.0, found.1), (1, 2));
    assert!(eq(&found.2, &unit()));
    let mut wrong = f;
    wrong.values_mut().next().unwrap().pop_last();
    assert!(check(&wrong, &[&a, &b], &mut Backend::default()).is_none());
}
#[test]
fn support_ranking_finds_late_pair_before_probe_limit() {
    let a = binomial(KernelVariable::InputKet(0), 1);
    let b = binomial(KernelVariable::InputBra(0), 1);
    let f = multiply_sums(&a, &b).unwrap();
    let decoys = (2..10).map(constant).collect::<Vec<_>>();
    let mut refs = decoys.iter().collect::<Vec<_>>();
    refs.extend([&a, &b]);
    let mut backend = Backend {
        probes: 1,
        ..Backend::default()
    };
    assert!(check(&f, &refs, &mut backend).is_some());
    assert_eq!(backend.products, 1);
}
#[test]
fn collects_certified_scalar_and_phase_in_correct_direction() {
    let a = binomial(KernelVariable::InputKet(0), 1);
    let b = binomial(KernelVariable::InputBra(0), 2);
    let u = sum(vec![], -3, vec![phase(&KernelVariable::InputKet(0), 1)]);
    let f = multiply_sums(&multiply_sums(&a, &b).unwrap(), &u).unwrap();
    let mut backend = Backend {
        units: vec![u.clone()],
        ..Backend::default()
    };
    let found = check(&f, &[&b, &a], &mut backend).unwrap();
    assert!(eq(&found.2, &u));
}
#[test]
fn selector_and_coefficient_differences_are_not_support_matches() {
    let a = binomial(KernelVariable::InputKet(0), 1);
    let b = binomial(KernelVariable::InputBra(0), 2);
    let f = multiply_sums(&a, &b).unwrap();
    let selector = sum(
        vec![bit(&KernelVariable::InputKet(0))],
        1,
        vec![KernelPhasePolynomial::default()],
    );
    let guarded = multiply_sums(&a, &selector).unwrap();
    assert!(check(&f, &[&guarded, &b], &mut Backend::default()).is_none());
    let wrong_weight = multiply_sums(&b, &constant(2)).unwrap();
    assert!(check(&f, &[&a, &wrong_weight], &mut Backend::default()).is_none());
}
#[test]
fn distinct_positions_required_but_equal_factors_are_allowed() {
    let a = binomial(KernelVariable::InputKet(0), 1);
    let f = multiply_sums(&a, &a).unwrap();
    assert!(check(&f, &[], &mut Backend::default()).is_none());
    assert!(check(&f, &[&a], &mut Backend::default()).is_none());
    assert!(check(&f, &[&a, &a], &mut Backend::default()).is_some());
}
#[test]
fn budgets_and_failed_multiplication_are_inconclusive() {
    let a = constant(2);
    let b = constant(3);
    let f = constant(6);
    for mut backend in [
        Backend {
            probes: 0,
            ..Backend::default()
        },
        Backend {
            cells: 0,
            ..Backend::default()
        },
        Backend {
            refuse: true,
            ..Backend::default()
        },
    ] {
        assert!(check(&f, &[&a, &b], &mut backend).is_none());
    }
    let many = vec![&a; MAX_FACTORS + 1];
    assert!(check(&f, &many, &mut Backend::default()).is_none());
}
#[test]
fn unmatched_pairs_do_not_expand_beyond_sixteen_proposals() {
    let factors = (2..9).map(constant).collect::<Vec<_>>();
    let refs = factors.iter().collect::<Vec<_>>();
    let mut backend = Backend::default();
    assert!(check(&constant(101), &refs, &mut backend).is_none());
    assert_eq!(backend.products, 16);
    assert_eq!(backend.probes, 128 - 16);
}
#[test]
fn zero_product_is_compared_without_dividing_by_either_factor() {
    let a = binomial(KernelVariable::InputKet(0), 4);
    let b = sum(
        vec![bit(&KernelVariable::InputKet(0)).xor(&KernelBooleanPolynomial::one())],
        1,
        vec![KernelPhasePolynomial::default()],
    );
    let f = ExactAggregate::new();
    assert!(check(&f, &[&a, &b], &mut Backend::default()).is_some());
}
