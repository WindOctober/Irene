use super::super::KernelBooleanPolynomial;
use super::super::scalar::ratio;
use super::*;
use crate::symbolic::PhaseCoefficient;

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

fn evaluate(p: &Product, input: usize) -> Cyclo {
    p.factors
        .iter()
        .fold(evaluate_sum(&p.common, input), |a, f| {
            multiply(a, evaluate_sum(f, input))
        })
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
    allow_pairs: bool,
    invalid_pair: Option<(usize, usize)>,
    refuse_multiply: bool,
    zero_calls: usize,
}
impl Backend {
    fn new() -> Self {
        Self {
            probes: 128,
            cells: 100000,
            units: vec![],
            allow_pairs: false,
            invalid_pair: None,
            refuse_multiply: false,
            zero_calls: 0,
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
        // Every supplied candidate is checked pointwise by the independent
        // exact oracle; a proposal table is not itself a certificate.
        self.units
            .iter()
            .find(|u| {
                (0..4)
                    .all(|i| evaluate_sum(a, i) == multiply(evaluate_sum(u, i), evaluate_sum(b, i)))
            })
            .cloned()
    }
    fn pair(
        &mut self,
        f: &ExactAggregate,
        rest: &[&ExactAggregate],
    ) -> Option<(usize, usize, ExactAggregate)> {
        if let Some((a, b)) = self.invalid_pair {
            return Some((a, b, unit()));
        }
        if !self.allow_pairs {
            return None;
        }
        for a in 0..rest.len() {
            for b in a + 1..rest.len() {
                self.probes = self.probes.checked_sub(1)?;
                let p = multiply_sums(rest[a], rest[b])?;
                if eq(f, &p) {
                    return Some((a, b, unit()));
                }
                if let Some(u) = self.unit(f, &p) {
                    return Some((a, b, u));
                }
            }
        }
        None
    }
    fn multiply(&mut self, a: ExactAggregate, b: ExactAggregate) -> Option<ExactAggregate> {
        if self.refuse_multiply {
            None
        } else {
            multiply_sums(&a, &b)
        }
    }
    fn zero_product(&mut self, factors: Vec<ExactAggregate>) -> bool {
        self.zero_calls += 1;
        (0..4).all(|i| {
            factors
                .iter()
                .fold(one(), |v, f| multiply(v, evaluate_sum(f, i)))
                == zero()
        })
    }
}
fn check(l: &Product, r: &Product, b: &mut Backend) -> bool {
    let result = matches(l, r, b, &mut BTreeSet::new());
    if result {
        for i in 0..4 {
            assert_eq!(evaluate(l, i), evaluate(r, i));
        }
    }
    result
}

#[test]
fn shuffled_factors_match_but_one_right_factor_cannot_be_used_twice() {
    let a = binomial(KernelVariable::InputKet(0), 1);
    let b = binomial(KernelVariable::InputBra(0), 2);
    let left = Product {
        common: unit(),
        factors: vec![a.clone(), b.clone()],
    };
    let right = Product {
        common: unit(),
        factors: vec![b.clone(), a.clone()],
    };
    assert!(check(&left, &right, &mut Backend::new()));
    let duplicate = Product {
        common: unit(),
        factors: vec![a.clone(), a],
    };
    assert!(!check(&duplicate, &right, &mut Backend::new()));
    let extra = Product {
        common: unit(),
        factors: vec![b.clone(), right.factors[1].clone(), constant(3)],
    };
    assert!(!check(&left, &extra, &mut Backend::new()));
    let missing = Product {
        common: unit(),
        factors: vec![b],
    };
    assert!(!check(&left, &missing, &mut Backend::new()));
}

fn scaled_pair() -> (Product, Product, Backend) {
    let a = binomial(KernelVariable::InputKet(0), 1);
    let b = binomial(KernelVariable::InputBra(0), 2);
    let two = constant(2);
    let turn = sum(vec![], 1, vec![phase(&KernelVariable::InputKet(0), 2)]);
    let left = Product {
        common: constant(3),
        factors: vec![
            multiply_sums(&two, &b).unwrap(),
            multiply_sums(&turn, &a).unwrap(),
        ],
    };
    let right = Product {
        common: multiply_sums(&constant(6), &turn).unwrap(),
        factors: vec![a, b],
    };
    let mut backend = Backend::new();
    backend.units = vec![two, turn];
    (left, right, backend)
}

#[test]
fn scalar_and_phase_units_accumulate_with_the_correct_direction() {
    let (left, right, mut backend) = scaled_pair();
    assert!(check(&left, &right, &mut backend));
    let wrong = Product {
        common: constant(6),
        factors: right.factors.clone(),
    };
    let (_, _, mut backend) = scaled_pair();
    assert!(!check(&left, &wrong, &mut backend));
    let wrong = Product {
        common: constant(3),
        factors: right.factors,
    };
    let (_, _, mut backend) = scaled_pair();
    assert!(!check(&left, &wrong, &mut backend));
}

#[test]
fn common_difference_is_multiplied_by_all_original_factors_not_cancelled() {
    let x = KernelVariable::InputKet(0);
    let f = binomial(x.clone(), 4);
    let left = Product {
        common: sum(vec![], 1, vec![phase(&x, 4)]),
        factors: vec![f.clone()],
    };
    let right = Product {
        common: unit(),
        factors: vec![f.clone()],
    };
    let mut backend = Backend::new();
    assert!(check(&left, &right, &mut backend));
    assert_eq!(backend.zero_calls, 1);
    let wrong = Product {
        common: sum(vec![], 1, vec![phase(&KernelVariable::InputBra(0), 2)]),
        factors: vec![f],
    };
    assert!(!check(&wrong, &right, &mut Backend::new()));
}

#[test]
fn identical_support_is_only_a_search_hint_and_guards_remain_semantic() {
    let x = KernelVariable::InputKet(0);
    let left = Product {
        common: unit(),
        factors: vec![binomial(x.clone(), 1)],
    };
    let right = Product {
        common: unit(),
        factors: vec![binomial(x, 2)],
    };
    let mut relevant = BTreeSet::new();
    assert!(!matches(&left, &right, &mut Backend::new(), &mut relevant));
    let guarded = Product {
        common: sum(
            vec![bit(&KernelVariable::InputBra(0))],
            1,
            vec![KernelPhasePolynomial::default()],
        ),
        factors: left.factors.clone(),
    };
    assert!(!check(&left, &guarded, &mut Backend::new()));
}

#[test]
fn pair_match_consumes_two_distinct_entries_and_preserves_the_last_factor() {
    let a = binomial(KernelVariable::InputKet(0), 1);
    let b = binomial(KernelVariable::InputBra(0), 2);
    let c = binomial(KernelVariable::InputKet(0), 3);
    let left = Product {
        common: unit(),
        factors: vec![multiply_sums(&a, &b).unwrap(), c.clone()],
    };
    let right = Product {
        common: unit(),
        factors: vec![c, b, a],
    };
    let mut backend = Backend::new();
    backend.allow_pairs = true;
    assert!(check(&left, &right, &mut backend));
    for pair in [(0, 0), (1, 0), (0, 3)] {
        let mut invalid = Backend::new();
        invalid.invalid_pair = Some(pair);
        assert!(!matches(&left, &right, &mut invalid, &mut BTreeSet::new()));
    }
}

#[test]
fn zero_probes_failed_multiplication_or_unit_budget_never_certify_eq() {
    for mode in 0..3 {
        let (left, right, mut backend) = scaled_pair();
        match mode {
            0 => backend.probes = 0,
            1 => backend.refuse_multiply = true,
            _ => backend.cells = 0,
        }
        assert!(!check(&left, &right, &mut backend));
    }
}

#[test]
fn collecting_units_matches_sequential_exact_multiplication() {
    let mut scale = integer(1);
    let mut turns = KernelPhasePolynomial::default();
    let mut cells = 100000;
    let mut expected = unit();
    for i in 0..24 {
        let variable = if i % 2 == 0 {
            KernelVariable::InputKet(0)
        } else {
            KernelVariable::InputBra(0)
        };
        let factor = sum(
            vec![],
            if i % 3 == 0 { -2 } else { 3 },
            vec![phase(&variable, 1)],
        );
        collect_unit(&factor, &mut scale, &mut turns, &mut cells).unwrap();
        expected = multiply_sums(&expected, &factor).unwrap();
    }
    let mut actual = ExactAggregate::new();
    accumulate_exact_term(
        ExactTerm {
            constraints: vec![],
            coefficient: KernelScalar::Rational(scale),
            phase: turns,
        },
        &mut actual,
        &mut 0,
    )
    .unwrap();
    assert!(eq(&actual, &expected));
}

#[test]
fn guarded_zero_multi_atom_and_oversized_units_are_refused() {
    let mut rejected = vec![
        ExactAggregate::new(),
        sum(
            vec![bit(&KernelVariable::InputKet(0))],
            1,
            vec![KernelPhasePolynomial::default()],
        ),
        binomial(KernelVariable::InputBra(0), 1),
    ];
    let mut huge = unit();
    *huge
        .values_mut()
        .next()
        .unwrap()
        .values_mut()
        .next()
        .unwrap() = KernelScalar::Rational(BigRational::from_integer(
        num_bigint::BigInt::from(1) << 4096,
    ));
    rejected.push(huge);
    let mut zero_weight = unit();
    *zero_weight
        .values_mut()
        .next()
        .unwrap()
        .values_mut()
        .next()
        .unwrap() = KernelScalar::Rational(integer(0));
    rejected.push(zero_weight);
    for candidate in rejected {
        assert!(
            collect_unit(
                &candidate,
                &mut integer(1),
                &mut KernelPhasePolynomial::default(),
                &mut 100000
            )
            .is_none()
        );
    }
}
