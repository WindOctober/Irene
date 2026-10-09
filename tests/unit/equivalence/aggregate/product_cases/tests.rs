use super::super::factor_relation::add_phase;
use super::super::scalar::{integer, ratio};
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
fn fixture() -> Product {
    Product {
        common: unit(),
        factors: vec![sum(vec![], 1, vec![phase(&KernelVariable::InputKet(0), 1)])],
    }
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

fn evaluate(p: &Product, input: usize) -> Cyclo {
    p.factors
        .iter()
        .fold(evaluate_sum(&p.common, input), |a, f| {
            multiply(a, evaluate_sum(f, input))
        })
}

/// Only the root deliberately declines matching, to exercise case analysis.
/// Later matching uses an independent exhaustive exact evaluator. The same
/// arithmetic counter is carried through both sides and both truth values.
struct Backend {
    splits: usize,
    steps: usize,
    calls: usize,
    refuse_true: bool,
}
impl Backend {
    fn new(steps: usize) -> Self {
        Self {
            splits: 8,
            steps,
            calls: 0,
            refuse_true: false,
        }
    }
    fn step(&mut self) -> Option<()> {
        self.steps = self.steps.checked_sub(1)?;
        Some(())
    }
}
impl Proof for Backend {
    fn matches(
        &mut self,
        l: &Product,
        r: &Product,
        relevant: &mut BTreeSet<KernelVariable>,
    ) -> bool {
        self.calls += 1;
        relevant.insert(KernelVariable::InputKet(0));
        self.calls != 1
            && !(self.refuse_true && self.calls == 3)
            && (0..4).all(|i| evaluate(l, i) == evaluate(r, i))
    }
    fn free_splits(&mut self) -> &mut usize {
        &mut self.splits
    }
    fn charge(&mut self, _: &ExactAggregate) -> Option<()> {
        self.step()
    }
    fn refine(&mut self, sum: ExactAggregate) -> Option<Vec<ExactAggregate>> {
        self.step()?;
        Some(vec![sum])
    }
    fn multiply(&mut self, a: ExactAggregate, b: ExactAggregate) -> Option<ExactAggregate> {
        self.step()?;
        let mut out = ExactAggregate::new();
        for (ae, av) in a {
            for (be, bv) in &b {
                let mut guards = ae.constraints.clone();
                guards.extend(be.constraints.iter().cloned());
                for (ap, ac) in &av {
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
}

#[test]
fn both_truth_values_must_be_proved_even_after_the_false_branch_succeeds() {
    let left = fixture();
    let mut backend = Backend::new(100);
    assert!(prove(left.clone(), left.clone(), &mut backend, 0));
    assert_eq!(backend.calls, 3);
    assert_eq!(backend.splits, 7);
    let mut other = left.clone();
    other.factors = vec![sum(vec![], 1, vec![phase(&KernelVariable::InputKet(0), 2)])];
    assert!(!prove(left.clone(), other, &mut Backend::new(100), 0));
    let mut unknown = Backend::new(100);
    unknown.refuse_true = true;
    assert!(!prove(left.clone(), left, &mut unknown, 0));
}

#[test]
fn equal_sums_over_inputs_are_not_pointwise_equality() {
    let left = Product {
        common: unit(),
        factors: vec![sum(vec![], 1, vec![phase(&KernelVariable::InputKet(0), 4)])],
    };
    let right = Product {
        common: sum(vec![], -1, vec![KernelPhasePolynomial::default()]),
        factors: left.factors.clone(),
    };
    for input in 0..2 {
        assert_ne!(evaluate(&left, input), evaluate(&right, input));
    }
    // Both expressions sum to zero over x, but equality is required at EACH x.
    for p in [&left, &right] {
        let a = evaluate(p, 0);
        let b = evaluate(p, 1);
        assert_eq!(std::array::from_fn::<_, 4, _>(|i| &a[i] + &b[i]), zero());
    }
    assert!(!prove(left, right, &mut Backend::new(100), 0));
}

#[test]
fn restricting_preserves_all_guards_weights_phases_and_remaining_factors() {
    let x = KernelVariable::InputKet(0);
    let y = KernelVariable::InputBra(0);
    let source = Product {
        common: sum(vec![], -3, vec![phase(&y, 2)]),
        factors: vec![
            sum(vec![bit(&y)], 2, vec![phase(&x, 1)]),
            sum(
                vec![],
                1,
                vec![KernelPhasePolynomial::default(), phase(&y, 1)],
            ),
        ],
    };
    for value in [false, true] {
        let result = restrict(&source, &x, value, &mut Backend::new(100)).unwrap();
        for input in 0..4 {
            let original_input = (input & !1) | usize::from(value);
            assert_eq!(evaluate(&result, input), evaluate(&source, original_input));
        }
        assert_eq!(evaluate(&result, 2), zero());
        assert_ne!(evaluate(&result, 0), zero());
    }
}

#[test]
fn one_budget_is_shared_across_both_branches_and_every_refusal_is_inconclusive() {
    let p = fixture();
    let mut full = Backend::new(100);
    assert!(prove(p.clone(), p.clone(), &mut full, 0));
    let required = 100 - full.steps;
    for allowed in 0..required {
        assert!(!prove(p.clone(), p.clone(), &mut Backend::new(allowed), 0));
    }
    assert!(prove(p.clone(), p.clone(), &mut Backend::new(required), 0));
    let mut no_splits = Backend::new(100);
    no_splits.splits = 0;
    assert!(!prove(p.clone(), p.clone(), &mut no_splits, 0));
    assert!(!prove(
        p.clone(),
        p,
        &mut Backend::new(100),
        MAX_PRODUCT_SPLIT_DEPTH
    ));
}

#[test]
fn bound_paths_cannot_be_split_as_free_coordinates() {
    let path = KernelVariable::PathKet { term: 1, path: 0 };
    let p = Product {
        common: unit(),
        factors: vec![sum(vec![], 1, vec![phase(&path, 1)])],
    };
    assert!(!prove(p.clone(), p.clone(), &mut Backend::new(100), 0));
    assert!(restrict(&p, &path, false, &mut Backend::new(100)).is_none());
    assert!(restrict(&p, &path, true, &mut Backend::new(100)).is_none());
}

#[test]
fn an_exact_zero_factor_is_zero_but_a_refused_factor_is_not() {
    let x = KernelVariable::InputKet(0);
    let p = Product {
        common: unit(),
        factors: vec![
            sum(vec![bit(&x)], 1, vec![KernelPhasePolynomial::default()]),
            sum(vec![], 2, vec![phase(&x, 1)]),
        ],
    };
    let zero_case = restrict(&p, &x, true, &mut Backend::new(100)).unwrap();
    for input in 0..4 {
        assert_eq!(evaluate(&zero_case, input), zero());
    }
    assert!(restrict(&p, &x, true, &mut Backend::new(0)).is_none());
    let nonzero = restrict(&p, &x, false, &mut Backend::new(100)).unwrap();
    assert_ne!(evaluate(&nonzero, 0), zero());
}

#[test]
fn failed_late_factor_never_exposes_a_successful_restriction_prefix() {
    let mut p = fixture();
    p.factors
        .push(sum(vec![], 3, vec![phase(&KernelVariable::InputBra(0), 1)]));
    let mut full = Backend::new(100);
    let result = restrict(&p, &KernelVariable::InputKet(0), false, &mut full).unwrap();
    for i in 0..4 {
        assert_eq!(evaluate(&result, i), evaluate(&p, i & !1));
    }
    let required = 100 - full.steps;
    for steps in 0..required {
        assert!(
            restrict(
                &p,
                &KernelVariable::InputKet(0),
                false,
                &mut Backend::new(steps)
            )
            .is_none()
        );
    }
}
