use super::*;
use std::collections::BTreeMap;
use std::convert::Infallible;

fn path() -> KernelVariable {
    KernelVariable::PathKet { term: 0, path: 0 }
}
fn var(v: KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v)
}
fn term() -> WorkingTerm {
    WorkingTerm {
        constraints: vec![],
        paths: [path()].into(),
        coefficient: KernelScalar::Rational(integer(3)),
        phase: KernelPhasePolynomial::default(),
    }
}

// Independent exact oracle in Q(zeta_8), with zeta_8^4 = -1.
// No production path-sum reducer or floating-point tolerance is used here.
#[derive(Debug, Clone, PartialEq, Eq)]
struct Cyclo([BigRational; 4]);
impl Cyclo {
    fn zero() -> Self {
        Self(std::array::from_fn(|_| integer(0)))
    }
    fn rational(r: BigRational) -> Self {
        let mut result = Self::zero();
        result.0[0] = r;
        result
    }
    fn root(exponent: i64) -> Self {
        let e = exponent.rem_euclid(8) as usize;
        let mut result = Self::zero();
        result.0[e % 4] = integer(if e < 4 { 1 } else { -1 });
        result
    }
    fn add(mut self, other: Self) -> Self {
        for i in 0..4 {
            self.0[i] += &other.0[i];
        }
        self
    }
    fn multiply(self, other: Self) -> Self {
        let mut result = Self::zero();
        for i in 0..4 {
            for j in 0..4 {
                let sign = integer(if i + j < 4 { 1 } else { -1 });
                result.0[(i + j) % 4] += &self.0[i] * &other.0[j] * sign;
            }
        }
        result
    }
}

type Values = BTreeMap<KernelVariable, bool>;
fn boolean(p: &KernelBooleanPolynomial, values: &Values) -> bool {
    p.as_graph()
        .evaluate::<Infallible>(|v| Ok(values[&KernelVariable::from_graph_variable(v)]))
        .unwrap()
}
fn scalar(s: &KernelScalar, values: &Values) -> Cyclo {
    match s {
        KernelScalar::Rational(r) => Cyclo::rational(r.clone()),
        KernelScalar::Mul(a, b) => scalar(a, values).multiply(scalar(b, values)),
        KernelScalar::Add(a, b) => scalar(a, values).add(scalar(b, values)),
        KernelScalar::Neg(a) => Cyclo::rational(integer(-1)).multiply(scalar(a, values)),
        KernelScalar::Sqrt(a) => {
            assert_eq!(**a, KernelScalar::Rational(integer(2)));
            // sqrt(2) = zeta_8 - zeta_8^3.
            Cyclo::root(1).add(Cyclo::root(7))
        }
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => scalar(
            if boolean(condition, values) {
                when_true
            } else {
                when_false
            },
            values,
        ),
        _ => panic!("unsupported test scalar"),
    }
}
fn sum(t: &WorkingTerm, inputs: &Values) -> Cyclo {
    let paths: Vec<_> = t.paths.iter().cloned().collect();
    let mut result = Cyclo::zero();
    for mask in 0..1usize << paths.len() {
        let mut values = inputs.clone();
        for (i, p) in paths.iter().enumerate() {
            values.insert(p.clone(), mask & (1 << i) != 0);
        }
        if t.constraints.iter().any(|p| boolean(p, &values)) {
            continue;
        }
        let mut turns = integer(0);
        for (p, c) in t.phase.selectors() {
            if boolean(&p, &values) {
                turns += c.as_rational().expect("rational test phase");
            }
        }
        let eighths = turns * integer(8);
        assert!(eighths.is_integer());
        let exponent = i64::try_from(eighths.to_integer()).unwrap();
        result = result.add(scalar(&t.coefficient, &values).multiply(Cyclo::root(exponent)));
    }
    result
}
fn finish(t: &mut WorkingTerm, factor: KernelScalar) {
    t.coefficient = factor.multiply(t.coefficient.clone());
    assert!(t.paths.remove(&path()));
}
fn assert_same(before: &WorkingTerm, after: &WorkingTerm) {
    for mask in 0..4 {
        let inputs = [
            (KernelVariable::InputKet(0), mask & 1 != 0),
            (KernelVariable::InputBra(0), mask & 2 != 0),
        ]
        .into();
        assert_eq!(sum(before, &inputs), sum(after, &inputs));
    }
}

#[test]
fn fourier_and_omega_preserve_exact_sums_for_all_two_input_parities() {
    let y = var(path());
    let a = var(KernelVariable::InputKet(0));
    let b = var(KernelVariable::InputBra(0));
    let monomials = [
        KernelBooleanPolynomial::one(),
        a.clone(),
        b.clone(),
        a.and(&b),
    ];
    for mask in 0..16 {
        let mut parity = KernelBooleanPolynomial::zero();
        for (i, m) in monomials.iter().enumerate() {
            if mask & (1 << i) != 0 {
                parity = parity.xor(m);
            }
        }
        for quarter in 0..4 {
            for offset in 0..8 {
                let mut before = term();
                before.coefficient = KernelScalar::Select {
                    condition: a.clone(),
                    when_true: Box::new(KernelScalar::Rational(integer(2))),
                    when_false: Box::new(KernelScalar::Rational(integer(3))),
                };
                before
                    .phase
                    .add_boolean(&y, PhaseCoefficient::rational(ratio(quarter, 4)));
                before
                    .phase
                    .add_boolean(&y.and(&parity), PhaseCoefficient::rational(ratio(1, 2)));
                before
                    .phase
                    .add_boolean(&b, PhaseCoefficient::rational(ratio(offset, 8)));
                let mut after = before.clone();
                let rule = after.phase_sum_profile(&path());
                let factor = rule.apply(&mut after, &path()).expect("closed-form sum");
                finish(&mut after, factor);
                assert_same(&before, &after);
            }
        }
    }
}

#[test]
fn vacuous_sum_and_contradictory_fourier_have_correct_weights() {
    for half in [0, 1] {
        let mut before = term();
        before
            .phase
            .add_boolean(&var(path()), PhaseCoefficient::rational(ratio(half, 2)));
        let mut after = before.clone();
        let factor = after
            .phase_sum_profile(&path())
            .apply(&mut after, &path())
            .unwrap();
        finish(&mut after, factor);
        assert_same(&before, &after);
        if half == 1 {
            assert_eq!(sum(&after, &Values::new()), Cyclo::zero());
        }
    }
}

#[test]
fn graph_fourier_keeps_zero_cofactor_phase() {
    let y = var(path());
    let a = var(KernelVariable::InputKet(0));
    let b = var(KernelVariable::InputBra(0));
    let selector = KernelBooleanPolynomial::from_graph(y.xor(&a).and(&b).as_graph());
    let mut before = term();
    before
        .phase
        .add_boolean(&selector, PhaseCoefficient::rational(ratio(1, 2)));
    before
        .phase
        .add_boolean(&a, PhaseCoefficient::rational(ratio(1, 8)));
    let mut after = before.clone();
    let factor = after.graph_fourier(&path()).unwrap();
    finish(&mut after, factor);
    assert_same(&before, &after);
}

#[test]
fn dependent_guards_scalars_and_free_coordinates_are_not_summed() {
    let mut cases = Vec::new();
    let mut guarded = term();
    guarded.constraints.push(var(path()));
    cases.push(guarded);
    let mut weighted = term();
    weighted.coefficient = KernelScalar::Select {
        condition: var(path()),
        when_true: Box::new(KernelScalar::Rational(integer(2))),
        when_false: Box::new(KernelScalar::Rational(integer(3))),
    };
    cases.push(weighted);
    for before in cases {
        let mut after = before.clone();
        assert!(
            after
                .phase_sum_profile(&path())
                .apply(&mut after, &path())
                .is_none()
        );
        assert!(after.graph_fourier(&path()).is_none());
        assert_same(&before, &after);
        assert!(after.paths.contains(&path()));
    }
    let mut free = term();
    let input = KernelVariable::InputKet(0);
    free.paths.insert(input.clone());
    assert!(matches!(
        free.phase_sum_profile(&input),
        PhaseProfile::Unsupported
    ));
    assert!(free.graph_fourier(&input).is_none());
    let missing = KernelVariable::PathBra { term: 0, path: 7 };
    assert!(matches!(
        free.phase_sum_profile(&missing),
        PhaseProfile::Unsupported
    ));
}

#[test]
fn unsupported_phase_refusal_is_transactional() {
    let mut before = term();
    before
        .phase
        .add_boolean(&var(path()), PhaseCoefficient::rational(ratio(1, 8)));
    let mut after = before.clone();
    assert!(
        after
            .phase_sum_profile(&path())
            .apply(&mut after, &path())
            .is_none()
    );
    assert!(after.graph_fourier(&path()).is_none());
    assert_eq!(after.phase, before.phase);
    assert_eq!(after.coefficient, before.coefficient);
    assert_eq!(after.constraints, before.constraints);
    assert_eq!(after.paths, before.paths);
    assert_same(&before, &after);
}
