use super::*;
fn evaluate(t: &WorkingTerm, free: &KernelVariable, value: bool) -> BigRational {
    let paths: Vec<_> = t.paths.iter().cloned().collect();
    (0..1usize << paths.len())
        .map(|bits| {
            let mut a = BTreeMap::from([(free.clone(), value)]);
            for (i, v) in paths.iter().enumerate() {
                a.insert(v.clone(), bits & (1 << i) != 0);
            }
            let boolean = |p: &KernelBooleanPolynomial| {
                p.as_graph()
                    .evaluate::<std::convert::Infallible>(|v| {
                        Ok(a[&KernelVariable::from_graph_variable(v)])
                    })
                    .unwrap()
            };
            fn scalar(
                s: &KernelScalar,
                b: &impl Fn(&KernelBooleanPolynomial) -> bool,
            ) -> BigRational {
                match s {
                    KernelScalar::Rational(r) => r.clone(),
                    KernelScalar::Mul(x, y) => scalar(x, b) * scalar(y, b),
                    KernelScalar::Add(x, y) => scalar(x, b) + scalar(y, b),
                    KernelScalar::Neg(x) => -scalar(x, b),
                    KernelScalar::Select {
                        condition,
                        when_true,
                        when_false,
                    } => scalar(if b(condition) { when_true } else { when_false }, b),
                    _ => panic!("unexpected scalar"),
                }
            }
            if t.constraints.iter().any(&boolean) {
                return integer(0);
            }
            let phase = t
                .phase
                .selectors()
                .filter(|(p, _)| boolean(p))
                .fold(integer(0), |s, (_, c)| s + c.as_rational().unwrap());
            let sign = if phase.is_integer() {
                1
            } else {
                assert!((phase * integer(2)).is_integer());
                -1
            };
            scalar(&t.coefficient, &boolean) * integer(sign)
        })
        .fold(integer(0), |a, b| a + b)
}
#[test]
fn every_candidate_preserves_both_coherent_branches_and_free_selectors() {
    let vars: Vec<_> = (0..3)
        .map(|path| KernelVariable::PathKet { term: 0, path })
        .collect();
    let free = KernelVariable::QuantumOutputKet(0);
    let p: Vec<_> = vars
        .iter()
        .cloned()
        .map(KernelBooleanPolynomial::variable)
        .collect();
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(
        &p[0].and(&p[1]),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
    );
    let t = WorkingTerm {
        paths: vars.iter().cloned().collect(),
        constraints: vec![
            p[1].and(&p[2])
                .xor(&KernelBooleanPolynomial::variable(free.clone())),
        ],
        coefficient: KernelScalar::Select {
            condition: p[0].clone(),
            when_true: Box::new(KernelScalar::Rational(integer(3))),
            when_false: Box::new(KernelScalar::Rational(integer(1))),
        },
        phase,
    };
    for v in &vars {
        let children = children(&t, v).unwrap();
        for bit in [false, true] {
            let actual = children
                .iter()
                .map(|r| match r {
                    Reduction::Zero => integer(0),
                    Reduction::Residual => panic!("small exact cofactor refused"),
                    Reduction::Sum(s) => evaluate(s, &free, bit),
                    Reduction::Exact(s) => evaluate(
                        &WorkingTerm {
                            constraints: s.constraints.clone(),
                            paths: BTreeSet::new(),
                            coefficient: s.coefficient.clone(),
                            phase: s.phase.clone(),
                        },
                        &free,
                        bit,
                    ),
                })
                .fold(integer(0), |a, b| a + b);
            assert_eq!(evaluate(&t, &free, bit), actual);
        }
    }
}
