use super::*;

#[test]
fn refinement_retains_improvement_after_refusal_and_exceeds_four_rounds() {
    let t = WorkingTerm {
        paths: (0..9)
            .map(|path| KernelVariable::PathKet { term: 0, path })
            .collect(),
        constraints: vec![],
        coefficient: KernelScalar::Rational(integer(1)),
        phase: KernelPhasePolynomial::default(),
    };
    let mut steps = 0;
    let result = refine(t, |current| {
        steps += 1;
        if steps > 6 {
            return None;
        }
        let mut next = current.clone();
        next.paths.pop_first();
        // A vacuous coherent path contributes exactly two.
        next.coefficient = KernelScalar::Rational(integer(1 << steps));
        Some(Reduction::Sum(Box::new(next)))
    });
    let Reduction::Sum(result) = result else {
        panic!("expected retained candidate")
    };
    assert_eq!(steps, 7);
    assert_eq!(result.paths.len(), 3);
    assert_eq!(result.coefficient, KernelScalar::Rational(integer(64)));
    let mut calls = 0;
    let _ = refine(*result, |t| {
        calls += 1;
        Some(Reduction::Sum(Box::new(t.clone())))
    });
    assert_eq!(calls, 1, "equal-cost steps terminate without oscillation");
}

#[test]
fn davio_import_preserves_guards_and_phase_for_every_assignment_and_order() {
    let mut vars: Vec<_> = (0..4)
        .map(|path| KernelVariable::PathKet { term: 0, path })
        .collect();
    vars.extend([KernelVariable::InputKet(0), KernelVariable::InputBra(0)]);
    let p: Vec<_> = vars
        .iter()
        .cloned()
        .map(KernelBooleanPolynomial::variable)
        .collect();
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(
        &p[0].and(&p[1].xor(&p[4])),
        PhaseCoefficient::rational(ratio(1, 8)),
    );
    phase.add_boolean(&p[0].and(&p[2]), PhaseCoefficient::rational(ratio(1, 2)));
    phase.add_boolean(&p[0].and(&p[3]), PhaseCoefficient::rational(ratio(1, 2)));
    let original = WorkingTerm {
        paths: vars[..4].iter().cloned().collect(),
        constraints: vec![p[1].xor(&p[0].and(&p[5])), p[2].and(&p[3].xor(&p[4]))],
        phase,
        coefficient: KernelScalar::Rational(ratio(3, 7)),
    };
    for order in [
        vars[..4].to_vec(),
        vars[..4].iter().rev().cloned().collect(),
        central_order(&original),
    ] {
        let result = normalize(&original, &order).unwrap();
        assert_eq!(result.paths, original.paths);
        assert_eq!(result.coefficient, original.coefficient);
        for bits in 0..64 {
            let boolean = |p: &KernelBooleanPolynomial| {
                p.as_graph()
                    .evaluate::<std::convert::Infallible>(|v| {
                        let v = KernelVariable::from_graph_variable(v);
                        Ok(bits >> vars.iter().position(|w| *w == v).unwrap() & 1 != 0)
                    })
                    .unwrap()
            };
            assert_eq!(
                original.constraints.iter().map(boolean).collect::<Vec<_>>(),
                result.constraints.iter().map(boolean).collect::<Vec<_>>()
            );
            let value = |p: &KernelPhasePolynomial| {
                p.selectors()
                    .filter(|(p, _)| boolean(p))
                    .fold(integer(0), |a, (_, c)| a + c.as_rational().unwrap())
            };
            assert!((value(&original.phase) - value(&result.phase)).is_integer());
        }
    }
}
