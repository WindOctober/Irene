use super::*;
use crate::symbolic::PhaseCoefficient;
fn prepared() -> PreparedComparison {
    let p = crate::frontend::openqasm3::parse_str(
        "OPENQASM 3.0; include \"stdgates.inc\"; qubit q; h q;",
        "graph-test",
    )
    .unwrap();
    let q = qubits(&p)[0].clone();
    let config = EquivalenceConfig {
        input_pairs: vec![InputPair {
            left: Endpoint::Quantum(q.clone()),
            right: Endpoint::Quantum(q.clone()),
        }],
        output_pairs: vec![OutputPair {
            left: Endpoint::Quantum(q.clone()),
            right: Endpoint::Quantum(q),
        }],
        ..EquivalenceConfig::default()
    };
    prepare_comparison(&p, &p, &config).unwrap()
}
fn answer(consensus: PortfolioConsensus) -> Result<PortfolioResult, SolverDisagreement> {
    Ok(PortfolioResult {
        consensus,
        results: vec![],
    })
}

#[test]
fn only_unsat_certifies_equivalence() {
    let p = prepared();
    let before = p.clone();
    for consensus in [PortfolioConsensus::Sat, PortfolioConsensus::Inconclusive] {
        assert!(compare_with(&p, |_| answer(consensus)).is_none());
    }
    let a = compare_with(&p, |query| {
        assert!(query.contains("(check-sat)"));
        answer(PortfolioConsensus::Unsat)
    })
    .unwrap()
    .unwrap();
    assert_eq!(a.verdict, Verdict::Equivalent);
    assert_eq!(a.evidence, Evidence::PathwiseGraph);
    assert_eq!(a.solver_queries.len(), 1);
    assert_eq!(p, before);
}

#[test]
fn disagreement_is_not_swallowed() {
    let error = SolverDisagreement { answers: vec![] };
    assert_eq!(
        compare_with(&prepared(), |_| Err(error.clone()))
            .unwrap()
            .unwrap_err(),
        error
    );
}

#[test]
fn only_supported_constant_real_weights_have_a_square() {
    let one = BigRational::from_integer(1.into());
    assert_eq!(square(&Scalar::one()), Some(one.clone()));
    assert_eq!(
        square(&Scalar::Neg(Box::new(Scalar::one()))),
        Some(one.clone())
    );
    assert_eq!(
        square(&Scalar::Sqrt(Box::new(Scalar::Rational(-one)))),
        None
    );
    let mut p = prepared();
    p.right.hps.components[0].scalar = Scalar::Rational(BigRational::from_integer(2.into()));
    assert!(compare_with(&p, |_| panic!("weight mismatch")).is_none());
}

#[test]
#[ignore = "requires installed SMT solvers"]
fn rational_phase_identity_is_checked_semantically() {
    let mut p = prepared();
    let x = p.left.hps.input.quantum.values().next().unwrap().clone();
    let y = p.left.terminals[0].outputs[0].value.clone();
    let half = PhaseCoefficient::rational(BigRational::new(1.into(), 2.into()));
    // (x xor y)/2 equals x/2 + y/2 modulo one, although selectors differ.
    p.left.hps.components[0]
        .phase
        .add_boolean(&x.xor(&y), half.clone());
    p.right.hps.components[0]
        .phase
        .add_boolean(&x, half.clone());
    p.right.hps.components[0].phase.add_boolean(&y, half);
    assert_eq!(compare(&p).unwrap().unwrap().verdict, Verdict::Equivalent);
    p.right.hps.components[0].phase.add_boolean(
        &y,
        PhaseCoefficient::rational(BigRational::new(1.into(), 3.into())),
    );
    assert!(compare(&p).is_none());
}

#[test]
#[ignore = "requires installed SMT solvers"]
fn certificate_checks_weights_phase_outputs_histories_and_binders() {
    let p = prepared();
    assert_eq!(compare(&p).unwrap().unwrap().verdict, Verdict::Equivalent);
    let mut renamed = p.clone();
    let old_path = *renamed.right.hps.components[0]
        .path_support
        .iter()
        .next()
        .unwrap();
    let rename = |v: &Variable| match v {
        Variable::Path(i) if *i == old_path => BooleanPolynomial::variable(Variable::Path(777)),
        _ => BooleanPolynomial::variable(v.clone()),
    };
    renamed.right.hps.components[0].path_support = [777].into();
    renamed.right.hps.components[0].phase.map_variables(rename);
    for output in &mut renamed.right.terminals[0].outputs {
        output.value = output.value.map_variables(rename);
    }
    assert_eq!(
        compare(&renamed).unwrap().unwrap().verdict,
        Verdict::Equivalent
    );
    let mut changed = p.clone();
    changed.right.hps.components[0].scalar =
        Scalar::Rational(BigRational::from_integer(2.into()));
    assert!(compare(&changed).is_none());
    let mut changed = p.clone();
    let selected = Scalar::Select {
        condition: BooleanPolynomial::variable(Variable::Path(0)),
        when_true: Box::new(Scalar::Rational(BigRational::from_integer(1.into()))),
        when_false: Box::new(Scalar::Rational(BigRational::from_integer(2.into()))),
    };
    changed.left.hps.components[0].scalar = selected.clone();
    changed.right.hps.components[0].scalar = selected;
    assert!(compare(&changed).is_none());
    let mut changed = p.clone();
    changed.right.hps.components[0].path_support.insert(999);
    assert!(compare(&changed).is_none());
    let mut changed = p.clone();
    changed.right.hps.components[0]
        .output
        .history
        .push(HistoryEntry::Discard {
            value: BooleanPolynomial::one(),
        });
    assert!(compare(&changed).is_none());
    let mut changed = p.clone();
    changed.right.hps.components[0]
        .guard
        .push(BooleanPolynomial::one());
    assert!(compare(&changed).is_none());
    let mut changed = p.clone();
    let output = &mut changed.right.terminals[0].outputs[0].value;
    *output = output.xor(&BooleanPolynomial::one());
    // SAT means this pairing failed, not a NEQ certificate for path sums.
    assert!(compare(&changed).is_none());
    let mut changed = p.clone();
    let path = *changed.right.hps.components[0]
        .path_support
        .iter()
        .next()
        .unwrap();
    changed.right.hps.components[0].phase.add_boolean(
        &BooleanPolynomial::variable(Variable::Path(path)),
        PhaseCoefficient::rational(BigRational::new(1.into(), 4.into())),
    );
    assert!(compare(&changed).is_none());
    let mut changed = p;
    changed.right.hps.components[0].phase.add_boolean(
        &BooleanPolynomial::one(),
        PhaseCoefficient::rational(BigRational::new(1.into(), 7.into())),
    );
    assert_eq!(
        compare(&changed).unwrap().unwrap().verdict,
        Verdict::Equivalent
    );
}
