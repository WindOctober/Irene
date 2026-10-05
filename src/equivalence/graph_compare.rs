//! Sufficient pathwise certificate, not a general channel-inequality test.
//! Path cardinality and scalar magnitude are checked outside the Boolean
//! optimizer. All visible outputs and the ENTIRE rational phase are checked.
use super::phase_compare::{bit_width, lcm, modulo_one, rational_zero};
use super::solver_query::run_graph_query;
use super::*;
use num_bigint::BigInt;

fn square(s: &Scalar) -> Option<BigRational> {
    match s {
        Scalar::Rational(r) => Some(r * r),
        Scalar::Sqrt(v) => {
            if let Scalar::Rational(r) = v.as_ref() {
                (r >= &rational_zero()).then(|| r.clone())
            } else {
                None
            }
        }
        Scalar::Mul(a, b) => Some(square(a)? * square(b)?),
        Scalar::Neg(v) => square(v),
        _ => None,
    }
}

pub(super) fn compare(p: &PreparedComparison) -> Option<Result<Analysis, SolverDisagreement>> {
    compare_with(p, run_graph_query)
}

fn compare_with(
    p: &PreparedComparison,
    run: impl FnOnce(&str) -> Result<PortfolioResult, SolverDisagreement>,
) -> Option<Result<Analysis, SolverDisagreement>> {
    let [left] = p.left.hps.components.as_slice() else {
        return None;
    };
    let [right] = p.right.hps.components.as_slice() else {
        return None;
    };
    if left.path_support.len() != right.path_support.len()
        || !left.guard.is_empty()
        || !right.guard.is_empty()
        || !left.output.history.is_empty()
        || !right.output.history.is_empty()
        // Only constant real weights admit this magnitude comparison. Equal
        // selector syntax is NOT enough: the right path renaming could change
        // a path-dependent scalar even when its original spelling matches.
        || square(&left.scalar)? != square(&right.scalar)?
    {
        return None;
    }
    // TODO: Investigate theory-aware HPS isomorphism that searches path
    // bijections while using SMT to establish Boolean/phase equivalence,
    // instead of validating only this fixed positional pairing. Survey
    // related work on graph matching modulo theories and consider integrating
    // this certificate with the existing structural-isomorphism pipeline.
    // Preserve the weight/guard/history admission conditions above: a failed
    // pairing or a SAT query must never imply inequality of the full path sums.
    let paths: BTreeMap<_, _> = right
        .path_support
        .iter()
        .zip(&left.path_support)
        .map(|(&r, &l)| (r, l))
        .collect();
    let rename = |value: &BooleanPolynomial| {
        value.map_variables(|v| match v {
            Variable::Input(_) => BooleanPolynomial::variable(v.clone()),
            Variable::Path(i) => BooleanPolynomial::variable(Variable::Path(paths[i])),
        })
    };
    let mut roots = Vec::new();
    for (a, b) in p
        .left
        .terminals
        .first()?
        .outputs
        .iter()
        .zip(&p.right.terminals.first()?.outputs)
    {
        if a.kind != b.kind {
            return None;
        }
        roots.push(a.value.xor(&rename(&b.value)));
    }
    if p.left.terminals[0].outputs.len() != p.right.terminals[0].outputs.len() {
        return None;
    }
    let output_count = roots.len();
    let mut phase = BTreeMap::new();
    for (s, c) in left.phase.selectors() {
        phase.insert(s, c.as_rational()?);
    }
    for (s, c) in right.phase.selectors() {
        let key = rename(&s);
        let value = phase.remove(&key).unwrap_or_else(rational_zero) - c.as_rational()?;
        phase.insert(key, modulo_one(value));
    }
    // A single component may differ by one input/path-INDEPENDENT global phase.
    phase.retain(|s, c| {
        *c = modulo_one(c.clone());
        !s.is_one() && *c != rational_zero()
    });
    let denominator = phase
        .values()
        .fold(BigInt::from(1), |d, c| lcm(d, c.denom().clone()));
    let coefficients: Vec<_> = phase
        .values()
        .map(|c| c.numer() * (&denominator / c.denom()))
        .collect();
    roots.extend(phase.into_keys());
    let (network, vars) = BooleanPolynomial::graph_network(&roots);
    let names: Vec<_> = (0..vars.len()).map(|i| format!("g{i}")).collect();
    let (definitions, values) = network.smt(&names, "gx")?;
    let mut differences = values[..output_count].to_vec();
    if !coefficients.is_empty() {
        let maximum = coefficients.iter().cloned().sum::<BigInt>();
        let width = bit_width(&std::cmp::max(maximum, denominator.clone()));
        let mut sum = format!("(_ bv0 {width})");
        for (selector, c) in values[output_count..].iter().zip(coefficients) {
            sum = format!("(bvadd {sum} (ite {selector} (_ bv{c} {width}) (_ bv0 {width})))");
        }
        differences.push(format!(
            "(distinct (bvurem {sum} (_ bv{denominator} {width})) (_ bv0 {width}))"
        ));
    }
    let assertion = match differences.len() {
        0 => "false".into(),
        1 => differences[0].clone(),
        _ => format!("(or {})", differences.join(" ")),
    };
    let declarations: String = names
        .iter()
        .map(|n| format!("(declare-fun {n} () Bool)\n"))
        .collect();
    let query = format!(
        "(set-logic QF_BV)\n{declarations}{definitions}(assert {assertion})\n(check-sat)\n"
    );
    let result = match run(&query) {
        Ok(r) => r,
        Err(e) => return Some(Err(e)),
    };
    // SAT rejects this pairing, NEVER the equality of the full path sums.
    if result.consensus != PortfolioConsensus::Unsat {
        return None;
    }
    let mut a = Analysis::new(Verdict::Equivalent, Evidence::PathwiseGraph, (0, 0));
    a.solver_queries.push(result);
    Some(Ok(a))
}

#[cfg(test)]
mod tests {
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
}
