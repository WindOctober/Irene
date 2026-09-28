//! Sufficient pathwise certificate, not a general channel-inequality test.
//! Path cardinality and scalar magnitude are checked outside the Boolean
//! optimizer. All visible outputs and the ENTIRE rational phase are checked.
use super::*;

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
    if std::env::var_os("IRENE_DISABLE_PATHWISE_GRAPH").is_some() {
        return None;
    }
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
    let result = match run_graph_query(&query) {
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
    #[test]
    fn certificate_checks_weights_phase_outputs_histories_and_binders() {
        let p = prepared();
        assert_eq!(compare(&p).unwrap().unwrap().verdict, Verdict::Equivalent);
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
