//! Sufficient pathwise certificate, not a general channel-inequality test.
//! Path cardinality and scalar magnitude are checked outside the Boolean
//! optimizer. All visible outputs and the ENTIRE rational phase are checked.
use super::phase::{bit_width, lcm, modulo_one, rational_zero};
use super::*;
use crate::equivalence::solver::query::run_graph_query;
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

pub(in crate::equivalence) fn compare(
    p: &PreparedComparison,
) -> Option<Result<Analysis, SolverDisagreement>> {
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
