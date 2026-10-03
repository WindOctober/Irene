//! Exact contraction of a coherent full-input/full-output operator HPS.
use super::reduce_path_sums;
use crate::symbolic::{BooleanPolynomial, Component, HybridMemory, Scalar, Variable};
use num_bigint::BigInt;
use num_rational::BigRational;

/// Constructs the complete normalized trace summand. The caller MUST establish
/// unitarity before using this as channel equality or inequality.
/// No history/density representatives, partial outputs, initialized inputs,
/// or coherent sibling components may be supplied as a complete operator.
pub(crate) fn normalized_trace_component(
    mut c: Component,
    input: &HybridMemory,
) -> Option<Component> {
    let trace_started = std::time::Instant::now();
    if !c.output.classical.is_empty()
        || !c.output.history.is_empty()
        || !input.classical.is_empty()
        || !input.history.is_empty()
        || c.output.quantum.keys().ne(input.quantum.keys())
        || input
            .quantum
            .iter()
            .any(|(q, value)| *value != BooleanPolynomial::variable(Variable::Input(q.clone())))
    {
        return None;
    }
    // Tr(V) = sum_x sum_y a(x,y) [f(x,y)=x]. This is contraction,
    // not partial trace or deletion of an observed quantum output.
    for (q, output) in &c.output.quantum {
        c.guard.push(output.xor(&input.quantum[q]));
    }
    c.output.quantum.clear();
    let Some(fresh) = c.path_support.last().map_or(Some(0), |p| p.checked_add(1)) else {
        return None;
    };
    if fresh.checked_add(input.quantum.len()).is_none() {
        return None;
    }
    let mut replacements = std::collections::BTreeMap::new();
    for (i, q) in input.quantum.keys().enumerate() {
        let path = fresh + i;
        replacements.insert(
            Variable::Input(q.clone()),
            BooleanPolynomial::variable(Variable::Path(path)),
        );
        c.path_support.insert(path);
    }
    // Input-to-fresh-path renaming is simultaneous and capture-free. Traverse
    // each shared phase/guard DAG once, not once for every declared input.
    let rename = |v: &Variable| {
        replacements
            .get(v)
            .cloned()
            .unwrap_or_else(|| BooleanPolynomial::variable(v.clone()))
    };
    c.guard = BooleanPolynomial::map_roots(&c.guard, rename);
    c.phase.map_variables(rename);
    // Scalar conditions also retain every dependency. Their usually tiny AST
    // uses the existing exact substitution; disjoint fresh ranges make these
    // substitutions equivalent to the simultaneous renaming above.
    for (variable, replacement) in &replacements {
        c.scalar = c.scalar.substitute(variable, replacement);
    }
    // Every input is summed, including inputs absent from the phase/guards.
    // Vacuous elimination supplies their exact factor two.
    c.scalar = c.scalar.multiply(Scalar::rational(BigRational::new(
        BigInt::from(1),
        BigInt::from(1) << input.quantum.len(),
    )));
    if std::env::var_os("IRENE_DEBUG_COMPACTION").is_some() {
        eprintln!(
            "unitary trace rebind seconds={:.6} paths={} guards={} phase_selectors={} phase_storage={}",
            trace_started.elapsed().as_secs_f64(),
            c.path_support.len(),
            c.guard.len(),
            c.phase.selectors().count(),
            c.phase.storage_size()
        );
    }
    if !reduce_path_sums(&mut c, false) {
        if std::env::var_os("IRENE_DEBUG_COMPACTION").is_some() {
            eprintln!(
                "unitary trace contradiction seconds={:.6}",
                trace_started.elapsed().as_secs_f64()
            );
        }
        // Exact contradiction in the complete single-component summand.
        c.scalar = Scalar::zero();
        c.phase = Default::default();
        c.guard.clear();
        c.path_support.clear();
        return Some(c);
    }
    if std::env::var_os("IRENE_DEBUG_COMPACTION").is_some() {
        eprintln!(
            "unitary trace: paths={} guards={} phase_selectors={} phase_storage={} scalar={} seconds={:.6}",
            c.path_support.len(),
            c.guard.len(),
            c.phase.selectors().count(),
            c.phase.storage_size(),
            c.scalar,
            trace_started.elapsed().as_secs_f64()
        );
    }
    Some(c)
}

#[cfg(test)]
mod tests;
