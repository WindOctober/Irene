//! Optional full-unitary proof candidates. Approximate results are deliberately
//! separate from `analyze`'s exact Verdict, and never certify non-equivalence.
use super::miter as unitary_miter;
pub use super::rewrite::dependency::Statistics;
use crate::equivalence::*;
use crate::ir::Program;
use num_rational::BigRational;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Wire,
    Dag,
    DagScheduled,
}
#[derive(Clone, Debug)]
pub struct Options {
    pub mode: Mode,
    /// Source/operator phase order above which interval cancellation is eligible.
    pub exact_order: u64,
    /// None preserves exact semantics. Otherwise this bounds channel diamond distance.
    pub diamond_tolerance: Option<BigRational>,
}
#[derive(Clone, Debug)]
pub struct Candidate {
    pub circuit: Program,
    pub identity: Program,
    pub statistics: Statistics,
}
impl Candidate {
    pub fn is_exact(&self) -> bool {
        self.statistics.diamond_error == BigRational::from_integer(0.into())
    }
}

pub fn candidate(
    left: &Program,
    right: &Program,
    config: &EquivalenceConfig,
    options: &Options,
) -> Option<Candidate> {
    if !options.exact_order.is_power_of_two() || options.exact_order < 8 {
        return None;
    }
    if options
        .diamond_tolerance
        .as_ref()
        .is_some_and(|v| v < &BigRational::from_integer(0.into()))
    {
        return None;
    }
    if !super::full_quantum_interface(left, right, config) {
        return None;
    }
    crate::symbolic::numeric_domains(left).ok()?;
    crate::symbolic::numeric_domains(right).ok()?;
    let (forward, inverse) = super::orient_pair(left, right);
    let started = std::time::Instant::now();
    let (circuit, identity) = unitary_miter::miter(forward, inverse).ok()?;
    let (circuit, mut statistics) = if options.mode == Mode::Wire {
        let before = circuit.operation_count();
        let next = super::rewrite::preprocess_with(&circuit, super::rewrite::Strategy::Wire)
            .unwrap_or(circuit);
        let after = next.operation_count();
        (
            next,
            Statistics {
                before,
                after,
                diamond_error: BigRational::from_integer(0.into()),
                ..Default::default()
            },
        )
    } else {
        super::rewrite::dependency::reduce(
            &circuit,
            options.exact_order,
            options.diamond_tolerance.clone(),
            options.mode == Mode::DagScheduled,
        )?
    };
    statistics.elapsed_us = started.elapsed().as_micros();
    Some(Candidate {
        circuit,
        identity,
        statistics,
    })
}

/// Exact checking of the remaining candidate, using the existing HPS/kernel
/// machinery. A mismatch of an approximate candidate says NOTHING about the
/// original pair: callers must report Unknown unless they have a separate
/// certified lower bound on the original channel distance.
pub fn proves_identity(c: &Candidate) -> bool {
    if c.circuit.body.statements.is_empty() {
        return true;
    }
    if c.statistics.after >= c.statistics.before {
        return false;
    }
    let wires = crate::equivalence::qubits(&c.circuit);
    let config = EquivalenceConfig {
        input_pairs: wires
            .iter()
            .map(|q| InputPair::quantum(q.clone(), q.clone()))
            .collect(),
        output_pairs: wires
            .into_iter()
            .map(|q| OutputPair {
                left: Endpoint::Quantum(q.clone()),
                right: Endpoint::Quantum(q),
            })
            .collect(),
        numeric_input_pairs: vec![],
    };
    analyze(&c.circuit, &c.identity, &config).is_ok_and(|r| r.verdict == Verdict::Equivalent)
}
