//! Structural HPS coefficient simplification with certified numerical leaves.
//!
//! Shared Boolean expressions and structural elimination are attempted first;
//! small physical-wire frontiers refine unresolved results afterward. Every
//! path and input remains accounted for in the normalized trace. Boolean
//! guards/selectors stay exact; MPFR endpoints enclose all scalar/phase values.
//! For a d-dimensional unitary V and t=Tr(V)/d, choose its global phase so that
//! ||V-exp(i phi)I||_F^2=2d(1-|t|). The channel diamond distance is therefore
//! at most 2 sqrt(2d(1-|t|)). This intentionally conservative, dimension-aware
//! bound does not confuse average trace fidelity with worst-case equivalence.
//! A normalized maximally entangled input also gives a lower bound:
//! 2 sqrt(1-|t|^2). A strictly positive, error-corrected lower bound proves NEQ.
//! These are separate certificates; the exact `analyze` route is unchanged.
use super::miter as unitary_miter;
use crate::ir::{NumericExpr, Program};
use crate::symbolic::{
    BooleanPolynomial, ExecutionConfig, OutputSelection, Scalar, Variable, execute,
    normalized_trace_component,
};
use num_rational::BigRational;
use rug::{Float, Integer, float::Round};
use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

use super::numeric::{Complex, Interval, PREC, float_rational, number};
mod frontier;
mod structured;

/// Certified distance enclosure for a complete static unitary versus identity.
/// `bound` alone is never a NEQ witness. A positive `lower_bound` is, provided
/// any error incurred before this check has been subtracted first.
#[derive(Debug)]
pub struct Report {
    /// Contraction strategy, independent of the certified coefficient domain.
    pub method: &'static str,
    pub precision: u32,
    pub bound: Option<BigRational>,
    pub lower_bound: Option<BigRational>,
    pub reason: &'static str,
    pub paths: usize,
    pub work: usize,
    pub max_width: usize,
    pub nodes: usize,
}
impl Report {
    /// Triangle inequality transfers the residual lower bound to the original
    /// circuit. Nonnegative preprocessing error must itself be a certified
    /// channel diamond-distance upper bound, not an empirical tolerance.
    pub fn corrected_lower_bound(&self, preprocessing_error: &BigRational) -> Option<BigRational> {
        let zero = BigRational::from_integer(0.into());
        if preprocessing_error < &zero {
            return None;
        }
        Some((self.lower_bound.as_ref()? - preprocessing_error).max(zero))
    }
}

/// Apply the difference channel to one half of a normalized maximally entangled
/// state. The two pure outputs have overlap Tr(V)/d and trace-norm distance
/// 2 sqrt(1-|Tr(V)/d|^2), a lower bound on the channel diamond norm. In particular
/// a global phase has overlap modulus one and must not yield a NEQ certificate.
fn trace_distance_lower(trace: &Complex) -> Option<BigRational> {
    let norm_squared = trace.re.square().add(&trace.im.square()).finite()?;
    let one = Float::with_val(PREC, 1);
    let mut gap = Float::with_val_round(PREC, &one - &norm_squared.hi, Round::Down).0;
    if gap <= 0 {
        return Some(BigRational::from_integer(0.into()));
    }
    gap.sqrt_round(Round::Down);
    let lower = Float::with_val_round(PREC, &gap * 2, Round::Down).0;
    float_rational(&lower)
}

/// Common certificate extraction for both structural and physical-wire sums.
fn trace_bounds(trace: &Complex, n: usize) -> Option<(BigRational, BigRational)> {
    let norm = trace.re.square().add(&trace.im.square()).sqrt()?.finite()?;
    if norm.lo > 1 {
        return None;
    }
    let lower = trace_distance_lower(trace)?;
    let one = Float::with_val(PREC, 1);
    let gap = Float::with_val_round(PREC, &one - &norm.lo, Round::Up).0;
    let scale = Float::with_val(PREC, Integer::from(1) << (n + 3));
    let mut upper = Float::with_val_round(PREC, &gap * &scale, Round::Up).0;
    upper.sqrt_round(Round::Up);
    if !upper.is_finite() {
        return None;
    }
    if upper > 2 {
        upper = Float::with_val(PREC, 2);
    }
    Some((float_rational(&upper)?, lower))
}

/// A cheap exact rational distance certificate from an already proved
/// r = |Tr(V)/d|^2. For 0 <= r <= 1, diamond distance >= 2 sqrt(1-r)
/// which is at least 2(1-r). No new HPS contraction or numerical rounding is needed.
/// This deliberately weaker rational bound is strictly positive for every
/// rational trace mismatch. Callers must subtract any preprocessing error.
pub fn exact_trace_distance_lower(norm_squared: &BigRational) -> Option<BigRational> {
    let zero = BigRational::from_integer(0.into());
    let one = BigRational::from_integer(1.into());
    if norm_squared < &zero || norm_squared > &one {
        return None;
    }
    Some((one - norm_squared) * BigRational::from_integer(2.into()))
}
/// Checks a complete static unitary against identity, for all coherent inputs.
/// Measurements, reset, classical observation and runtime numeric inputs refuse.
pub fn identity_bound(program: &Program) -> Report {
    identity_bound_with_tolerance(
        program,
        &BigRational::new(1.into(), 1_000_000_000_000i64.into()),
    )
}

/// The target guides refinement only; every returned bound remains certified.
/// Give the entire initial HPS attempt five seconds, then refine an
/// inconclusive enclosure with the complete physical-wire matrix. Cooperative
/// checks include HPS construction and elimination, not only contraction.
/// An expired probe gets a normal-budget HPS retry if the matrix cannot decide.
pub fn identity_bound_with_tolerance(program: &Program, target: &BigRational) -> Report {
    identity_bound_with_error(program, target, &BigRational::from_integer(0.into()))
}

/// The input-state early exit must survive the certified preprocessing error.
/// Bounds in the report still describe `program`; callers correct them with
/// that error when certifying the original program pair.
pub fn identity_bound_with_error(
    program: &Program,
    target: &BigRational,
    preprocessing_error: &BigRational,
) -> Report {
    assert!(preprocessing_error >= &BigRational::from_integer(0.into()));
    probe_then_frontier(
        structured::identity_bound_with_budget(program, Duration::from_secs(5)),
        target,
        || {
            frontier::identity_bound_with_witness_target(
                program,
                target,
                &(target + preprocessing_error),
            )
        },
        || structured::identity_bound(program),
    )
}

fn decisive(report: &Report, target: &BigRational) -> bool {
    report.bound.as_ref().is_some_and(|u| u <= target)
        || report.lower_bound.as_ref().is_some_and(|l| l > target)
}

fn probe_then_frontier(
    probe: Report,
    target: &BigRational,
    frontier: impl FnOnce() -> Option<Report>,
    full_hps: impl FnOnce() -> Report,
) -> Report {
    let interrupted = probe.reason == structured::TIME_BUDGET_REASON;
    let report = refine_with_frontier(probe, target, frontier);
    if interrupted && !decisive(&report, target) {
        // The scoped probe deadline has ended. Start a complete HPS attempt
        // with the ordinary resource limits, retaining any matrix enclosure.
        // A completed (rather than timed-out) probe already had these same
        // work limits and need not be repeated with an identical input.
        refine_with_frontier(full_hps(), target, || Some(report))
    } else {
        report
    }
}

fn refine_with_frontier(
    first: Report,
    target: &BigRational,
    frontier: impl FnOnce() -> Option<Report>,
) -> Report {
    if decisive(&first, target) {
        return first;
    }
    if let Some(mut report) = frontier() {
        if decisive(&report, target) {
            return report;
        }
        if report.method != first.method {
            report.method = "structured+frontier";
        }
        report.precision = report.precision.max(first.precision);
        report.bound = match (first.bound, report.bound) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
        report.lower_bound = match (first.lower_bound, report.lower_bound) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (a, b) => a.or(b),
        };
        report.work += first.work;
        report.nodes = report.nodes.max(first.nodes);
        // Keep structural diagnostics for the unresolved symbolic residual.
        report.paths = first.paths;
        report.max_width = report.max_width.max(first.max_width);
        return report;
    }
    first
}
