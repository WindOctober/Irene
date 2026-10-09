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
use super::unitary_miter;
use crate::ir::{NumericExpr, Program};
use crate::symbolic::{
    BooleanPolynomial, ExecutionConfig, OutputSelection, Scalar, Variable, execute,
    normalized_trace_component,
};
#[cfg(test)]
use num_bigint::BigInt;
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::openqasm3;

    fn enclosure(method: &'static str, upper: Option<i64>, lower: Option<i64>) -> Report {
        Report {
            method,
            precision: PREC,
            bound: upper.map(|n| BigRational::from_integer(n.into())),
            lower_bound: lower.map(|n| BigRational::from_integer(n.into())),
            reason: "test enclosure",
            paths: 0,
            work: 0,
            max_width: 0,
            nodes: 0,
        }
    }

    #[test]
    fn expired_hps_attempt_is_inconclusive_and_matrix_has_no_inherited_deadline() {
        let p = openqasm3::parse_str(
            "OPENQASM 3.0; include \"stdgates.inc\"; qubit q; h q; h q;",
            "deadline.qasm",
        )
        .unwrap();
        let first = structured::identity_bound_with_budget(&p, Duration::ZERO);
        assert_eq!(first.reason, "HPS time budget");
        assert!(first.bound.is_none() && first.lower_bound.is_none());
        let report = refine_with_frontier(first, &tolerance(), || {
            assert!(!crate::symbolic::deadline::expired());
            frontier::identity_bound_with_tolerance(&p, &tolerance())
        });
        assert_eq!(report.method, "frontier");
        assert!(report.bound.unwrap() <= tolerance());
        let later = structured::identity_bound_with_budget(&p, Duration::from_secs(5));
        assert!(later.bound.unwrap() <= tolerance());
    }

    #[test]
    fn expired_probe_gets_full_hps_after_matrix_refusal_or_inconclusive_bounds() {
        for matrix in [None, Some(enclosure("frontier", Some(2), Some(0)))] {
            let mut probe = enclosure("structured", None, None);
            probe.reason = structured::TIME_BUDGET_REASON;
            let order = std::cell::Cell::new(0);
            let report = probe_then_frontier(
                probe,
                &tolerance(),
                || {
                    assert_eq!(order.replace(1), 0);
                    matrix
                },
                || {
                    assert_eq!(order.replace(2), 1);
                    assert!(!crate::symbolic::deadline::expired());
                    enclosure("structured", Some(0), Some(0))
                },
            );
            assert_eq!(order.get(), 2);
            assert_eq!(report.bound, Some(BigRational::from_integer(0.into())));
        }
    }

    #[test]
    fn settled_matrix_or_completed_probe_does_not_repeat_hps() {
        let mut probe = enclosure("structured", None, None);
        probe.reason = structured::TIME_BUDGET_REASON;
        let report = probe_then_frontier(
            probe,
            &tolerance(),
            || Some(enclosure("frontier", Some(0), Some(0))),
            || panic!("matrix settled the query"),
        );
        assert_eq!(report.method, "frontier");
        probe_then_frontier(
            enclosure("structured", Some(2), Some(0)),
            &tolerance(),
            || None,
            || panic!("completed probe needs no identical retry"),
        );
        probe_then_frontier(
            enclosure("structured", Some(0), Some(0)),
            &tolerance(),
            || panic!("probe settled the query"),
            || panic!("probe settled the query"),
        );
    }

    #[test]
    fn expired_probe_recovers_on_wide_program_and_keeps_unresolved_bounds() {
        let p = openqasm3::parse_str(
            "OPENQASM 3.0; include \"stdgates.inc\"; qubit[11] q; h q[0]; h q[0];",
            "wide-deadline.qasm",
        )
        .unwrap();
        let first = structured::identity_bound_with_budget(&p, Duration::ZERO);
        let report = probe_then_frontier(
            first,
            &tolerance(),
            || {
                let matrix = frontier::identity_bound_with_tolerance(&p, &tolerance());
                assert!(matrix.is_none());
                matrix
            },
            || structured::identity_bound(&p),
        );
        assert_eq!(report.method, "structured");
        assert!(report.bound.unwrap() <= tolerance());

        let mut probe = enclosure("structured", None, None);
        probe.reason = structured::TIME_BUDGET_REASON;
        let report = probe_then_frontier(
            probe,
            &BigRational::from_integer(1.into()),
            || Some(enclosure("frontier", Some(3), Some(1))),
            || enclosure("structured", Some(2), Some(0)),
        );
        assert_eq!(report.bound, Some(BigRational::from_integer(2.into())));
        assert_eq!(
            report.lower_bound,
            Some(BigRational::from_integer(1.into()))
        );
    }

    #[test]
    fn decisive_hps_bounds_do_not_run_matrix_refinement() {
        for first in [
            enclosure("structured", Some(0), Some(0)),
            enclosure("structured", Some(2), Some(1)),
        ] {
            let report = refine_with_frontier(first, &tolerance(), || {
                panic!("a decisive HPS certificate must return before matrix contraction")
            });
            assert_eq!(report.method, "structured");
        }
    }

    #[test]
    fn unresolved_hps_can_be_settled_by_matrix_or_preserved_on_refusal() {
        for first in [
            enclosure("structured", None, None),
            enclosure("structured", Some(2), Some(0)),
        ] {
            let report = refine_with_frontier(first, &tolerance(), || {
                Some(enclosure("frontier", Some(0), Some(0)))
            });
            assert_eq!(report.method, "frontier");
            assert_eq!(report.bound, Some(BigRational::from_integer(0.into())));
        }
        let report = refine_with_frontier(
            enclosure("structured", Some(2), Some(0)),
            &tolerance(),
            || None,
        );
        assert_eq!(report.method, "structured");
        assert_eq!(report.bound, Some(BigRational::from_integer(2.into())));
    }

    #[test]
    fn inconclusive_refinement_keeps_the_best_of_both_bounds() {
        let report = refine_with_frontier(
            enclosure("structured", Some(4), Some(1)),
            &BigRational::from_integer(2.into()),
            || Some(enclosure("frontier", Some(3), Some(0))),
        );
        assert_eq!(report.method, "structured+frontier");
        assert_eq!(report.bound, Some(BigRational::from_integer(3.into())));
        assert_eq!(
            report.lower_bound,
            Some(BigRational::from_integer(1.into()))
        );
    }
    #[test]
    fn exact_trace_distance_lower_is_positive_only_for_valid_mismatches() {
        let r = |n: i64, d: i64| BigRational::new(n.into(), d.into());
        for (norm, lower) in [
            (r(0i64, 1i64), r(2, 1)),
            (r(1, 16), r(15, 8)),
            (r(1, 4), r(3, 2)),
            (r(1, 1), r(0, 1)),
        ] {
            let bound = exact_trace_distance_lower(&norm).unwrap();
            assert_eq!(bound, lower);
            // Squaring checks the lower enclosure against 2 sqrt(1-r).
            assert!(&bound * &bound <= r(4, 1) * (r(1, 1) - norm));
        }
        assert!(exact_trace_distance_lower(&r(-1, 1)).is_none());
        assert!(exact_trace_distance_lower(&r(2, 1)).is_none());
    }
    #[test]
    fn distance_certificates_enclose_exact_rationals_across_precisions() {
        let one = BigRational::from_integer(1.into());
        for precision in [256, 513, 1024] {
            let domain = super::super::numeric::Enclosure { precision };
            for r in [
                BigRational::new(1.into(), 3.into()),
                &one - BigRational::new(1.into(), BigInt::from(3) << 60usize),
                &one - BigRational::new(1.into(), BigInt::from(7) << 300usize),
                one.clone(),
            ] {
                let trace = Complex::real(domain.scalar(&Scalar::rational(r.clone())).unwrap());
                let (upper, lower) = trace_bounds(&trace, 2).unwrap();
                assert!(&lower * &lower <= (&one - &r * &r) * BigInt::from(4));
                let expected =
                    ((&one - r) * BigInt::from(32)).min(BigRational::from_integer(4.into()));
                assert!(&upper * &upper >= expected);
            }
        }
    }
    fn run(body: &str) -> Report {
        let p = openqasm3::parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; {body}"),
            "test",
        )
        .unwrap();
        identity_bound(&p)
    }
    fn tolerance() -> BigRational {
        BigRational::new(1.into(), 1_000_000_000_000i64.into())
    }
    #[test]
    fn arbitrary_rotation_inverse_cancels() {
        let r = run("rx(0.123456789) q[0]; rx(-0.123456789) q[0];");
        assert!(r.bound.as_ref().is_some_and(|b| b < &tolerance()), "{r:?}");
        assert_eq!(r.lower_bound.unwrap(), BigRational::from_integer(0.into()));
    }
    #[test]
    fn phase_and_amplitude_differences_have_positive_lower_bounds() {
        for body in ["x q[0];", "z q[0];", "cz q[0],q[1];", "rx(0.123) q[0];"] {
            let r = run(body);
            assert!(
                r.lower_bound.as_ref().is_some_and(|b| b > &tolerance()),
                "{r:?}"
            );
            assert!(r.lower_bound.as_ref().unwrap() <= r.bound.as_ref().unwrap());
        }
    }
    #[test]
    fn global_phase_and_destructive_interference_are_not_neq() {
        for body in [
            "rx(2*pi) q[0];",
            "h q[0]; h q[0];",
            "p(0.123) q[0]; p(-0.123) q[0];",
        ] {
            let r = run(body);
            assert_eq!(
                r.lower_bound.as_ref(),
                Some(&BigRational::from_integer(0.into())),
                "{body}: {r:?}"
            );
        }
    }
    #[test]
    fn lower_bound_subtracts_preprocessing_error() {
        let r = run("rx(1e-8) q[0];");
        let zero = BigRational::from_integer(0.into());
        let lower = r.lower_bound.as_ref().unwrap();
        assert!(lower > &tolerance());
        assert_eq!(r.corrected_lower_bound(lower), Some(zero.clone()));
        assert_eq!(
            r.corrected_lower_bound(&(lower * BigInt::from(2))),
            Some(zero.clone())
        );
        assert_eq!(
            r.corrected_lower_bound(&(lower / BigInt::from(2))),
            Some(lower / BigInt::from(2))
        );
        assert!(
            r.corrected_lower_bound(&BigRational::from_integer((-1).into()))
                .is_none()
        );
        assert!(
            run("bit c; c=measure q[0];")
                .corrected_lower_bound(&zero)
                .is_none()
        );
    }
    #[test]
    fn inconclusive_trace_enclosure_does_not_prove_neq() {
        let trace = Complex::real(Interval {
            lo: Float::with_val(PREC, 0),
            hi: Float::with_val(PREC, 1),
        });
        assert_eq!(
            trace_distance_lower(&trace),
            Some(BigRational::from_integer(0.into()))
        );
        assert_eq!(
            trace_distance_lower(&Complex::n(0)),
            Some(BigRational::from_integer(2.into()))
        );
        assert_eq!(
            trace_distance_lower(&Complex {
                re: Interval::n(0),
                im: Interval::n(1)
            }),
            Some(BigRational::from_integer(0.into()))
        );
    }
    #[test]
    fn noncommuting_inverse_sequence_and_global_phase() {
        let r =
            run("rx(0.123) q[0]; ry(0.456) q[0]; ry(-0.456) q[0]; rx(-0.123) q[0]; rx(2*pi) q[1];");
        assert!(r.bound.as_ref().is_some_and(|b| b < &tolerance()), "{r:?}");
        let wrong = run("rx(0.123) q[0]; ry(0.456) q[0]; rx(-0.123) q[0]; ry(-0.456) q[0];");
        assert!(wrong.bound.unwrap() > tolerance());
    }
    #[test]
    fn phase_is_not_ignored() {
        let r = run("p(0.25) q[0];");
        assert!(r.bound.unwrap() > tolerance());
    }
    #[test]
    fn small_scalar_and_phase_residuals_are_bounded() {
        for body in ["rx(1e-15) q[0];", "p(1e-15) q[0];"] {
            let r = run(body);
            assert!(r.bound.as_ref().is_some_and(|b| b < &tolerance()), "{r:?}");
        }
    }
    #[test]
    fn entangled_inputs_are_not_replaced_with_basis_samples() {
        let r = run("cz q[0],q[1];");
        assert!(r.bound.unwrap() > tolerance());
    }
    #[test]
    fn measurements_refuse() {
        assert!(run("bit c; c=measure q[0];").bound.is_none());
    }
    #[test]
    fn trig_encloses_interior_extrema() {
        let i = Interval {
            lo: Float::with_val(PREC, 0),
            hi: Float::with_val(PREC, 4),
        };
        let s = i.trig(true);
        assert!(s.lo <= -0.75 && s.hi >= 1);
    }
    #[test]
    fn interval_multiplication_and_zero_crossing() {
        let i = Interval {
            lo: Float::with_val(PREC, -2),
            hi: Float::with_val(PREC, 3),
        };
        let s = i.square();
        assert_eq!(s.lo, 0);
        assert_eq!(s.hi, 9);
        assert!(Interval::n(1).div(&i).is_none());
    }
}
