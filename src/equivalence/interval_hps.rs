//! Structural HPS coefficient simplification with certified numerical leaves.
//!
//! No whole-function truth tables are constructed. Boolean expressions stay
//! shared while scalar coefficients and common factors are simplified. Every
//! path and input remains accounted for in the normalized trace. Boolean
//! guards/selectors stay exact; MPFR endpoints enclose all scalar/phase values.
//! For a d-dimensional unitary V and t=Tr(V)/d, choose its global phase so that
//! ||V-exp(i phi)I||_F^2=2d(1-|t|). The channel diamond distance is therefore
//! at most 2 sqrt(2d(1-|t|)). This intentionally conservative, dimension-aware
//! bound does not confuse average trace fidelity with worst-case equivalence.
//! A normalized maximally entangled input also gives a lower bound:
//! 2 sqrt(1-|t|^2). A strictly positive, error-corrected lower bound proves NEQ.
//! These are separate certificates; the exact `analyze` route is unchanged.
use crate::ir::{NumericConstant, NumericExpr, NumericExprKind, Program, unitary};
use crate::symbolic::{
    BooleanPolynomial, ExecutionConfig, OutputSelection, Scalar, Variable, execute,
    normalized_trace_component,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use rug::{
    Float, Integer,
    float::{Constant, Round},
};
use std::collections::{BTreeMap, BTreeSet};
use std::time::{Duration, Instant};

const PREC: u32 = 256;
mod structured;

#[derive(Clone, Debug)]
struct Interval {
    lo: Float,
    hi: Float,
}
impl Interval {
    fn n(n: i32) -> Self {
        Self {
            lo: Float::with_val(PREC, n),
            hi: Float::with_val(PREC, n),
        }
    }
    fn rational(r: &BigRational) -> Option<Self> {
        if r.numer().bits() > 16384 || r.denom().bits() > 16384 {
            return None;
        }
        let cv = |n: &BigInt| -> Option<Self> {
            let n = Integer::from_str_radix(&n.to_string(), 10).ok()?;
            Some(Self {
                lo: Float::with_val_round(PREC, &n, Round::Down).0,
                hi: Float::with_val_round(PREC, &n, Round::Up).0,
            })
        };
        cv(r.numer())?.div(&cv(r.denom())?)
    }
    fn pi() -> Self {
        Self {
            lo: Float::with_val_round(PREC, Constant::Pi, Round::Down).0,
            hi: Float::with_val_round(PREC, Constant::Pi, Round::Up).0,
        }
    }
    fn add(&self, b: &Self) -> Self {
        Self {
            lo: Float::with_val_round(PREC, &self.lo + &b.lo, Round::Down).0,
            hi: Float::with_val_round(PREC, &self.hi + &b.hi, Round::Up).0,
        }
    }
    fn neg(&self) -> Self {
        Self {
            lo: -self.hi.clone(),
            hi: -self.lo.clone(),
        }
    }
    fn mul(&self, b: &Self) -> Self {
        let mut lo = Float::with_val(PREC, f64::INFINITY);
        let mut hi = -lo.clone();
        for a in [&self.lo, &self.hi] {
            for b in [&b.lo, &b.hi] {
                let l = Float::with_val_round(PREC, a * b, Round::Down).0;
                let h = Float::with_val_round(PREC, a * b, Round::Up).0;
                if l < lo {
                    lo = l;
                }
                if h > hi {
                    hi = h;
                }
            }
        }
        Self { lo, hi }
    }
    fn div(&self, b: &Self) -> Option<Self> {
        if b.lo <= 0 && b.hi >= 0 {
            return None;
        }
        let one = Float::with_val(PREC, 1);
        Some(self.mul(&Self {
            lo: Float::with_val_round(PREC, &one / &b.hi, Round::Down).0,
            hi: Float::with_val_round(PREC, &one / &b.lo, Round::Up).0,
        }))
    }
    fn sqrt(&self) -> Option<Self> {
        if self.lo < 0 {
            return None;
        }
        let mut lo = self.lo.clone();
        lo.sqrt_round(Round::Down);
        let mut hi = self.hi.clone();
        hi.sqrt_round(Round::Up);
        Some(Self { lo, hi })
    }
    fn square(&self) -> Self {
        let mut r = self.mul(self);
        if self.lo <= 0 && self.hi >= 0 {
            r.lo = Float::with_val(PREC, 0);
        }
        r
    }
    fn trig(&self, sine: bool) -> Self {
        // sin/cos are globally 1-Lipschitz. Correctly rounded values at the
        // lower endpoint plus the interval width also enclose interior extrema.
        let mut lo = self.lo.clone();
        let mut hi = self.lo.clone();
        if sine {
            lo.sin_round(Round::Down);
            hi.sin_round(Round::Up);
        } else {
            lo.cos_round(Round::Down);
            hi.cos_round(Round::Up);
        }
        let width = Float::with_val_round(PREC, &self.hi - &self.lo, Round::Up).0;
        lo = Float::with_val_round(PREC, lo - &width, Round::Down).0;
        hi = Float::with_val_round(PREC, hi + &width, Round::Up).0;
        if lo < -1 {
            lo = Float::with_val(PREC, -1);
        }
        if hi > 1 {
            hi = Float::with_val(PREC, 1);
        }
        Self { lo, hi }
    }
    fn finite(self) -> Option<Self> {
        (self.lo.is_finite() && self.hi.is_finite() && self.lo <= self.hi).then_some(self)
    }
}
fn number(e: &NumericExpr, depth: usize) -> Option<Interval> {
    if depth > 256 {
        return None;
    }
    let r = match &e.kind {
        NumericExprKind::Rational(r) => Interval::rational(r)?,
        NumericExprKind::Constant(NumericConstant::Pi) => Interval::pi(),
        NumericExprKind::Constant(NumericConstant::Tau) => Interval::pi().mul(&Interval::n(2)),
        NumericExprKind::Neg(a) => number(a, depth + 1)?.neg(),
        NumericExprKind::Add(a, b) => number(a, depth + 1)?.add(&number(b, depth + 1)?),
        NumericExprKind::Sub(a, b) => number(a, depth + 1)?.add(&number(b, depth + 1)?.neg()),
        NumericExprKind::Mul(a, b) => number(a, depth + 1)?.mul(&number(b, depth + 1)?),
        NumericExprKind::Div(a, b) => number(a, depth + 1)?.div(&number(b, depth + 1)?)?,
        _ => return None,
    };
    r.finite()
}
#[derive(Clone)]
struct Complex {
    re: Interval,
    im: Interval,
}
impl Complex {
    fn real(re: Interval) -> Self {
        Self {
            re,
            im: Interval::n(0),
        }
    }
    fn n(n: i32) -> Self {
        Self::real(Interval::n(n))
    }
    fn add(&self, b: &Self) -> Self {
        Self {
            re: self.re.add(&b.re),
            im: self.im.add(&b.im),
        }
    }
    fn mul(&self, b: &Self) -> Self {
        Self {
            re: self.re.mul(&b.re).add(&self.im.mul(&b.im).neg()),
            im: self.re.mul(&b.im).add(&self.im.mul(&b.re)),
        }
    }
}
fn float_rational(v: &Float) -> Option<BigRational> {
    let (n, e) = v.to_integer_exp()?;
    if e.unsigned_abs() > 16384 {
        return None;
    }
    let n = BigInt::parse_bytes(n.to_string().as_bytes(), 10)?;
    Some(if e >= 0 {
        BigRational::from_integer(n << (e as usize))
    } else {
        BigRational::new(n, BigInt::from(1) << ((-e) as usize))
    })
}

/// Certified distance enclosure for a complete static unitary versus identity.
/// `bound` alone is never a NEQ witness. A positive `lower_bound` is, provided
/// any error incurred before this check has been subtracted first.
#[derive(Debug)]
pub struct Report {
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
    let mut gap = Float::with_val_round(
        PREC,
        Float::with_val(PREC, 1) - &norm_squared.hi,
        Round::Down,
    )
    .0;
    if gap <= 0 {
        return Some(BigRational::from_integer(0.into()));
    }
    gap.sqrt_round(Round::Down);
    let lower = Float::with_val_round(PREC, gap * 2, Round::Down).0;
    float_rational(&lower)
}
/// Checks a complete static unitary against identity, for all coherent inputs.
/// Measurements, reset, classical observation and runtime numeric inputs refuse.
pub fn identity_bound(program: &Program) -> Report {
    structured::identity_bound(program)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::openqasm3;
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
                r.lower_bound.unwrap(),
                BigRational::from_integer(0.into()),
                "{body}"
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
