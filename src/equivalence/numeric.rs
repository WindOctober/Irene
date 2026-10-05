//! Certified numerical interpretation of exact symbolic expressions.
//! Enclosures are values, never identities for interning expressions.
use crate::ir::{NumericConstant, NumericExpr, NumericExprKind};
use num_bigint::BigInt;
use num_rational::BigRational;
use rug::{
    Float, Integer,
    float::{Constant, Round},
};

pub(super) const PREC: u32 = 256;

#[derive(Clone, Debug)]
pub(super) struct Interval {
    pub(super) lo: Float,
    pub(super) hi: Float,
}
impl Interval {
    pub(super) fn integer(n: &BigInt) -> Option<Self> {
        Self::rational(&BigRational::from_integer(n.clone()))
    }
    pub(super) fn n(n: i32) -> Self {
        Self {
            lo: Float::with_val(PREC, n),
            hi: Float::with_val(PREC, n),
        }
    }
    pub(super) fn rational(r: &BigRational) -> Option<Self> {
        Self::rational_at(r, PREC)
    }
    fn rational_at(r: &BigRational, precision: u32) -> Option<Self> {
        if r.numer().bits() > 16384 || r.denom().bits() > 16384 {
            return None;
        }
        let cv = |n: &BigInt| -> Option<Self> {
            let n = Integer::from_str_radix(&n.to_string(), 10).ok()?;
            Some(Self {
                lo: Float::with_val_round(precision, &n, Round::Down).0,
                hi: Float::with_val_round(precision, &n, Round::Up).0,
            })
        };
        cv(r.numer())?.div(&cv(r.denom())?)
    }
    pub(super) fn pi() -> Self {
        Self::pi_at(PREC)
    }
    fn pi_at(precision: u32) -> Self {
        Self {
            lo: Float::with_val_round(precision, Constant::Pi, Round::Down).0,
            hi: Float::with_val_round(precision, Constant::Pi, Round::Up).0,
        }
    }
    pub(super) fn add(&self, b: &Self) -> Self {
        let precision = self
            .lo
            .prec()
            .max(self.hi.prec())
            .max(b.lo.prec())
            .max(b.hi.prec());
        Self {
            lo: Float::with_val_round(precision, &self.lo + &b.lo, Round::Down).0,
            hi: Float::with_val_round(precision, &self.hi + &b.hi, Round::Up).0,
        }
    }
    pub(super) fn neg(&self) -> Self {
        Self {
            lo: -self.hi.clone(),
            hi: -self.lo.clone(),
        }
    }
    pub(super) fn mul(&self, b: &Self) -> Self {
        let precision = self
            .lo
            .prec()
            .max(self.hi.prec())
            .max(b.lo.prec())
            .max(b.hi.prec());
        if self.is_zero() || b.is_zero() {
            return Self::n(0);
        }
        if self.lo == 1 && self.hi == 1 {
            return b.clone();
        }
        if b.lo == 1 && b.hi == 1 {
            return self.clone();
        }
        let mut lo = Float::with_val(precision, f64::INFINITY);
        let mut hi = -lo.clone();
        for a in [&self.lo, &self.hi] {
            for b in [&b.lo, &b.hi] {
                let l = Float::with_val_round(precision, a * b, Round::Down).0;
                let h = Float::with_val_round(precision, a * b, Round::Up).0;
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
    pub(super) fn div(&self, b: &Self) -> Option<Self> {
        let precision = self
            .lo
            .prec()
            .max(self.hi.prec())
            .max(b.lo.prec())
            .max(b.hi.prec());
        if b.lo <= 0 && b.hi >= 0 {
            return None;
        }
        let one = Float::with_val(precision, 1);
        Some(self.mul(&Self {
            lo: Float::with_val_round(precision, &one / &b.hi, Round::Down).0,
            hi: Float::with_val_round(precision, &one / &b.lo, Round::Up).0,
        }))
    }
    pub(super) fn sqrt(&self) -> Option<Self> {
        if self.lo < 0 {
            return None;
        }
        let mut lo = self.lo.clone();
        lo.sqrt_round(Round::Down);
        let mut hi = self.hi.clone();
        hi.sqrt_round(Round::Up);
        Some(Self { lo, hi })
    }
    pub(super) fn square(&self) -> Self {
        let mut r = self.mul(self);
        if self.lo <= 0 && self.hi >= 0 {
            r.lo = Float::with_val(PREC, 0);
        }
        r
    }
    pub(super) fn trig(&self, sine: bool) -> Self {
        let precision = self.lo.prec().max(self.hi.prec());
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
        let width = Float::with_val_round(precision, &self.hi - &self.lo, Round::Up).0;
        lo = Float::with_val_round(precision, &lo - &width, Round::Down).0;
        hi = Float::with_val_round(precision, &hi + &width, Round::Up).0;
        if lo < -1 {
            lo = Float::with_val(precision, -1);
        }
        if hi > 1 {
            hi = Float::with_val(precision, 1);
        }
        Self { lo, hi }
    }
    pub(super) fn finite(self) -> Option<Self> {
        (self.lo.is_finite() && self.hi.is_finite() && self.lo <= self.hi).then_some(self)
    }
    pub(super) fn is_zero(&self) -> bool {
        self.lo == 0 && self.hi == 0
    }
}
pub(super) fn number(e: &NumericExpr, depth: usize) -> Option<Interval> {
    number_at(e, depth, PREC)
}
fn number_at(e: &NumericExpr, depth: usize, precision: u32) -> Option<Interval> {
    if depth > 256 {
        return None;
    }
    let r = match &e.kind {
        NumericExprKind::Rational(r) => Interval::rational_at(r, precision)?,
        NumericExprKind::Constant(NumericConstant::Pi) => Interval::pi_at(precision),
        NumericExprKind::Constant(NumericConstant::Tau) => {
            Interval::pi_at(precision).mul(&Interval::n(2))
        }
        NumericExprKind::Neg(a) => number_at(a, depth + 1, precision)?.neg(),
        NumericExprKind::Add(a, b) => {
            number_at(a, depth + 1, precision)?.add(&number_at(b, depth + 1, precision)?)
        }
        NumericExprKind::Sub(a, b) => {
            number_at(a, depth + 1, precision)?.add(&number_at(b, depth + 1, precision)?.neg())
        }
        NumericExprKind::Mul(a, b) => {
            number_at(a, depth + 1, precision)?.mul(&number_at(b, depth + 1, precision)?)
        }
        NumericExprKind::Div(a, b) => {
            number_at(a, depth + 1, precision)?.div(&number_at(b, depth + 1, precision)?)?
        }
        _ => return None,
    };
    r.finite()
}
#[derive(Clone)]
pub(super) struct Complex {
    pub(super) re: Interval,
    pub(super) im: Interval,
}
impl Complex {
    pub(super) fn multiply_assign(&mut self, b: &Self) {
        // Exact roots of unity only; never recognize one by a tolerance.
        if b.im.is_zero() && b.re.lo == b.re.hi {
            if b.re.lo == 1 {
                return;
            }
            if b.re.lo == -1 {
                self.re = self.re.neg();
                self.im = self.im.neg();
                return;
            }
        }
        if b.re.is_zero() && b.im.lo == b.im.hi && (b.im.lo == 1 || b.im.lo == -1) {
            std::mem::swap(&mut self.re, &mut self.im);
            if b.im.lo == 1 {
                self.re = self.re.neg();
            } else {
                self.im = self.im.neg();
            }
            return;
        }
        *self = self.mul(b);
    }
    pub(super) fn is_zero(&self) -> bool {
        self.re.is_zero() && self.im.is_zero()
    }
    pub(super) fn real(re: Interval) -> Self {
        Self {
            re,
            im: Interval::n(0),
        }
    }
    pub(super) fn n(n: i32) -> Self {
        Self::real(Interval::n(n))
    }
    pub(super) fn add(&self, b: &Self) -> Self {
        if self.is_zero() {
            return b.clone();
        }
        if b.is_zero() {
            return self.clone();
        }
        Self {
            re: self.re.add(&b.re),
            im: self.im.add(&b.im),
        }
    }
    pub(super) fn mul(&self, b: &Self) -> Self {
        if self.is_zero() || b.is_zero() {
            return Self::n(0);
        }
        if self.im.is_zero() && self.re.lo == 1 && self.re.hi == 1 {
            return b.clone();
        }
        if b.im.is_zero() && b.re.lo == 1 && b.re.hi == 1 {
            return self.clone();
        }
        Self {
            re: self.re.mul(&b.re).add(&self.im.mul(&b.im).neg()),
            im: self.re.mul(&b.im).add(&self.im.mul(&b.re)),
        }
    }
}

/// Interpret a closed phase using the default precision.
pub(super) fn phase(a: &crate::symbolic::PhaseCoefficient) -> Option<Complex> {
    phase_at(a, PREC)
}
/// Evaluation policy is separate from the identity of symbolic expressions.
pub(super) struct Enclosure {
    pub precision: u32,
}
impl Enclosure {
    pub fn scalar(&self, s: &crate::symbolic::Scalar) -> Option<Interval> {
        scalar_at(s, 0, self.precision)
    }
    pub fn phase(&self, p: &crate::symbolic::PhaseCoefficient) -> Option<Complex> {
        phase_at(p, self.precision)
    }
}
fn scalar_at(s: &crate::symbolic::Scalar, depth: usize, precision: u32) -> Option<Interval> {
    use crate::symbolic::Scalar as S;
    if depth > 256 {
        return None;
    }
    let r = match s {
        S::Rational(r) => Interval::rational_at(r, precision)?,
        S::Sin(a) => number_at(a, 0, precision)?.trig(true),
        S::Cos(a) => number_at(a, 0, precision)?.trig(false),
        S::Sqrt(a) => scalar_at(a, depth + 1, precision)?.sqrt()?,
        S::Neg(a) => scalar_at(a, depth + 1, precision)?.neg(),
        S::Inverse(a) => Interval::n(1).div(&scalar_at(a, depth + 1, precision)?)?,
        S::Add(a, b) => {
            scalar_at(a, depth + 1, precision)?.add(&scalar_at(b, depth + 1, precision)?)
        }
        S::Mul(a, b) => {
            scalar_at(a, depth + 1, precision)?.mul(&scalar_at(b, depth + 1, precision)?)
        }
        S::Select {
            condition,
            when_true,
            when_false,
        } => {
            if condition.is_one() {
                scalar_at(when_true, depth + 1, precision)?
            } else if condition.is_zero() {
                scalar_at(when_false, depth + 1, precision)?
            } else {
                return None;
            }
        }
    };
    r.finite()
}

fn phase_at(a: &crate::symbolic::PhaseCoefficient, precision: u32) -> Option<Complex> {
    let (turns, radians) = a.constant_turns_radians()?;
    let quarters = &turns * BigInt::from(4);
    if radians == BigRational::from_integer(0.into()) && quarters.is_integer() {
        let k: i32 = (quarters.to_integer() % BigInt::from(4)).try_into().ok()?;
        return Some(match k.rem_euclid(4) {
            0 => Complex::n(1),
            2 => Complex::n(-1),
            k => Complex {
                re: Interval::n(0),
                im: Interval::n(if k == 1 { 1 } else { -1 }),
            },
        });
    }
    let angle = Interval::rational_at(&turns, precision)?
        .mul(&Interval::pi_at(precision))
        .mul(&Interval::n(2))
        .add(&Interval::rational_at(&radians, precision)?)
        .finite()?;
    Some(Complex {
        re: angle.trig(false),
        im: angle.trig(true),
    })
}
pub(super) fn float_rational(v: &Float) -> Option<BigRational> {
    // MPFR's zero has a sentinel exponent, not an enormous denominator.
    if v == &0 {
        return Some(BigRational::from_integer(0.into()));
    }
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
