//! Directed MPFR arithmetic. Decimal literals stay exact rationals; pi is
//! enclosed, never replaced by an unaccounted binary64 approximation.
use super::*;
use crate::ir::NumericExpr;
use num_bigint::BigInt;
use rug::{
    Float, Integer,
    float::{Constant, Round},
};
const PREC: u32 = 256;
#[derive(Clone)]
struct Interval {
    lo: Float,
    hi: Float,
}
impl Interval {
    fn integer(n: &BigInt) -> Option<Self> {
        let n = Integer::from_str_radix(&n.to_string(), 10).ok()?;
        Some(Self {
            lo: Float::with_val_round(PREC, &n, Round::Down).0,
            hi: Float::with_val_round(PREC, &n, Round::Up).0,
        })
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
        let inv = Self {
            lo: Float::with_val_round(PREC, &one / &b.hi, Round::Down).0,
            hi: Float::with_val_round(PREC, &one / &b.lo, Round::Up).0,
        };
        Some(self.mul(&inv))
    }
    fn finite(self) -> Option<Self> {
        (self.lo.is_finite() && self.hi.is_finite()).then_some(self)
    }
}
fn evaluate(e: &NumericExpr, depth: usize) -> Option<Interval> {
    if depth > 128 {
        return None;
    }
    let r = match &e.kind {
        NumericExprKind::Rational(r) => {
            Interval::integer(r.numer())?.div(&Interval::integer(r.denom())?)?
        }
        NumericExprKind::Constant(NumericConstant::Pi) => Interval::pi(),
        NumericExprKind::Neg(a) => evaluate(a, depth + 1)?.neg(),
        NumericExprKind::Add(a, b) => evaluate(a, depth + 1)?.add(&evaluate(b, depth + 1)?),
        NumericExprKind::Sub(a, b) => evaluate(a, depth + 1)?.add(&evaluate(b, depth + 1)?.neg()),
        NumericExprKind::Mul(a, b) => evaluate(a, depth + 1)?.mul(&evaluate(b, depth + 1)?),
        NumericExprKind::Div(a, b) => evaluate(a, depth + 1)?.div(&evaluate(b, depth + 1)?)?,
        _ => return None,
    };
    r.finite()
}
fn radians(op: &Op) -> Option<Interval> {
    let StatementKind::Apply { parameters, .. } = &op.statement.kind else {
        return None;
    };
    if let Some(p) = parameters.first() {
        return evaluate(p, 0);
    }
    let turns = op.angle.as_ref()?.as_rational()?;
    Interval::integer(&(turns.numer() * 2))?
        .mul(&Interval::pi())
        .div(&Interval::integer(turns.denom())?)
}
/// Conservative diamond distance for replacing the pair by identity.
/// ||U(theta+d)-U(theta)|| <= |d|/2 for R*, <= |d| for P/CP;
/// the induced channel diamond distance is at most twice that norm.
pub(super) fn pair_error(a: &Op, b: &Op) -> Option<BigRational> {
    block_error(&[a, b])
}

/// Accumulate angles before applying a period shift. In particular, three
/// mixed pi/rational angles may cancel even when no pair cancels. Directed
/// rounding encloses every addition; no rounded literal replaces the source.
pub(super) fn block_error(ops: &[&Op]) -> Option<BigRational> {
    let a = *ops.first()?;
    if ops
        .iter()
        .any(|b| a.family() != b.family() || a.wires != b.wires)
    {
        return None;
    }
    let phase = matches!(a.family(), Gate::P | Gate::Cp);
    if !phase
        && !matches!(
            a.family(),
            Gate::Rx | Gate::Ry | Gate::Rz | Gate::Crx | Gate::Cry | Gate::Crz
        )
    {
        return None;
    }
    let mut sum = radians(a)?;
    for b in &ops[1..] {
        sum = sum.add(&radians(b)?).finite()?;
    }
    let period = Interval::pi().mul(&Interval::integer(&BigInt::from(if phase {
        2
    } else {
        4
    }))?);
    // Any integer period shift is legal; nearest is only a proposal, and the
    // final directed residual enclosure is the certificate.
    let ratio = Float::with_val(PREC, &sum.lo / &period.lo);
    let k = ratio.to_integer_round(Round::Nearest)?.0;
    let k = BigInt::parse_bytes(k.to_string().as_bytes(), 10)?;
    let residual = sum
        .add(&period.mul(&Interval::integer(&k)?).neg())
        .finite()?;
    let upper = residual.lo.abs().max(&residual.hi.abs());
    let (n, exp) = upper.to_integer_exp()?;
    // Avoid pathological input exponents requiring enormous BigInts.
    if exp.unsigned_abs() > 16384 {
        return None;
    }
    let n = BigInt::parse_bytes(n.to_string().as_bytes(), 10)?;
    let mut bound = if exp >= 0 {
        BigRational::from_integer(n << (exp as usize))
    } else {
        BigRational::new(n, BigInt::from(1) << ((-exp) as usize))
    };
    if phase {
        bound *= BigInt::from(2);
    }
    Some(bound)
}
