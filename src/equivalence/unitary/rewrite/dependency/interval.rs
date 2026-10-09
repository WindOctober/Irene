//! Directed MPFR arithmetic. Decimal literals stay exact rationals; pi is
//! enclosed, never replaced by an unaccounted binary64 approximation.
use super::*;
use crate::equivalence::unitary::numeric::{Interval, PREC, float_rational, number as evaluate};
use num_bigint::BigInt;
use rug::{Float, float::Round};
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
    let mut bound = float_rational(&upper)?;
    if phase {
        bound *= BigInt::from(2);
    }
    Some(bound)
}
