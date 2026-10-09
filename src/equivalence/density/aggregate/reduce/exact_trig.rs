//! Exact sin/cos constants at multiples of pi/6, retaining signs and roots.
//! This is scalar normalization, not a larger phase/witness value field.

use crate::equivalence::density::aggregate::KernelScalar;
use crate::equivalence::density::aggregate::scalar::{
    integer, normalize_product, normalize_scalar, ratio,
};
use crate::ir::{NumericExpr, NumericExprKind};
use crate::symbolic::PhaseCoefficient;

/// Conservative well-defined constant-expression entrance. Division is admitted
/// only by a nonzero rational literal; numeric inputs and larger trees refuse.
/// Refusal leaves the original scalar expression unchanged.
pub(in crate::equivalence::density::aggregate) fn admitted(
    angle: &NumericExpr,
    nodes: &mut usize,
) -> bool {
    let Some(remaining) = nodes.checked_sub(1) else {
        return false;
    };
    *nodes = remaining;
    match &angle.kind {
        NumericExprKind::Rational(r) => r.numer().bits() <= 4096 && r.denom().bits() <= 4096,
        NumericExprKind::Constant(_) => true,
        NumericExprKind::Input(_) => false,
        NumericExprKind::Neg(a) => admitted(a, nodes),
        NumericExprKind::Add(a, b) | NumericExprKind::Sub(a, b) | NumericExprKind::Mul(a, b) => {
            admitted(a, nodes) && admitted(b, nodes)
        }
        NumericExprKind::Div(a, b) => {
            matches!(&b.kind, NumericExprKind::Rational(r) if r != &integer(0))
                && admitted(a, nodes)
                && admitted(b, nodes)
        }
    }
}

pub(in crate::equivalence::density::aggregate) fn normalize(
    angle: &NumericExpr,
    sine: bool,
) -> Option<KernelScalar> {
    if !admitted(angle, &mut 64) {
        return None;
    }
    // The existing exact angle algebra gives a rational only if all radian,
    // Euler and other symbolic atoms have cancelled. No numeric approximation.
    let twelfths = PhaseCoefficient::angle(angle.clone(), integer(1)).as_rational()? * integer(12);
    if !twelfths.is_integer() {
        return None;
    }
    let index = usize::try_from(twelfths.to_integer()).ok()?;
    // cos(theta)=sin(theta+pi/2); rational turns already lie in [0,1).
    let index = (index + if sine { 0 } else { 3 }) % 12;
    let (magnitude, negative) = match index {
        0 | 6 => (KernelScalar::Rational(integer(0)), false),
        1 | 5 | 7 | 11 => (KernelScalar::Rational(ratio(1, 2)), index >= 6),
        3 | 9 => (KernelScalar::Rational(integer(1)), index >= 6),
        2 | 4 | 8 | 10 => (
            normalize_product(vec![
                KernelScalar::Rational(ratio(1, 2)),
                KernelScalar::Sqrt(Box::new(KernelScalar::Rational(integer(3)))),
            ]),
            index >= 6,
        ),
        _ => unreachable!(),
    };
    Some(if negative {
        normalize_scalar(KernelScalar::Neg(Box::new(magnitude)))
    } else {
        magnitude
    })
}
