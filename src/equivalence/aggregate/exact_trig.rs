//! Exact sin/cos constants at multiples of pi/6, retaining signs and roots.
//! This is scalar normalization, not a larger phase/witness value field.

use super::*;
use crate::ir::{NumericExpr, NumericExprKind};
use crate::symbolic::PhaseCoefficient;

/// Conservative well-defined constant-expression entrance. Division is admitted
/// only by a nonzero rational literal; numeric inputs and larger trees refuse.
/// Refusal leaves the original scalar expression unchanged.
pub(super) fn admitted(angle: &NumericExpr, nodes: &mut usize) -> bool {
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

pub(super) fn normalize(angle: &NumericExpr, sine: bool) -> Option<KernelScalar> {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{AstIdGenerator, NumericConstant, SymbolId};

    fn angle(numerator: i64, denominator: i64) -> NumericExpr {
        let mut ids = AstIdGenerator::default();
        let pi = ids.node(NumericExprKind::Constant(NumericConstant::Pi));
        let scale = ids.node(NumericExprKind::Rational(ratio(numerator, denominator)));
        ids.node(NumericExprKind::Mul(Box::new(pi), Box::new(scale)))
    }

    // Interpret returned scalars as a+b*sqrt(3), independently of production
    // scalar normalization. Both real embeddings remain algebraically exact;
    // sqrt(3) denotes the positive root in the trigonometric table.
    fn quadratic(value: &KernelScalar) -> (BigRational, BigRational) {
        match value {
            KernelScalar::Rational(r) => (r.clone(), integer(0)),
            KernelScalar::Sqrt(v) if **v == KernelScalar::Rational(integer(3)) => {
                (integer(0), integer(1))
            }
            KernelScalar::Sqrt(v) if **v == KernelScalar::Rational(ratio(3, 4)) => {
                (integer(0), ratio(1, 2))
            }
            KernelScalar::Mul(a, b) => {
                let (a, b) = (quadratic(a), quadratic(b));
                (
                    &a.0 * &b.0 + integer(3) * &a.1 * &b.1,
                    &a.0 * &b.1 + &a.1 * &b.0,
                )
            }
            KernelScalar::Neg(a) => {
                let (a, b) = quadratic(a);
                (-a, -b)
            }
            _ => panic!("unexpected exact trigonometric scalar: {value:?}"),
        }
    }

    #[test]
    fn all_signed_twelfth_turn_values_match_independent_quadratic_recurrence() {
        // Multiply repeatedly by sqrt(3)/2+i/2, starting from 1.
        let mut cos = (integer(1), integer(0));
        let mut sin = (integer(0), integer(0));
        let mut expected = Vec::new();
        for _ in 0..12 {
            expected.push((sin.clone(), cos.clone()));
            let next_cos = (
                integer(3) * &cos.1 / integer(2) - &sin.0 / integer(2),
                &cos.0 / integer(2) - &sin.1 / integer(2),
            );
            let next_sin = (
                &cos.0 / integer(2) + integer(3) * &sin.1 / integer(2),
                &cos.1 / integer(2) + &sin.0 / integer(2),
            );
            cos = next_cos;
            sin = next_sin;
        }
        assert_eq!(cos, (integer(1), integer(0)));
        assert_eq!(sin, (integer(0), integer(0)));
        for n in -36i64..=36 {
            let angle = angle(n, 6);
            let s = normalize(&angle, true).unwrap();
            let c = normalize(&angle, false).unwrap();
            assert_eq!(
                (quadratic(&s), quadratic(&c)),
                expected[n.rem_euclid(12) as usize]
            );
            assert_eq!(
                normalize_scalar(KernelScalar::Add(
                    Box::new(s.clone().multiply(s)),
                    Box::new(c.clone().multiply(c))
                )),
                KernelScalar::Rational(integer(1))
            );
        }
    }

    #[test]
    fn trigonometric_refusal_preserves_unsupported_angles_and_undefined_divisors() {
        for a in [angle(1, 7), angle(1, 4)] {
            assert!(normalize(&a, true).is_none());
            assert_eq!(
                normalize_scalar(KernelScalar::Sin(a.clone())),
                KernelScalar::Sin(a)
            );
        }
        let mut ids = AstIdGenerator::default();
        let radian = ids.node(NumericExprKind::Rational(ratio(1, 2)));
        assert!(normalize(&radian, true).is_none());
        let input = ids.node(NumericExprKind::Input(SymbolId(0)));
        assert!(normalize(&input, true).is_none());
        let zero = ids.node(NumericExprKind::Rational(integer(0)));
        let invalid = ids.node(NumericExprKind::Div(
            Box::new(angle(1, 6)),
            Box::new(zero.clone()),
        ));
        let hidden = ids.node(NumericExprKind::Mul(
            Box::new(zero),
            Box::new(invalid.clone()),
        ));
        for a in [invalid, hidden] {
            assert!(normalize(&a, true).is_none());
        }
        let mut large = angle(1, 6);
        for _ in 0..64 {
            large = ids.node(NumericExprKind::Neg(Box::new(large)));
        }
        assert!(normalize(&large, true).is_none());
        let mut nodes = 0;
        assert!(!admitted(&angle(1, 6), &mut nodes));
    }
}
