use super::*;
use crate::equivalence::kernel::KernelBooleanPolynomial;
use crate::ir::{AstIdGenerator, NumericConstant, NumericExpr, NumericExprKind, SymbolId};

fn q(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}
fn r(n: i64, d: i64) -> KernelScalar {
    KernelScalar::Rational(q(n, d))
}
fn eval(s: &KernelScalar) -> Cyclotomic {
    lower(s, &mut Budget::new(2_000_000)).unwrap()
}
fn angle(n: i64, d: i64) -> NumericExpr {
    let mut ids = AstIdGenerator::default();
    let factor = ids.node(NumericExprKind::Rational(q(n, d)));
    let pi = ids.node(NumericExprKind::Constant(NumericConstant::Pi));
    ids.node(NumericExprKind::Mul(Box::new(factor), Box::new(pi)))
}

#[test]
fn rational_arithmetic_and_signed_inverse_are_exact() {
    let expr = KernelScalar::Add(
        Box::new(KernelScalar::Neg(Box::new(r(1, 2)))),
        Box::new(KernelScalar::Mul(
            Box::new(r(3, 4)),
            Box::new(KernelScalar::Inverse(Box::new(r(-2, 1)))),
        )),
    );
    assert_eq!(eval(&expr), eval(&r(-7, 8)));
    assert!(
        lower(
            &KernelScalar::Inverse(Box::new(r(0, 1))),
            &mut Budget::new(100)
        )
        .is_none()
    );
    assert!(
        lower(
            &KernelScalar::Inverse(Box::new(KernelScalar::Add(
                Box::new(r(1, 1)),
                Box::new(r(1, 1))
            ))),
            &mut Budget::new(100)
        )
        .is_none()
    );
}

#[test]
fn square_roots_are_positive_and_exact_or_refused() {
    assert_eq!(eval(&KernelScalar::Sqrt(Box::new(r(9, 4)))), eval(&r(3, 2)));
    let root = eval(&KernelScalar::Sqrt(Box::new(r(1, 2))));
    let expected = Cyclotomic::from_terms(
        [(ORDER / 8, q(1, 2)), (3 * ORDER / 8, q(-1, 2))],
        &mut Budget::new(100),
    )
    .unwrap();
    assert_eq!(root, expected);
    assert_eq!(
        root.multiply(&root, &mut Budget::new(100)).unwrap(),
        eval(&r(1, 2))
    );
    for n in [-1, 3, 5] {
        assert!(
            lower(
                &KernelScalar::Sqrt(Box::new(r(n, 1))),
                &mut Budget::new(100)
            )
            .is_none()
        );
    }
}

#[test]
fn exact_trigonometric_values_preserve_signs() {
    let half_root = eval(&KernelScalar::Sqrt(Box::new(r(1, 2))));
    assert_eq!(eval(&KernelScalar::Sin(angle(1, 4))), half_root);
    assert_eq!(eval(&KernelScalar::Cos(angle(1, 4))), half_root);
    assert_eq!(
        eval(&KernelScalar::Sin(angle(-1, 4))),
        half_root
            .multiply(&eval(&r(-1, 1)), &mut Budget::new(100))
            .unwrap()
    );
    assert_eq!(eval(&KernelScalar::Sin(angle(1, 6))), eval(&r(1, 2)));
    assert_eq!(eval(&KernelScalar::Cos(angle(1, 3))), eval(&r(1, 2)));
    assert!(lower(&KernelScalar::Sin(angle(1, 3)), &mut Budget::new(1000)).is_none());
}

#[test]
fn dyadic_sine_and_cosine_satisfy_exact_identities() {
    for n in -16..=16 {
        let s = eval(&KernelScalar::Sin(angle(n, 8)));
        let c = eval(&KernelScalar::Cos(angle(n, 8)));
        let mut budget = Budget::new(10000);
        assert!(
            s.multiply(&s, &mut budget)
                .unwrap()
                .add(&c.multiply(&c, &mut budget).unwrap(), &mut budget)
                .unwrap()
                .is_one()
        );
        assert_eq!(s, eval(&KernelScalar::Cos(angle(4 - n, 8))));
        assert_eq!(c, eval(&KernelScalar::Cos(angle(-n, 8))));
    }
}

#[test]
fn unsupported_or_invalid_inputs_cannot_hide_behind_zero() {
    let mut ids = AstIdGenerator::default();
    let input = ids.node(NumericExprKind::Input(SymbolId(0)));
    let one = ids.node(NumericExprKind::Rational(q(1, 1)));
    let zero = ids.node(NumericExprKind::Rational(q(0, 1)));
    let invalid = ids.node(NumericExprKind::Div(Box::new(one), Box::new(zero)));
    for bad in [
        KernelScalar::Sin(input),
        KernelScalar::Cos(invalid),
        KernelScalar::Sin(angle(1, 7)),
        KernelScalar::Inverse(Box::new(r(0, 1))),
        KernelScalar::Select {
            condition: KernelBooleanPolynomial::zero(),
            when_true: Box::new(r(1, 1)),
            when_false: Box::new(r(2, 1)),
        },
    ] {
        assert!(lower(&bad, &mut Budget::new(10000)).is_none());
        assert!(
            lower(
                &KernelScalar::Mul(Box::new(r(0, 1)), Box::new(bad)),
                &mut Budget::new(10000)
            )
            .is_none()
        );
    }
}

#[test]
fn resource_refusal_preserves_the_source() {
    let original = KernelScalar::Sin(angle(1, 4));
    let saved = original.clone();
    assert!(lower(&original, &mut Budget::new(1)).is_none());
    assert_eq!(original, saved);
    let mut deep = r(1, 1);
    for _ in 0..64 {
        deep = KernelScalar::Neg(Box::new(deep));
    }
    assert!(lower(&deep, &mut Budget::new(10000)).is_none());
    let huge = KernelScalar::Rational(BigRational::from_integer(BigInt::from(1) << 4096));
    assert!(lower(&huge, &mut Budget::new(10000)).is_none());
}
