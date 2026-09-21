use super::*;
use crate::equivalence::kernel::{KernelBooleanPolynomial, KernelVariable};

// Independent rational evaluation for finite, well-defined test expressions.
// Square roots in these cases are exact rational squares under each assignment.
fn evaluate(value: &KernelScalar, input: bool) -> BigRational {
    match value {
        KernelScalar::Rational(r) => r.clone(),
        KernelScalar::Add(a, b) => evaluate(a, input) + evaluate(b, input),
        KernelScalar::Mul(a, b) => evaluate(a, input) * evaluate(b, input),
        KernelScalar::Neg(a) => -evaluate(a, input),
        KernelScalar::Inverse(a) => {
            let r = evaluate(a, input);
            assert_ne!(r, integer(0));
            r.recip()
        }
        KernelScalar::Sqrt(a) => {
            let r = evaluate(a, input);
            assert!(r >= integer(0));
            let n = r.numer().sqrt();
            let d = r.denom().sqrt();
            assert_eq!(&n * &n, *r.numer());
            assert_eq!(&d * &d, *r.denom());
            BigRational::new(n, d)
        }
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => {
            let select = condition
                .as_graph()
                .evaluate::<std::convert::Infallible>(|v| {
                    assert_eq!(
                        KernelVariable::from_graph_variable(v),
                        KernelVariable::InputKet(0)
                    );
                    Ok(input)
                })
                .unwrap();
            evaluate(if select { when_true } else { when_false }, input)
        }
        _ => panic!("unsupported test expression"),
    }
}

fn assert_preserves_value(value: KernelScalar) {
    let normalized = normalize_scalar(value.clone());
    for input in [false, true] {
        assert_eq!(evaluate(&value, input), evaluate(&normalized, input));
    }
}

#[test]
fn normalization_preserves_signed_products_sums_and_selected_values() {
    for a in -4..=4 {
        for b in -4..=4 {
            let selected = KernelScalar::Select {
                condition: KernelBooleanPolynomial::variable(KernelVariable::InputKet(0)),
                when_true: Box::new(rational(a)),
                when_false: Box::new(rational(b)),
            };
            assert_preserves_value(add(
                multiply(rational(2), selected.clone()),
                add(multiply(selected.clone(), rational(-3)), selected.clone()),
            ));
            assert_preserves_value(multiply(
                add(selected.clone(), rational(2)),
                add(rational(-3), selected.clone()),
            ));
            let square = multiply(selected.clone(), selected);
            let root = KernelScalar::Sqrt(Box::new(square));
            assert_preserves_value(multiply(root.clone(), root));
        }
    }
}

#[test]
fn rational_root_normalization_preserves_negative_signs_and_reciprocals() {
    for sign in [-3, -1, 1, 3] {
        for n in 1..=5 {
            let root = sqrt_ratio(n * n, 4);
            assert_preserves_value(multiply(rational(sign), root.clone()));
            assert_preserves_value(KernelScalar::Inverse(Box::new(root)));
        }
    }
}

#[test]
fn inverse_and_root_without_required_domain_facts_are_left_symbolic() {
    let zero_inverse = KernelScalar::Inverse(Box::new(rational(0)));
    assert_eq!(normalize_scalar(zero_inverse.clone()), zero_inverse);
    let negative_root = sqrt_ratio(-1, 1);
    assert_eq!(normalize_scalar(negative_root.clone()), negative_root);
    let unknown = KernelScalar::Select {
        condition: KernelBooleanPolynomial::variable(KernelVariable::InputKet(0)),
        when_true: Box::new(rational(-1)),
        when_false: Box::new(rational(1)),
    };
    assert!(!scalar_is_provably_nonnegative(&unknown));
}

fn rational(value: i64) -> KernelScalar {
    KernelScalar::Rational(integer(value))
}

fn sqrt_ratio(numerator: i64, denominator: i64) -> KernelScalar {
    KernelScalar::Sqrt(Box::new(KernelScalar::Rational(ratio(
        numerator,
        denominator,
    ))))
}

fn add(left: KernelScalar, right: KernelScalar) -> KernelScalar {
    KernelScalar::Add(Box::new(left), Box::new(right))
}

fn multiply(left: KernelScalar, right: KernelScalar) -> KernelScalar {
    KernelScalar::Mul(Box::new(left), Box::new(right))
}

#[test]
fn scalar_product_normal_form_is_associative_and_commutative() {
    let a = sqrt_ratio(2, 1);
    let b = KernelScalar::Inverse(Box::new(sqrt_ratio(3, 1)));
    let left = multiply(multiply(rational(-2), a.clone()), b.clone());
    let reordered = multiply(b, multiply(a, rational(-2)));

    assert_eq!(normalize_scalar(left), normalize_scalar(reordered));
}

#[test]
fn scalar_sum_normal_form_is_associative_commutative_and_cancels() {
    let atom = KernelScalar::Inverse(Box::new(sqrt_ratio(2, 1)));
    let left = add(
        add(atom.clone(), rational(3)),
        KernelScalar::Neg(Box::new(atom.clone())),
    );
    let reordered = add(
        rational(3),
        add(KernelScalar::Neg(Box::new(atom.clone())), atom),
    );

    assert_eq!(normalize_scalar(left), rational(3));
    assert_eq!(normalize_scalar(reordered), rational(3));
}

#[test]
fn scalar_rational_radicals_are_combined_exactly() {
    assert_eq!(
        normalize_scalar(multiply(sqrt_ratio(2, 1), sqrt_ratio(8, 1))),
        rational(4)
    );

    // This is the nested density-weight shape that occurs in
    // sqbricks-owm-vs-tele-0002: 2 * sqrt(1/2) / sqrt(2) = 1.
    let nested = multiply(
        rational(2),
        multiply(
            sqrt_ratio(1, 2),
            KernelScalar::Inverse(Box::new(sqrt_ratio(2, 1))),
        ),
    );
    assert_eq!(normalize_scalar(nested), rational(1));
}

#[test]
fn scalar_does_not_cancel_an_unproved_inverse() {
    let atom = KernelScalar::Select {
        condition: KernelBooleanPolynomial::variable(KernelVariable::InputKet(0)),
        when_true: Box::new(rational(0)),
        when_false: Box::new(rational(1)),
    };
    let value = multiply(atom.clone(), KernelScalar::Inverse(Box::new(atom)));

    assert!(!matches!(
        normalize_scalar(value),
        KernelScalar::Rational(value) if value == integer(1)
    ));
}

#[test]
fn scalar_select_reduces_only_decided_or_equal_branches() {
    let condition = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
    let equal = KernelScalar::Select {
        condition: condition.clone(),
        when_true: Box::new(rational(7)),
        when_false: Box::new(rational(7)),
    };
    let false_condition = KernelScalar::Select {
        condition: KernelBooleanPolynomial::zero(),
        when_true: Box::new(rational(7)),
        when_false: Box::new(rational(9)),
    };
    let unresolved = KernelScalar::Select {
        condition,
        when_true: Box::new(rational(7)),
        when_false: Box::new(rational(9)),
    };

    assert_eq!(normalize_scalar(equal), rational(7));
    assert_eq!(normalize_scalar(false_condition), rational(9));
    assert!(matches!(
        normalize_scalar(unresolved),
        KernelScalar::Select { .. }
    ));
}
