use super::simplify_scalar;
use crate::symbolic::{
    BooleanPolynomial, Component, HybridMemory, HybridPathSum, PhasePolynomial, Scalar,
    ScalarBindings, Variable,
};
use num_rational::BigRational;

fn rational(n: i64, d: i64) -> Scalar {
    Scalar::rational(BigRational::new(n.into(), d.into()))
}

// Build raw products so the test exercises this pass, not constructor folding.
fn mul(a: Scalar, b: Scalar) -> Scalar {
    Scalar::Mul(Box::new(a), Box::new(b))
}

fn normalization_product() -> Scalar {
    let root = Scalar::sqrt(rational(1, 2));
    mul(
        rational(2, 1),
        mul(rational(2, 1), mul(rational(1, 2), mul(root.clone(), root))),
    )
}

#[test]
fn nested_normalization_factors_reduce_exactly() {
    assert_eq!(simplify_scalar(&normalization_product()), Scalar::one());
}

#[test]
fn nonnegative_rational_roots_combine_with_correct_sign() {
    for n in 0..8 {
        for d in 1..8 {
            let source = mul(
                Scalar::Neg(Box::new(Scalar::sqrt(rational(n, d)))),
                mul(rational(3, 2), Scalar::sqrt(rational(4 * n, d))),
            );
            // -sqrt(r) * (3/2) * sqrt(4r) = -3r for r >= 0.
            assert_eq!(simplify_scalar(&source), rational(-3 * n, d));
        }
    }
}

#[test]
fn symbolic_factors_keep_boolean_dependent_signs() {
    let condition = BooleanPolynomial::variable(Variable::Path(0));
    let factor = Scalar::select(condition, rational(-2, 1), rational(3, 1));
    let source = mul(factor, normalization_product());
    let reduced = simplify_scalar(&source);
    for (bit, expected) in [(false, 3), (true, -2)] {
        let mut bindings = ScalarBindings::default();
        bindings.booleans.insert(Variable::Path(0), bit);
        assert_eq!(source.evaluate(128, &bindings).unwrap(), expected);
        assert_eq!(reduced.evaluate(128, &bindings).unwrap(), expected);
    }
}

#[test]
fn square_root_of_symbolic_square_is_not_replaced_by_signed_value() {
    let x = Scalar::select(
        BooleanPolynomial::variable(Variable::Path(0)),
        rational(-2, 1),
        rational(3, 1),
    );
    let source = mul(Scalar::sqrt(mul(x.clone(), x)), rational(2, 1));
    let reduced = simplify_scalar(&source);
    for (bit, expected) in [(false, 6), (true, 4)] {
        let mut bindings = ScalarBindings::default();
        bindings.booleans.insert(Variable::Path(0), bit);
        assert_eq!(source.evaluate(128, &bindings).unwrap(), expected);
        assert_eq!(reduced.evaluate(128, &bindings).unwrap(), expected);
    }
}

#[test]
fn negative_radicands_are_not_combined_into_a_positive_root() {
    // Outside the real scalar domain: this pass must not turn two invalid
    // real roots into a valid positive constant by multiplying radicands.
    let source = mul(Scalar::sqrt(rational(-2, 1)), Scalar::sqrt(rational(-8, 1)));
    let reduced = simplify_scalar(&source);
    assert!(
        source
            .evaluate(128, &ScalarBindings::default())
            .unwrap()
            .is_nan()
    );
    assert!(
        reduced
            .evaluate(128, &ScalarBindings::default())
            .unwrap()
            .is_nan()
    );
}

#[test]
fn reordered_symbolic_products_share_a_normal_form() {
    let a = Scalar::select(
        BooleanPolynomial::variable(Variable::Path(0)),
        rational(-1, 1),
        rational(2, 1),
    );
    let b = Scalar::select(
        BooleanPolynomial::variable(Variable::Path(1)),
        rational(3, 1),
        rational(-4, 1),
    );
    let left = mul(a.clone(), mul(rational(-3, 2), b.clone()));
    let right = mul(b, mul(a, rational(-3, 2)));
    let reduced = simplify_scalar(&left);
    assert_eq!(reduced, simplify_scalar(&right));
    for bits in 0..4 {
        let mut bindings = ScalarBindings::default();
        for i in 0..2 {
            bindings
                .booleans
                .insert(Variable::Path(i), bits & (1 << i) != 0);
        }
        let expected = if bits & 1 != 0 { -1 } else { 2 } * if bits & 2 != 0 { 3 } else { -4 } * -3;
        assert_eq!(reduced.evaluate(128, &bindings).unwrap() * 2, expected);
    }
}

#[test]
fn hps_simplification_applies_scalar_normalization() {
    let hps = HybridPathSum {
        input: HybridMemory::default(),
        components: vec![Component {
            guard: Vec::new(),
            scalar: normalization_product(),
            path_support: Default::default(),
            phase: PhasePolynomial::zero(),
            output: HybridMemory::default(),
        }],
    };
    let reduced = super::simplify(hps);
    assert_eq!(reduced.components.len(), 1);
    assert_eq!(reduced.components[0].scalar, Scalar::one());
}
