use super::*;

fn q(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}
fn budget() -> Budget {
    Budget::new(2_000_000)
}
fn value(terms: &[(u64, i64)]) -> Cyclotomic {
    Cyclotomic::from_terms(terms.iter().map(|(p, r)| (*p, q(*r, 1))), &mut budget()).unwrap()
}

#[test]
fn signs_wrap_and_cancellation_are_exact() {
    assert!(value(&[(0, 1), (HALF, 1)]).is_zero());
    assert!(value(&[(ORDER, 1)]).is_one());
    assert_eq!(value(&[(ORDER - 1, 3)]), value(&[(HALF - 1, -3)]));
    assert_eq!(value(&[(u64::MAX, 2)]), value(&[(u64::MAX % ORDER, 2)]));
    let i = value(&[(ORDER / 4, 1)]);
    assert_eq!(i.multiply(&i, &mut budget()).unwrap(), value(&[(0, -1)]));
    assert!(i.norm_squared(&mut budget()).unwrap().is_one());
}

#[test]
fn phase_admission_never_rounds() {
    for (turns, exponent) in [
        (q(1, 8), ORDER / 8),
        (q(-1, 4), 3 * ORDER / 4),
        (q(3, 2), HALF),
    ] {
        assert_eq!(
            Cyclotomic::from_phase(&PhaseCoefficient::rational(turns), &mut budget()).unwrap(),
            value(&[(exponent, 1)])
        );
    }
    assert!(Cyclotomic::from_phase(&PhaseCoefficient::rational(q(1, 3)), &mut budget()).is_none());
    assert!(
        Cyclotomic::from_phase(
            &PhaseCoefficient::rational(BigRational::new(1.into(), BigInt::from(1) << 63)),
            &mut budget()
        )
        .is_none()
    );
}

#[test]
fn modulus_is_taken_after_coherent_addition() {
    let a = value(&[(0, 1)]);
    let b = value(&[(0, -1)]);
    assert!(
        a.add(&b, &mut budget())
            .unwrap()
            .norm_squared(&mut budget())
            .unwrap()
            .is_zero()
    );
    assert_eq!(
        a.norm_squared(&mut budget())
            .unwrap()
            .add(&b.norm_squared(&mut budget()).unwrap(), &mut budget())
            .unwrap(),
        value(&[(0, 2)])
    );
    let t = Cyclotomic::from_terms([(0, q(1, 2)), (ORDER / 8, q(1, 2))], &mut budget()).unwrap();
    let expected = Cyclotomic::from_terms(
        [
            (0, q(1, 2)),
            (ORDER / 8, q(1, 4)),
            (3 * ORDER / 8, q(-1, 4)),
        ],
        &mut budget(),
    )
    .unwrap();
    let norm = t.norm_squared(&mut budget()).unwrap();
    assert_eq!(norm, expected);
    assert!(!norm.is_one());
}

// Independent dense Q(zeta_16) oracle: ordinary polynomial convolution,
// reduced by x^8 + 1. No production normalization is used by this oracle.
fn dense_product(a: &[BigRational; 8], b: &[BigRational; 8]) -> [BigRational; 8] {
    let mut out = std::array::from_fn(|_| q(0, 1));
    for i in 0..8 {
        for j in 0..8 {
            let product = &a[i] * &b[j];
            out[(i + j) % 8] += if i + j >= 8 { -product } else { product };
        }
    }
    out
}
fn sparse(a: &[BigRational; 8]) -> Cyclotomic {
    Cyclotomic::from_terms(
        a.iter()
            .enumerate()
            .map(|(i, r)| (i as u64 * (ORDER / 16), r.clone())),
        &mut budget(),
    )
    .unwrap()
}

#[test]
fn generated_arithmetic_matches_independent_dense_polynomials() {
    for seed in 0..32 {
        let a = std::array::from_fn(|i| q((seed + 3 * i) as i64 % 7 - 3, (i % 3 + 1) as i64));
        let b = std::array::from_fn(|i| q((2 * seed + i) as i64 % 5 - 2, (i % 2 + 1) as i64));
        let x = sparse(&a);
        let y = sparse(&b);
        assert_eq!(
            x.multiply(&y, &mut budget()).unwrap(),
            sparse(&dense_product(&a, &b))
        );
        let sum = std::array::from_fn(|i| &a[i] + &b[i]);
        assert_eq!(x.add(&y, &mut budget()).unwrap(), sparse(&sum));
        let mut conjugate = std::array::from_fn(|_| q(0, 1));
        conjugate[0] = a[0].clone();
        for i in 1..8 {
            conjugate[8 - i] = -a[i].clone();
        }
        assert_eq!(x.conjugate(&mut budget()).unwrap(), sparse(&conjugate));
        assert_eq!(
            x.norm_squared(&mut budget()).unwrap(),
            sparse(&dense_product(&a, &conjugate))
        );
        assert_eq!(
            x.conjugate(&mut budget())
                .unwrap()
                .conjugate(&mut budget())
                .unwrap(),
            x
        );
    }
}

#[test]
fn refusal_never_returns_partial_arithmetic_or_changes_operands() {
    let x = value(&[(0, 1), (ORDER / 8, 1)]);
    let original = x.clone();
    assert!(x.multiply(&x, &mut Budget::new(0)).is_none());
    assert!(x.norm_squared(&mut Budget::new(1)).is_none());
    let mut small = budget();
    small.max_terms = 1;
    assert!(x.add(&x, &mut small).is_none());
    let mut small = budget();
    small.max_bits = 2;
    assert!(Cyclotomic::from_terms([(0, q(4, 1))], &mut small).is_none());
    let mut small = budget();
    small.max_bits = 2;
    assert!(Cyclotomic::from_terms([(0, q(3, 1)), (0, q(3, 1))], &mut small).is_none());
    assert_eq!(x, original);
    assert!(x.terms().iter().all(|(p, r)| *p < HALF && *r != q(0, 1)));
}
