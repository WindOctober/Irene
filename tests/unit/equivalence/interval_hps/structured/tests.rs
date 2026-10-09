use super::*;

#[test]
fn fused_sum_preserves_nonlinear_predicates_and_missing_coordinates() {
    // Independent integer oracle; compare actual values, not node IDs.
    for seed in 0..16 {
        let mut d = Dag::new();
        let vars: Vec<_> = (0..4)
            .map(|i| BooleanPolynomial::variable(Variable::Path(i)))
            .collect();
        let mut factors = vec![];
        let mut oracle = vec![];
        for j in 0..5 {
            let a = (seed + j) % 4;
            let b = (seed + 2 * j + 1) % 4;
            let c = (seed + 3 * j + 2) % 4;
            let p = vars[a].and(&vars[b]).xor(&vars[c]);
            let t = (j as i64 % 3) - 1;
            let f = (seed as i64 % 3) + 1;
            let ti = d.rational(&BigRational::from_integer(t.into())).unwrap();
            let fi = d.rational(&BigRational::from_integer(f.into())).unwrap();
            factors.push(d.select(p, ti, fi).unwrap());
            oracle.push((a, b, c, t, f));
        }
        // Path 9 is absent: summing over it must still double the result.
        let expected: i64 = 2
            * (0..16)
                .map(|assignment| {
                    oracle
                        .iter()
                        .map(|&(a, b, c, t, f)| {
                            let bit = |i| assignment & (1 << i) != 0;
                            if (bit(a) && bit(b)) ^ bit(c) { t } else { f }
                        })
                        .product::<i64>()
                })
                .sum::<i64>();
        let paths = [0, 1, 2, 3, 9].into_iter().map(Variable::Path).collect();
        let id = d.sum_paths(factors, paths).unwrap();
        let value = d.value(id).unwrap();
        assert_eq!(value.re.lo, expected);
        assert_eq!(value.re.hi, expected);
        assert!(value.im.is_zero());
    }
}

#[test]
fn paired_restriction_does_not_evaluate_discarded_inverse() {
    let mut d = Dag::new();
    let y = BooleanPolynomial::variable(Variable::Path(0));
    let indicator = d.select(y.clone(), 1, 0).unwrap();
    let inverse = d.unary(Key::Inverse(indicator)).unwrap();
    let guarded = d.select(y, inverse, 1).unwrap();
    let id = d
        .sum_paths(vec![guarded], BTreeSet::from([Variable::Path(0)]))
        .unwrap();
    let value = d.value(id).unwrap();
    assert_eq!(value.re.lo, 2);
    assert_eq!(value.re.hi, 2);
}

#[test]
fn cofactor_cache_does_not_alias_variables_or_partial_results() {
    let mut d = Dag::new();
    let y = BooleanPolynomial::variable(Variable::Path(0));
    let z = BooleanPolynomial::variable(Variable::Path(1));
    let root = d.select(y.and(&z), 1, 0).unwrap();
    for variable in [0, 1, 0] {
        let v = d.variable(Variable::Path(variable));
        let partial = d.restrict(root, v, [true, false], 0).unwrap();
        assert_eq!(partial[0], 0);
        let pair = d.cofactor_pair(root, v, 0).unwrap();
        assert_eq!(pair[0], 0);
        let other = Variable::Path(1 - variable);
        assert_eq!(d.cofactor(pair[1], &other, false, 0), Some(0));
        assert_eq!(d.cofactor(pair[1], &other, true, 0), Some(1));
    }
}

#[test]
fn fused_sum_keeps_interval_uncertainty() {
    let mut d = Dag::new();
    let x = d
        .constant(Complex::real(Interval {
            lo: Float::with_val(PREC, 1),
            hi: Float::with_val(PREC, 2),
        }))
        .unwrap();
    let p = BooleanPolynomial::variable(Variable::Path(0));
    let y = d.select(p.clone(), x, 1).unwrap();
    let z = d.select(p, 1, x).unwrap();
    let id = d
        .sum_paths(vec![y, z], BTreeSet::from([Variable::Path(0)]))
        .unwrap();
    let value = d.value(id).unwrap();
    assert!(value.re.lo <= 2 && value.re.hi >= 4);
    assert!(value.re.lo < value.re.hi);
}

#[test]
fn deep_scalar_import_is_iterative() {
    let mut s = Scalar::one();
    for _ in 0..200 {
        s = Scalar::Mul(Box::new(s), Box::new(Scalar::one()));
    }
    let mut d = Dag::new();
    let id = d.scalar(&s).unwrap();
    assert_eq!(id, 1);
}
#[test]
fn wide_predicate_stays_shared_and_complements_cancel() {
    let p = (0..100)
        .map(|i| BooleanPolynomial::variable(Variable::Path(i)))
        .fold(BooleanPolynomial::zero(), |p, q| p.xor(&q));
    let mut d = Dag::new();
    let two = d.rational(&BigRational::from_integer(2.into())).unwrap();
    let a = d.select(p.clone(), two, 1).unwrap();
    let b = d.select(p.xor(&BooleanPolynomial::one()), two, 1).unwrap();
    let sum = d.add(a, b).unwrap();
    assert!(d.nodes.len() < 20);
    let value = d.value(sum).unwrap();
    assert_eq!(value.re.lo, 3);
    assert_eq!(value.re.hi, 3);
}
#[test]
fn equal_enclosures_are_not_an_equality_test() {
    let mut d = Dag::new();
    let v = Complex::real(Interval {
        lo: Float::with_val(PREC, 0),
        hi: Float::with_val(PREC, 1),
    });
    let a = d.constant(v.clone()).unwrap();
    let b = d.constant(v).unwrap();
    assert_ne!(a, b);
    let p = BooleanPolynomial::variable(Variable::Path(0));
    let s = d.select(p, a, b).unwrap();
    assert!(d.value(s).is_none());
}
#[test]
fn same_condition_factors_align_without_assignment_enumeration() {
    let mut d = Dag::new();
    let p = BooleanPolynomial::variable(Variable::Path(0));
    let a = d.select(p.clone(), 0, 1).unwrap();
    let b = d.select(p, 1, 0).unwrap();
    assert_eq!(d.multiply(vec![a, b]).unwrap(), 0);
}
#[test]
fn collapsed_selectors_finish_constant_multiplication() {
    let mut d = Dag::new();
    let p = BooleanPolynomial::variable(Variable::Path(0));
    let q = BooleanPolynomial::variable(Variable::Path(1));
    let minus = d.rational(&BigRational::from_integer((-1).into())).unwrap();
    let two = d.rational(&BigRational::from_integer(2.into())).unwrap();
    let a = d.select(p, minus, 1).unwrap();
    let b = d.select(q, minus, 1).unwrap();
    let product = d.multiply(vec![a, a, b, b, two]).unwrap();
    let value = d.value(product).unwrap();
    assert_eq!(value.re.lo, 2);
    assert_eq!(value.re.hi, 2);
}
#[test]
fn half_turn_xor_factors_preserve_all_assignments() {
    let mut d = Dag::new();
    let p = BooleanPolynomial::variable(Variable::Path(0));
    let q = BooleanPolynomial::variable(Variable::Path(1));
    let minus = d.rational(&BigRational::from_integer((-1).into())).unwrap();
    let root = p.xor(&q).xor(&BooleanPolynomial::one());
    let direct = d.select(root.clone(), minus, 1).unwrap();
    let factors = root
        .xor_terms()
        .into_iter()
        .map(|p| d.select(p, minus, 1).unwrap())
        .collect();
    let split = d.multiply(factors).unwrap();
    for a in [false, true] {
        for b in [false, true] {
            let eval = |d: &mut Dag, id| {
                let id = d.cofactor(id, &Variable::Path(0), a, 0).unwrap();
                let id = d.cofactor(id, &Variable::Path(1), b, 0).unwrap();
                d.value(id).unwrap()
            };
            let x = eval(&mut d, direct);
            let y = eval(&mut d, split);
            assert_eq!(x.re.lo, y.re.lo);
            assert_eq!(x.re.hi, y.re.hi);
        }
    }
}
