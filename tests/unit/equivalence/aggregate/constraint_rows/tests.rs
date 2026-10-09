use super::*;

#[test]
fn nonlinear_rows_preserve_selectors_without_claiming_boolean_ideal_completion() {
    let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
    let y = KernelBooleanPolynomial::variable(KernelVariable::InputKet(1));
    let z = KernelBooleanPolynomial::variable(KernelVariable::InputKet(2));
    let original = [
        x.and(&y).xor(&z),
        y.and(&z).xor(&KernelBooleanPolynomial::one()),
    ];
    let reduced = reduce(&original.iter().collect::<Vec<_>>()).ok().unwrap();
    let eval = |p: &KernelBooleanPolynomial, value: usize| {
        p.terms().fold(false, |a, m| {
            a ^ m.variables().all(|v| {
                let KernelVariable::InputKet(i) = v else {
                    panic!("unexpected role")
                };
                value & (1 << i) != 0
            })
        })
    };
    for value in 0..8 {
        assert_eq!(
            original.iter().all(|p| !eval(p, value)),
            reduced.iter().all(|p| !eval(p, value))
        );
    }
    let only_x = reduce(&[&x]).ok().unwrap();
    let xy = x.and(&y);
    // Same Boolean zero set, different formal row span: keep this incomplete.
    assert_ne!(only_x, reduce(&[&x, &xy]).ok().unwrap());
}

#[test]
fn budget_refusal_is_atomic_for_the_constraint_owner() {
    let mut rows = (0..3163)
        .map(|i| KernelBooleanPolynomial::variable(KernelVariable::InputKet(i)))
        .collect::<Vec<_>>();
    let original = rows.clone();
    assert!(matches!(
        normalize_constraint_span(&mut rows),
        ConstraintNormalization::BudgetExceeded
    ));
    assert_eq!(rows, original);
}
