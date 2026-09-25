use super::*;
use crate::symbolic::PhaseCoefficient;

fn bit(v: &KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v.clone())
}

#[test]
fn shared_small_sum_large_source_uses_complete_consuming_product_gate() {
    let a = KernelVariable::PathKet { term: 0, path: 0 };
    let b = KernelVariable::PathBra { term: 1, path: 0 };
    let mut common = WorkingTerm {
        constraints: vec![bit(&KernelVariable::ClassicalOutput(0))],
        paths: BTreeSet::new(),
        coefficient: KernelScalar::Rational(integer(1)),
        phase: KernelPhasePolynomial::default(),
    };
    let mut factor = WorkingTerm {
        constraints: Vec::new(),
        paths: BTreeSet::from([a.clone(), b.clone()]),
        coefficient: KernelScalar::Rational(integer(1)),
        phase: KernelPhasePolynomial::default(),
    };
    let mut small = factor.clone();
    small.paths.remove(&b);
    factor
        .phase
        .add_boolean(&bit(&a), PhaseCoefficient::rational(ratio(1, 2)));
    factor.phase.add_boolean(
        &bit(&a).and(&bit(&b)),
        PhaseCoefficient::rational(ratio(1, 2)),
    );
    for i in 0..10000 {
        let m = KernelMonomial::from_variables([
            KernelVariable::InputKet(i),
            KernelVariable::InputBra(i),
        ]);
        factor.phase.add_term(
            m.multiply(&KernelMonomial::variable(b.clone())),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
        common
            .phase
            .add_term(m, PhaseCoefficient::rational(ratio(1, 8)));
    }
    let mut left_common = common.clone();
    left_common.phase = KernelPhasePolynomial::default();
    // Both products denote 2[c=0] exp(F): at b=0 the two a leaves
    // cancel, and at b=1 both a leaves contribute exp(F). Source phases and
    // scalar/selector cannot be discarded merely to reduce local syntax.
    assert!(matches_components(
        vec![left_common.clone(), factor.clone()],
        vec![common.clone(), small.clone()]
    ));
    let mut wrong = common.clone();
    wrong.coefficient = KernelScalar::Rational(integer(2));
    assert!(!matches_components(
        vec![left_common.clone(), factor.clone()],
        vec![wrong, small.clone()]
    ));
    let mut wrong = common.clone();
    wrong.constraints[0] = wrong.constraints[0].complement();
    assert!(!matches_components(
        vec![left_common.clone(), factor.clone()],
        vec![wrong, small.clone()]
    ));
    let mut wrong = common.clone();
    wrong.phase.add_boolean(
        &bit(&KernelVariable::InputKet(0)),
        PhaseCoefficient::rational(ratio(1, 4)),
    );
    assert!(!matches_components(
        vec![left_common, factor.clone()],
        vec![wrong, small]
    ));
    // A later refused factor may never be omitted after a successful sum.
    let mut undeclared = factor.clone();
    undeclared.paths.clear();
    assert!(!matches_components(
        vec![common.clone(), factor.clone(), undeclared],
        vec![common]
    ));
    for i in 10000..34000 {
        factor.phase.add_term(
            KernelMonomial::from_variables([
                KernelVariable::InputKet(i),
                KernelVariable::InputBra(i),
            ]),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    assert!(!admitted(&factor));
}
