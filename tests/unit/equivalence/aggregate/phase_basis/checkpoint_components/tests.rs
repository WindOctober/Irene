use super::*;

fn bit(v: &KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v.clone())
}
fn allowance() -> usize {
    WORK_CELLS
}

#[test]
fn complete_component_output_period_keeps_common_fields_and_refuses_a_late_factor() {
    use crate::symbolic::PhaseCoefficient;
    let [x, y, z, w] = [0, 1, 2, 3].map(|path| KernelVariable::PathKet { term: 7, path });
    let mut source = WorkingTerm {
        paths: BTreeSet::from([x.clone(), y.clone(), z.clone(), w.clone()]),
        constraints: vec![],
        coefficient: KernelScalar::Rational(integer(1)),
        phase: KernelPhasePolynomial::default(),
    };
    let mut expected = KernelPhasePolynomial::default();
    for (v, c) in [(&z, 1), (&w, 3)] {
        source
            .phase
            .add_boolean(&bit(v), PhaseCoefficient::rational(ratio(c, 8)));
        expected.add_boolean(&bit(v), PhaseCoefficient::rational(ratio(c, 8)));
    }
    for i in 0..24 {
        let alias = KernelVariable::PathBra { term: 7, path: i };
        let rhs =
            bit(&KernelVariable::InputKet(2 * i)).xor(&bit(&KernelVariable::InputKet(2 * i + 1)));
        source.paths.insert(alias.clone());
        source.constraints.push(bit(&alias).xor(&rhs));
        for j in 0..40 {
            let free = bit(&KernelVariable::InputBra(i * 40 + j));
            source.phase.add_boolean(
                &bit(&alias).and(&bit(&x).xor(&bit(&y))).and(&free),
                PhaseCoefficient::rational(ratio(1, 8)),
            );
            expected.add_boolean(
                &rhs.and(&bit(&x)).and(&free),
                PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
    }
    assert!(local_cells(&source).is_some());
    let Reduction::Sum(reduced) = reduce_working_term(source.clone()) else {
        panic!("complete four-bit local sum");
    };
    assert_eq!(reduced.paths.len(), 4);
    assert!(local_cells(&reduced).is_none());
    let mut common = WorkingTerm {
        paths: BTreeSet::new(),
        constraints: vec![bit(&KernelVariable::ClassicalOutput(0))],
        coefficient: KernelScalar::Rational(integer(-3)),
        phase: KernelPhasePolynomial::default(),
    };
    common.phase.add_boolean(
        &bit(&KernelVariable::InputKet(9)),
        PhaseCoefficient::rational(ratio(3, 8)),
    );
    let result = reduce_components(
        Components::from_complete_terms(vec![common.clone(), source.clone()]),
        &mut allowance(),
    )
    .unwrap();
    assert_eq!(result.len(), 2);
    assert_eq!(result[0].paths, common.paths);
    assert_eq!(result[0].constraints, common.constraints);
    assert_eq!(result[0].coefficient, common.coefficient);
    assert_eq!(result[0].phase, common.phase);
    assert_eq!(result[1].paths, BTreeSet::from([x, z, w]));
    assert!(result[1].constraints.is_empty());
    assert_eq!(result[1].coefficient, KernelScalar::Rational(integer(2)));
    assert_eq!(result[1].phase, expected);
    let mut late = WorkingTerm {
        paths: BTreeSet::new(),
        constraints: vec![],
        coefficient: KernelScalar::Rational(integer(1)),
        phase: KernelPhasePolynomial::default(),
    };
    for path in 0..9 {
        let v = KernelVariable::PathBra { term: 99, path };
        late.paths.insert(v.clone());
        late.phase
            .add_boolean(&bit(&v), PhaseCoefficient::rational(ratio(1, 8)));
    }
    assert!(
        reduce_components(
            Components::from_complete_terms(vec![common, source, late]),
            &mut allowance()
        )
        .is_none()
    );
}

#[test]
fn checkpoint_component_product_checks_every_factor_and_common_field() {
    let u = KernelVariable::InputKet(0);
    let mut left = WorkingTerm {
        paths: (0..530)
            .map(|path| KernelVariable::PathKet { term: 4, path })
            .collect(),
        constraints: vec![bit(&u)],
        coefficient: KernelScalar::Rational(BigRational::new(
            BigInt::from(1),
            BigInt::from(1) << 395,
        )),
        phase: KernelPhasePolynomial::default(),
    };
    //27 disconnected ten-bit chains, each exactly32, and260 absent bits.
    // Independent ALL1024 phase evaluations in Q[zeta8] establish32,
    // rather than asking the production local reducer to certify itself.
    let mut exact = [0i64; 4];
    for bits in 0..1024usize {
        let edges = (0..9).filter(|&i| bits & (3 << i) == 3 << i).count();
        let power = (4 * edges + usize::from(bits & 512 != 0)) % 8;
        exact[power % 4] += if power < 4 { 1 } else { -1 };
    }
    assert_eq!(exact, [32, 0, 0, 0]);
    for group in 0..27 {
        let paths = (0..10)
            .map(|i| KernelVariable::PathKet {
                term: 4,
                path: group * 10 + i,
            })
            .collect::<Vec<_>>();
        for pair in paths.windows(2) {
            left.phase.add_boolean(
                &bit(&pair[0]).and(&bit(&pair[1])),
                crate::symbolic::PhaseCoefficient::rational(ratio(1, 2)),
            );
        }
        left.phase.add_boolean(
            &bit(&paths[9]),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    assert!(without_vacuous(&left).is_none()); //270ACTIVE, not merely names.
    let right = WorkingTerm {
        paths: BTreeSet::new(),
        constraints: vec![bit(&u)],
        coefficient: KernelScalar::Rational(integer(1)),
        phase: KernelPhasePolynomial::default(),
    };
    assert!(matches(&left, &right));
    assert!(matches_checkpoints(
        &Reduction::Residual,
        &Reduction::Sum(Box::new(right.clone())),
        Some(&left),
        None
    ));
    let mut bad = right.clone();
    bad.coefficient = KernelScalar::Rational(integer(2));
    assert!(!matches(&left, &bad));
    bad = right.clone();
    bad.constraints = vec![bit(&u).xor(&KernelBooleanPolynomial::one())];
    assert!(!matches(&left, &bad));
    bad = right;
    bad.phase.add_boolean(
        &bit(&KernelVariable::InputBra(1)),
        crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
    );
    assert!(!matches(&left, &bad));
    let factors = components(&left, &mut allowance()).unwrap();
    assert!(reduce_components(factors.clone(), &mut 0).is_none());
    let mut bad_factors = factors;
    let last = bad_factors.last_mut().unwrap();
    //A last, valid nine-bit factor with no applicable exact local identity
    //must refuse the WHOLE new entrance, never accept earlier components.
    last.paths = (0..9)
        .map(|path| KernelVariable::PathBra { term: 7, path })
        .collect();
    last.phase = KernelPhasePolynomial::default();
    for p in &last.paths {
        last.phase.add_boolean(
            &bit(p),
            crate::symbolic::PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    assert!(reduce_components(bad_factors, &mut allowance()).is_none());
}
