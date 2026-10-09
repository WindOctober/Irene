use super::*;
#[test]
fn seven_variable_factors_and_separators_are_admitted_by_actual_cells() {
    let vars: Vec<_> = (0..8)
        .map(|path| KernelVariable::PathKet { term: 0, path })
        .collect();
    let ps: Vec<_> = vars
        .iter()
        .cloned()
        .map(KernelBooleanPolynomial::variable)
        .collect();
    let kernel = DensityKernel {
        input_pairs: vec![],
        quantum_output_count: 0,
        classical_output_count: 0,
        terms: vec![],
    };
    let parity = ps[1..]
        .iter()
        .fold(KernelBooleanPolynomial::zero(), |p, q| p.xor(q));
    let mut t = WorkingTerm {
        paths: vars[1..].iter().cloned().collect(),
        constraints: vec![parity],
        coefficient: KernelScalar::Rational(integer(1)),
        phase: KernelPhasePolynomial::default(),
    };
    let mut e = Encoder::new(&kernel).unwrap();
    assert!(e.contract(&t).unwrap() == e.literal(integer(64), 0, false).unwrap());
    t.paths = vars.iter().cloned().collect();
    t.constraints.clear();
    for p in &ps[1..] {
        t.phase
            .add_boolean(&ps[0].and(p), PhaseCoefficient::rational(ratio(1, 2)));
    }
    // Force the hub first, producing a seven-variable separator.
    assert!(
        e.contract_ordered(&t, Some(&vars)).unwrap()
            == e.literal(integer(128), 0, false).unwrap()
    );
    assert!(
        e.contraction_cells(usize::BITS as usize, 0, 1, "test")
            .is_none()
    );
    assert!(
        e.contraction_cells(7, crate::equivalence::tuning::limits().cells, 1, "test")
            .is_none()
    );
    e.work = 127;
    assert!(e.contraction_cells(7, 0, 1, "test").is_none());
}
#[test]
fn symbolic_cells_have_a_separate_separator_width_limit() {
    let kernel = DensityKernel {
        input_pairs: vec![],
        quantum_output_count: 0,
        classical_output_count: 0,
        terms: vec![],
    };
    let mut e = Encoder::new(&kernel).unwrap();
    assert_eq!(e.contraction_cells(7, 0, 1, "closed"), Some(128));
    // Only coordinate presence is relevant to table admission here.
    e.coordinates.push(KernelVariable::InputKet(0));
    assert_eq!(e.contraction_cells(6, 0, 1, "symbolic"), Some(64));
    assert!(e.contraction_cells(7, 0, 1, "symbolic").is_none());
    // A large arithmetic budget must not remove allocation/width guards.
    e.work = usize::MAX;
    assert!(e.contraction_cells(7, 0, 1, "symbolic").is_none());
}

#[test]
fn local_contraction_matches_complete_coherent_sum() {
    let vars: Vec<_> = (0..5)
        .map(|path| KernelVariable::PathKet { term: 0, path })
        .collect();
    let ps: Vec<_> = vars
        .iter()
        .cloned()
        .map(KernelBooleanPolynomial::variable)
        .collect();
    let free = KernelVariable::QuantumOutputKet(0);
    let q = KernelBooleanPolynomial::variable(free.clone());
    let empty = DensityKernel {
        input_pairs: vec![],
        quantum_output_count: 1,
        classical_output_count: 0,
        terms: vec![],
    };
    for seed in 0..16 {
        let mut phase = KernelPhasePolynomial::default();
        for i in 0..5 {
            phase.add_boolean(
                &ps[i],
                PhaseCoefficient::rational(ratio((seed + i as i64) % 8, 8)),
            );
            if i > 0 {
                phase.add_boolean(
                    &ps[i - 1].and(&ps[i]),
                    PhaseCoefficient::rational(ratio(1, 2)),
                );
            }
        }
        let t = WorkingTerm {
            paths: vars.iter().cloned().collect(),
            constraints: vec![ps[0].xor(&ps[1].and(&q))],
            phase,
            coefficient: KernelScalar::Select {
                condition: ps[3].xor(&q),
                when_true: Box::new(KernelScalar::Rational(ratio(3, 2))),
                when_false: Box::new(KernelScalar::Rational(ratio(-1, 3))),
            },
        };
        for bit in [false, true] {
            let mut e = Encoder::new(&empty).unwrap();
            let mut t = t.clone();
            t.substitute(&free, &KernelBooleanPolynomial::from(bit));
            let actual = e.contract(&t).unwrap();
            let mut expected = Vec::new();
            for bits in 0..32 {
                let mut assigned = t.clone();
                for (i, v) in vars.iter().enumerate() {
                    assigned.substitute(v, &KernelBooleanPolynomial::from(bits >> i & 1 != 0));
                }
                expected.extend(e.term(&assigned).unwrap());
            }
            let expected = e.compact(expected).unwrap();
            assert!(actual == expected, "seed={seed} free={bit}");
        }
    }
}
