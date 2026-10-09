use super::*;
use crate::symbolic::PhaseCoefficient;

#[test]
fn shared_blocks_preserve_every_free_entry_and_refuse_incomplete_work() {
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathBra { term: 1, path: 1 };
    let bit = |v: &KernelVariable| KernelBooleanPolynomial::variable(v.clone());
    let free = (0..4).map(KernelVariable::InputKet).collect::<Vec<_>>();
    let mut source = WorkingTerm {
        paths: BTreeSet::from([x.clone(), y.clone()]),
        constraints: vec![bit(&free[0]).xor(&bit(&free[1]))],
        coefficient: KernelScalar::Rational(ratio(-3, 8)),
        phase: KernelPhasePolynomial::default(),
    };
    for mask in 1..16 {
        let monomial = free
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .fold(KernelBooleanPolynomial::one(), |m, (_, v)| m.and(&bit(v)));
        source.phase.add_boolean(
            &bit(&x).xor(&bit(&y)).and(&monomial),
            PhaseCoefficient::rational(ratio(if mask % 3 == 0 { 3 } else { 1 }, 8)),
        );
    }
    let original = source.phase.clone();
    let mut reduced = source.clone();
    assert_eq!(
        compact(&mut reduced, &mut WORK_CELLS.to_owned()),
        Some(true)
    );
    assert_eq!(reduced.paths, source.paths);
    assert_eq!(reduced.constraints, source.constraints);
    assert_eq!(reduced.coefficient, source.coefficient);
    assert!(reduced.phase.term_count() < original.term_count());
    for input in 0..16 {
        let histogram = |phase: &KernelPhasePolynomial| {
            let mut sum = BTreeMap::<BigRational, usize>::new();
            for assignment in 0..4 {
                let mut point = BTreeMap::from([
                    (x.clone(), assignment & 1 != 0),
                    (y.clone(), assignment & 2 != 0),
                ]);
                point.extend(
                    free.iter()
                        .enumerate()
                        .map(|(i, v)| (v.clone(), input & (1 << i) != 0)),
                );
                let value = phase
                    .terms()
                    .filter(|(m, _)| m.variables().all(|v| point[v]))
                    .map(|(_, c)| c.as_rational().unwrap())
                    .sum::<BigRational>();
                let value = (value % integer(1) + integer(1)) % integer(1);
                *sum.entry(value).or_default() += 1;
            }
            sum
        };
        assert_eq!(histogram(&original), histogram(&reduced.phase));
    }
    let mut refused = source.clone();
    assert_eq!(compact(&mut refused, &mut 0), None);
    assert_eq!(refused.phase, original);
    refused.constraints.push(bit(&x));
    assert_eq!(
        compact(&mut refused, &mut WORK_CELLS.to_owned()),
        Some(false)
    );
    assert_eq!(refused.phase, original);
    let mut missing = source.clone();
    missing.paths.remove(&x);
    assert_eq!(
        compact(&mut missing, &mut WORK_CELLS.to_owned()),
        Some(false)
    );
    let mut scalar = source.clone();
    scalar.coefficient = KernelScalar::Select {
        condition: bit(&y),
        when_true: Box::new(KernelScalar::Rational(integer(1))),
        when_false: Box::new(KernelScalar::Rational(integer(0))),
    };
    assert_eq!(
        compact(&mut scalar, &mut WORK_CELLS.to_owned()),
        Some(false)
    );
    let compare = |left: WorkingTerm, right: WorkingTerm| {
        matches_using(
            &Reduction::Sum(Box::new(left)),
            &Reduction::Sum(Box::new(right)),
            true,
            8,
        )
    };
    // Add another disconnected component, required by full factorization.
    let z = KernelVariable::PathKet { term: 4, path: 0 };
    for term in [&mut source, &mut reduced] {
        term.paths.insert(z.clone());
        term.phase
            .add_boolean(&bit(&z), PhaseCoefficient::rational(ratio(1, 8)));
    }
    assert!(compare(source.clone(), reduced.clone()));
    let mut wrong = reduced.clone();
    wrong.coefficient = KernelScalar::Rational(integer(1));
    assert!(!compare(source.clone(), wrong));
    let mut wrong = reduced.clone();
    wrong.constraints.clear();
    assert!(!compare(source.clone(), wrong));
    let mut wrong = reduced.clone();
    wrong
        .phase
        .add_boolean(&bit(&free[3]), PhaseCoefficient::rational(ratio(1, 4)));
    assert!(!compare(source.clone(), wrong));
    let absent = reduced
        .paths
        .iter()
        .find(|v| !reduced.phase.variables().contains(*v))
        .unwrap()
        .clone();
    reduced.paths.remove(&absent);
    assert!(!compare(source, reduced));
}
