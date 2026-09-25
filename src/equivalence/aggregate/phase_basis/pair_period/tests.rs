use super::*;
use crate::symbolic::PhaseCoefficient;

fn variables() -> [KernelVariable; 5] {
    [
        KernelVariable::PathKet { term: 0, path: 0 },
        KernelVariable::PathBra { term: 0, path: 0 },
        KernelVariable::PathKet { term: 1, path: 0 },
        KernelVariable::InputKet(0),
        KernelVariable::InputBra(0),
    ]
}
fn fixture(coefficients: [i64; 4]) -> WorkingTerm {
    let [x, y, _, _, _] = variables();
    let mut phase = KernelPhasePolynomial::default();
    for (mask, coefficient) in coefficients.into_iter().enumerate() {
        let m = KernelMonomial::from_variables(
            [&x, &y]
                .into_iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, v)| v.clone()),
        );
        phase.add_term(m, PhaseCoefficient::rational(ratio(coefficient, 8)));
    }
    WorkingTerm {
        paths: BTreeSet::from([x, y]),
        constraints: Vec::new(),
        coefficient: KernelScalar::Rational(integer(3)),
        phase,
    }
}
fn work_budget() -> usize {
    WORK_CELLS
}
#[test]
fn oversized_pair_period_enters_complete_product_with_all_common_fields() {
    let [x, y, z, free, _] = variables();
    let mut left = fixture([0, 0, 0, 0]);
    left.paths.insert(z.clone());
    left.constraints
        .push(KernelBooleanPolynomial::variable(free.clone()));
    for i in 1..=4000 {
        let f = KernelMonomial::variable(KernelVariable::InputKet(i));
        for (mask, c) in [(1, 1), (2, 1), (3, -2)] {
            let m = KernelMonomial::from_variables(
                f.variables().cloned().chain(
                    [&x, &y]
                        .into_iter()
                        .enumerate()
                        .filter(|(j, _)| mask & (1 << j) != 0)
                        .map(|(_, v)| v.clone()),
                ),
            );
            left.phase
                .add_term(m, PhaseCoefficient::rational(ratio(c, 8)));
        }
    }
    left.phase.add_term(
        KernelMonomial::variable(z),
        PhaseCoefficient::rational(ratio(1, 8)),
    );
    let mut right = left.clone();
    right.phase.substitute(&y, &KernelBooleanPolynomial::zero());
    right.paths.remove(&y);
    right.coefficient = KernelScalar::Rational(integer(6));
    let compare = |a: WorkingTerm, b: WorkingTerm| {
        matches_reduced_components(
            &Reduction::Sum(Box::new(a)),
            &Reduction::Sum(Box::new(b)),
            &mut work_budget(),
        )
    };
    assert!(compare(left.clone(), right.clone()));
    let mut changed = right.clone();
    changed.coefficient = KernelScalar::Rational(integer(3));
    assert!(!compare(left.clone(), changed));
    let mut changed = right.clone();
    changed.constraints[0] = changed.constraints[0].complement();
    assert!(!compare(left.clone(), changed));
    let mut changed = right;
    changed.phase.add_term(
        KernelMonomial::variable(free),
        PhaseCoefficient::rational(ratio(1, 4)),
    );
    // Use a distinct free coordinate, not one forced to zero by the guard.
    changed.phase.add_term(
        KernelMonomial::variable(KernelVariable::InputBra(0)),
        PhaseCoefficient::rational(ratio(1, 4)),
    );
    assert!(!compare(left, changed));
}
