use super::*;
use crate::symbolic::PhaseCoefficient;
use num_rational::BigRational;

fn var(v: KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v)
}
fn bound() -> KernelVariable {
    KernelVariable::PathKet { term: 0, path: 0 }
}
fn rat(n: i64) -> KernelScalar {
    KernelScalar::Rational(BigRational::from_integer(n.into()))
}
fn term(rows: Vec<KernelBooleanPolynomial>) -> WorkingTerm {
    WorkingTerm {
        constraints: rows,
        paths: [bound()].into(),
        coefficient: rat(3),
        phase: KernelPhasePolynomial::default(),
    }
}
fn eval(p: &KernelBooleanPolynomial, variables: &[KernelVariable], assignment: usize) -> bool {
    p.as_graph()
        .evaluate::<std::convert::Infallible>(|v| {
            let v = KernelVariable::from_graph_variable(v);
            let i = variables.iter().position(|x| *x == v).unwrap();
            Ok(assignment & (1 << i) != 0)
        })
        .unwrap()
}

#[test]
fn combined_guard_and_history_rows_expose_contradiction() {
    let y = var(bound());
    let yp = var(KernelVariable::PathBra { term: 0, path: 0 });
    let mut t = term(vec![y.clone(), yp.complement(), y.xor(&yp)]);
    assert!(matches!(
        t.normalize_constraints(),
        ConstraintNormalization::Contradiction
    ));
}

#[test]
fn unique_pivot_preserves_every_three_variable_boolean_constraint() {
    let variables = [
        KernelVariable::InputKet(0),
        KernelVariable::InputBra(0),
        bound(),
    ];
    // All 256 Boolean polynomials on these three variables.
    for mask in 0..256 {
        let mut equation = KernelBooleanPolynomial::zero();
        for monomial in 0..8 {
            if mask & (1 << monomial) == 0 {
                continue;
            }
            let mut product = KernelBooleanPolynomial::one();
            for (i, v) in variables.iter().enumerate() {
                if monomial & (1 << i) != 0 {
                    product = product.and(&var(v.clone()));
                }
            }
            equation = equation.xor(&product);
        }
        let t = term(vec![equation.clone()]);
        if let Some((v, replacement)) = t.best_constraint_pivot() {
            assert_eq!(v, bound());
            assert!(!replacement.variables().contains(&v));
            let reduced = equation.substitute(&v, &replacement);
            for assignment in 0..8 {
                assert_eq!(
                    !eval(&equation, &variables, assignment),
                    !eval(&reduced, &variables, assignment)
                        && (assignment & 4 != 0) == eval(&replacement, &variables, assignment)
                );
            }
        }
    }
}

#[test]
fn coupled_binders_and_free_coordinates_are_not_pivots() {
    let y = var(bound());
    let x = var(KernelVariable::InputKet(0));
    let mut t = term(vec![y.xor(&y.and(&x)).xor(&KernelBooleanPolynomial::one())]);
    assert!(t.best_constraint_pivot().is_none());
    t.constraints = vec![var(KernelVariable::QuantumOutputKet(0)).xor(&x)];
    assert!(t.best_constraint_pivot().is_none());
}

#[test]
fn substitution_updates_constraints_scalar_phase_and_preserves_weight() {
    let y = var(bound());
    let x = var(KernelVariable::InputKet(0));
    let z = var(KernelVariable::InputBra(0));
    let output = var(KernelVariable::QuantumOutputKet(0));
    let rhs = x.and(&z);
    let mut t = term(vec![y.xor(&rhs), output.xor(&y).xor(&x)]);
    t.coefficient = KernelScalar::Select {
        condition: y.clone(),
        when_true: Box::new(rat(2)),
        when_false: Box::new(rat(3)),
    };
    t.phase.add_boolean(
        &y,
        PhaseCoefficient::rational(BigRational::new(1.into(), 8.into())),
    );
    t.substitute(&bound(), &rhs);
    t.paths.remove(&bound()); // The scheduling loop removes the solved binder.
    let variables = [
        KernelVariable::InputKet(0),
        KernelVariable::InputBra(0),
        KernelVariable::QuantumOutputKet(0),
    ];
    for assignment in 0..8 {
        let expected_y = eval(&rhs, &variables, assignment);
        let scalar = match &t.coefficient {
            KernelScalar::Select {
                condition,
                when_true,
                when_false,
            } => {
                if eval(condition, &variables, assignment) {
                    when_true.as_ref()
                } else {
                    when_false.as_ref()
                }
            }
            other => other,
        };
        assert_eq!(*scalar, rat(if expected_y { 2 } else { 3 }));
        let phase: BigRational = t
            .phase
            .selectors()
            .filter(|(p, _)| eval(p, &variables, assignment))
            .map(|(_, c)| c.as_rational().unwrap())
            .sum();
        assert_eq!(
            phase,
            BigRational::new((if expected_y { 1 } else { 0 }).into(), 8.into())
        );
        assert_eq!(
            t.constraints
                .iter()
                .all(|p| !eval(p, &variables, assignment)),
            (assignment & 4 != 0) == (expected_y ^ (assignment & 1 != 0))
        );
    }
    assert!(
        t.constraints
            .iter()
            .all(|p| !p.variables().contains(&bound()))
    );
    assert!(!t.phase.variables().contains(&bound()));
}

#[test]
fn graph_row_reduction_preserves_factored_boolean_constraints() {
    let vars = [
        KernelVariable::InputKet(0),
        KernelVariable::InputKet(1),
        KernelVariable::InputKet(2),
        bound(),
    ];
    let x = |i: usize| var(vars[i].clone()).as_graph();
    let product = x(0).and(&x(1).xor(&x(2)));
    let original = term(vec![
        KernelBooleanPolynomial::from_graph(product.clone().xor(&x(3))),
        KernelBooleanPolynomial::from_graph(product.xor(&x(1))),
    ]);
    let reduced = graph_rows(&original).unwrap();
    for assignment in 0..16 {
        assert_eq!(
            original
                .constraints
                .iter()
                .all(|p| !eval(p, &vars, assignment)),
            reduced.iter().all(|p| !eval(p, &vars, assignment))
        );
    }
}

#[test]
fn output_coordinates_become_constraints_without_becoming_binders() {
    use super::super::super::kernel::{KernelClassicalOutput, KernelPhaseDifference, KernelWeight};
    let y = var(bound());
    let bra = KernelVariable::PathBra { term: 0, path: 0 };
    let yp = var(bra.clone());
    let free = KernelVariable::QuantumOutputKet(0);
    let original = KernelTerm {
        ket_guard: vec![],
        bra_guard: vec![],
        history_equalities: vec![],
        ket_paths: [bound(), free.clone()].into(),
        bra_paths: [bra.clone()].into(),
        quantum_outputs_ket: vec![y.clone()],
        quantum_outputs_bra: vec![yp.clone()],
        classical_outputs: vec![KernelClassicalOutput { ket: y, bra: yp }],
        weight: KernelWeight {
            ket: rat(2),
            bra: rat(3),
        },
        phase: KernelPhaseDifference {
            ket: Default::default(),
            bra: Default::default(),
        },
    };
    let working = WorkingTerm::from_kernel(&original);
    assert!(!working.paths.contains(&free));
    assert_eq!(working.coefficient, rat(6));
    let variables = [
        bound(),
        bra,
        free,
        KernelVariable::QuantumOutputBra(0),
        KernelVariable::ClassicalOutput(0),
    ];
    for assignment in 0..32 {
        let bit = |i: usize| assignment & (1usize << i) != 0;
        assert_eq!(
            working
                .constraints
                .iter()
                .all(|p| !eval(p, &variables, assignment)),
            bit(2) == bit(0) && bit(3) == bit(1) && bit(4) == bit(0) && bit(4) == bit(1)
        );
    }
}
