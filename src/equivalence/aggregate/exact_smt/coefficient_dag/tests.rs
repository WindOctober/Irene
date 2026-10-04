use super::*;
fn empty() -> DensityKernel {
    DensityKernel {
        input_pairs: vec![],
        quantum_output_count: 1,
        classical_output_count: 0,
        terms: vec![],
    }
}
fn evaluate(dag: &Dag, roots: Value, bit: bool) -> Vec<BigRational> {
    let mut values: Vec<BigRational> = Vec::new();
    for node in &dag.nodes {
        let value = match node {
            Node::Constant(r) => r.clone(),
            Node::Scale(r, a) => r * &values[*a],
            Node::Add(a, b) => &values[*a] + &values[*b],
            Node::Multiply(a, b) => &values[*a] * &values[*b],
            Node::Select(p, a, b) => {
                let bval = p
                    .as_graph()
                    .evaluate::<std::convert::Infallible>(|_| Ok(bit))
                    .unwrap();
                values[if bval { *a } else { *b }].clone()
            }
        };
        values.push(value);
    }
    roots.iter().map(|i| values[*i].clone()).collect()
}
#[test]
fn ablation_retains_coefficient_backend_and_complete_sums() {
    let (_, report) = crate::ablation::run(
        crate::ablation::Config::without(crate::ablation::Group::ALL),
        contraction_matches_independent_complete_atom_sum,
    );
    assert!(
        report
            .counts(crate::ablation::Group::ExpressionSimplify)
            .skipped
            > 0
    );
    assert!(
        report
            .counts(crate::ablation::Group::PathSumPlanning)
            .skipped
            > 0
    );
}

#[test]
fn ablation_disables_enhanced_coefficient_rewrites_only() {
    crate::ablation::run(
        crate::ablation::Config::without([crate::ablation::Group::ExpressionSimplify]),
        || {
            let mut dag = Dag::new();
            assert!(!dag.expression_simplify && !dag.simplify && !dag.context_enabled);
            let p = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(0));
            let a = dag.select(p.clone(), 1, 0).unwrap();
            let b = dag.select(p.complement(), 1, 0).unwrap();
            let product = dag.multiply(a, b).unwrap();
            assert!(matches!(dag.nodes[product], Node::Multiply(..)));
            assert!(dag.simplified([product, 0, 0, 0]).is_none());
            for bit in [false, true] {
                assert_eq!(evaluate(&dag, [product, 0, 0, 0], bit), vec![integer(0); 4]);
            }
        },
    );
}

#[test]
fn contraction_matches_independent_complete_atom_sum() {
    let vars: Vec<_> = (0..5)
        .map(|path| {
            if path % 2 == 0 {
                KernelVariable::PathKet { term: 0, path }
            } else {
                KernelVariable::PathBra { term: 0, path }
            }
        })
        .collect();
    let p: Vec<_> = vars
        .iter()
        .cloned()
        .map(KernelBooleanPolynomial::variable)
        .collect();
    let qv = KernelVariable::QuantumOutputKet(0);
    let q = KernelBooleanPolynomial::variable(qv.clone());
    for seed in 0..8 {
        let mut phase = KernelPhasePolynomial::default();
        for i in 0..5 {
            phase.add_boolean(
                &p[i].xor(&q),
                PhaseCoefficient::rational(ratio((seed + i as i64) % 8, 8)),
            );
            if i > 0 {
                phase.add_boolean(
                    &p[i - 1].and(&p[i]),
                    PhaseCoefficient::rational(ratio(1, 2)),
                );
            }
        }
        let t = WorkingTerm {
            paths: vars.iter().cloned().collect(),
            constraints: vec![p[0].xor(&p[1].and(&q))],
            phase,
            coefficient: KernelScalar::Select {
                condition: p[3].xor(&q),
                when_true: Box::new(KernelScalar::Rational(ratio(3, 2))),
                when_false: Box::new(KernelScalar::Rational(ratio(-1, 3))),
            },
        };
        let mut dag = Dag::new();
        let actual = dag.contract(&t).unwrap();
        for bit in [false, true] {
            let mut expected = vec![integer(0); 4];
            let mut e = Encoder::new(&empty()).unwrap();
            for bits in 0..32 {
                let mut assigned = t.clone();
                assigned.substitute(&qv, &KernelBooleanPolynomial::from(bit));
                for (i, v) in vars.iter().enumerate() {
                    assigned.substitute(v, &KernelBooleanPolynomial::from(bits >> i & 1 != 0));
                }
                for atom in e.term(&assigned).unwrap() {
                    assert_eq!(atom.guard, "true");
                    assert!(!atom.radical);
                    let Power::Constant(power) = atom.power else {
                        panic!("constant assignment");
                    };
                    let k = (power / (ORDER / 8)) as usize;
                    expected[k % 4] += atom.weight * integer(if k >= 4 { -1 } else { 1 });
                }
            }
            assert_eq!(
                evaluate(&dag, actual, bit),
                expected,
                "seed={seed} bit={bit}"
            );
        }
    }
}
#[test]
fn roots_radicals_zero_factors_and_smt_bounds_are_exact() {
    let mut dag = Dag::new();
    let p = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(0));
    let scalar = KernelScalar::Sqrt(Box::new(KernelScalar::Rational(ratio(1, 2))));
    let s = dag.scalar(&scalar, 0).unwrap();
    let ss = dag.times(s, s).unwrap();
    assert_eq!(
        evaluate(&dag, ss, false),
        vec![ratio(1, 2), integer(0), integer(0), integer(0)]
    );
    let root = dag.phase(ONE, KernelBooleanPolynomial::one(), 1).unwrap();
    let mut power = ONE;
    for _ in 0..8 {
        power = dag.times(power, root).unwrap();
    }
    assert_eq!(power, ONE);
    assert_eq!(dag.times(ss, ZERO).unwrap(), ZERO);
    let a = dag.select(p.clone(), 1, 0).unwrap();
    let na = dag.select(p, 0, 1).unwrap();
    assert_eq!(dag.multiply(a, na).unwrap(), 0);
    assert_eq!(dag.multiply(a, a).unwrap(), a);
    let minus_a = dag.scale(a, integer(-1)).unwrap();
    let complement = dag.add(1, minus_a).unwrap();
    assert_eq!(evaluate(&dag, [complement, 0, 0, 0], false)[0], integer(1));
    assert_eq!(evaluate(&dag, [complement, 0, 0, 0], true)[0], integer(0));
    let negative = dag.scale(a, ratio(-3, 7)).unwrap();
    let positive = dag.scale(a, ratio(3, 7)).unwrap();
    assert_eq!(dag.add(negative, positive).unwrap(), 0);
    let q = dag.query([negative, 0, 0, 0], &empty()).unwrap();
    assert_eq!(
        run_solver(Solver::Bitwuzla, &q.script).status,
        SolverStatus::Sat
    );
    assert!(matches!(
        q.solve(&empty()),
        AggregateComparison::Different(..)
    ));
    let q = dag.query(ZERO, &empty()).unwrap();
    assert_eq!(
        run_solver(Solver::Bitwuzla, &q.script).status,
        SolverStatus::Unsat
    );
}
#[test]
fn no_dead_definitions_or_unbound_paths_reach_smt() {
    let mut dag = Dag::new();
    let bound = KernelBooleanPolynomial::variable(KernelVariable::PathKet { term: 0, path: 7 });
    let dead = dag.select(bound, 1, 0).unwrap();
    assert!(dag.query([dead, 0, 0, 0], &empty()).is_none());
    let q = dag.query(ONE, &empty()).unwrap();
    assert!(!q.script.contains("(ite"));
    assert!(!q.script.contains("(_ BitVec 62)"));
    let undefined = KernelScalar::Select {
        condition: KernelBooleanPolynomial::zero(),
        when_true: Box::new(KernelScalar::Inverse(Box::new(KernelScalar::Rational(
            integer(0),
        )))),
        when_false: Box::new(KernelScalar::Rational(integer(1))),
    };
    assert!(dag.scalar(&undefined, 0).is_none());
    assert!(
        dag.scalar(
            &KernelScalar::Sqrt(Box::new(KernelScalar::Rational(integer(3)))),
            0
        )
        .is_none()
    );
    let mut phase = KernelPhasePolynomial::default();
    phase.add_boolean(
        &KernelBooleanPolynomial::one(),
        PhaseCoefficient::rational(ratio(1, 16)),
    );
    assert!(
        dag.leaf(&WorkingTerm {
            paths: BTreeSet::new(),
            constraints: vec![],
            coefficient: KernelScalar::Rational(integer(1)),
            phase
        })
        .is_none()
    );
}

#[test]
fn complete_kernel_route_proves_eq_and_neq_and_refuses_invalid_admission() {
    use crate::equivalence::kernel::{KernelPhaseDifference, KernelWeight};
    let mut left = empty();
    left.quantum_output_count = 0;
    left.terms.push(KernelTerm {
        ket_paths: BTreeSet::from([KernelVariable::PathKet { term: 0, path: 0 }]),
        bra_paths: BTreeSet::new(),
        ket_guard: vec![],
        bra_guard: vec![],
        history_equalities: vec![],
        quantum_outputs_ket: vec![],
        quantum_outputs_bra: vec![],
        classical_outputs: vec![],
        weight: KernelWeight {
            ket: KernelScalar::Rational(integer(1)),
            bra: KernelScalar::Rational(integer(1)),
        },
        phase: KernelPhaseDifference {
            ket: KernelPhasePolynomial::default(),
            bra: KernelPhasePolynomial::default(),
        },
    });
    let mut right = left.clone();
    right.terms[0].ket_paths.clear();
    right.terms[0].weight.ket = KernelScalar::Rational(integer(2));
    assert!(matches!(
        compare(&left, &right),
        Some(AggregateComparison::SmtEquivalent(_))
    ));
    right.terms[0].weight.ket = KernelScalar::Rational(integer(1));
    assert!(matches!(
        compare(&left, &right),
        Some(AggregateComparison::Different(..))
    ));
    right.terms[0].phase.ket.add_boolean(
        &KernelBooleanPolynomial::one(),
        PhaseCoefficient::rational(ratio(1, 16)),
    );
    right.terms[0].phase.bra = right.terms[0].phase.ket.clone();
    assert!(compare(&right, &right).is_none());
    left.terms[0]
        .quantum_outputs_ket
        .push(KernelBooleanPolynomial::zero());
    assert!(compare(&left, &left).is_none());
}

#[test]
fn lowered_coefficient_dag_matches_exact_values_on_every_free_input() {
    let mut dag = Dag::new();
    let p = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(0));
    let a = dag.constant(ratio(-11, 3)).unwrap();
    let b = dag.constant(ratio(7, 5)).unwrap();
    let s = dag.select(p, a, b).unwrap();
    let square = dag.multiply(s, s).unwrap();
    let sum = dag.add(square, s).unwrap();
    for bit in [false, true] {
        let x = if bit { ratio(-11, 3) } else { ratio(7, 5) };
        let expected = &x * &x + x;
        let negative = dag.constant(-expected).unwrap();
        let difference = dag.add(sum, negative).unwrap();
        let q = dag.query([difference, 0, 0, 0], &empty()).unwrap();
        let script = q.script.replace(
            "(check-sat)",
            &format!("(assert (= u0 {bit}))\n(check-sat)"),
        );
        assert_eq!(
            run_solver(Solver::Bitwuzla, &script).status,
            SolverStatus::Unsat
        );
    }
}
