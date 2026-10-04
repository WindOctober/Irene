use super::*;
use crate::equivalence::kernel::{KernelInputPair, KernelPhaseDifference, KernelWeight};

fn kernel() -> DensityKernel {
    DensityKernel {
        input_pairs: vec![KernelInputPair {
            ket: KernelVariable::InputKet(0),
            bra: KernelVariable::InputBra(0),
        }],
        quantum_output_count: 0,
        classical_output_count: 0,
        terms: vec![],
    }
}
fn phase(v: KernelVariable, r: BigRational) -> KernelPhasePolynomial {
    let mut p = KernelPhasePolynomial::default();
    p.add_term(
        KernelMonomial::from_variables([v]),
        PhaseCoefficient::rational(r),
    );
    p
}

#[test]
fn closed_trace_norm_retains_interference_guards_scalars_and_vacuous_binders() {
    let x = KernelVariable::PathKet { term: 0, path: 0 };
    let y = KernelVariable::PathKet { term: 0, path: 1 };
    let p = KernelBooleanPolynomial::variable(x.clone());
    let mut t = WorkingTerm {
        paths: BTreeSet::from([x.clone()]),
        constraints: vec![],
        coefficient: KernelScalar::Rational(ratio(1, 2)),
        phase: phase(x.clone(), ratio(1, 8)),
    };
    // |(1+zeta_8)/2|² = 1/2 + zeta_8/4 - zeta_8³/4.
    let expected = vec![
        (0, ratio(1, 2)),
        (ORDER / 8, ratio(1, 4)),
        (3 * ORDER / 8, ratio(-1, 4)),
    ];
    assert_eq!(closed_norm(t.clone()), Some(expected.clone()));
    t.paths.insert(y);
    assert_eq!(
        closed_norm(t.clone()),
        Some(
            expected
                .into_iter()
                .map(|(p, c)| (p, c * integer(4)))
                .collect()
        )
    );
    t.constraints.push(p.clone());
    assert_eq!(closed_norm(t.clone()), Some(vec![(0, integer(1))]));
    t.constraints.push(p.complement());
    assert_eq!(closed_norm(t), Some(vec![]));

    let t = WorkingTerm {
        paths: BTreeSet::from([x.clone()]),
        constraints: vec![],
        coefficient: KernelScalar::Select {
            condition: p,
            when_true: Box::new(KernelScalar::Rational(integer(-1))),
            when_false: Box::new(KernelScalar::Rational(integer(1))),
        },
        phase: phase(x, ratio(1, 2)),
    };
    // The negative scalar and phase reinforce; they must not be squared
    // separately before the coherent sum (which would incorrectly give 2).
    assert_eq!(closed_norm(t), Some(vec![(0, integer(4))]));
}

#[test]
fn closed_trace_norm_refuses_free_or_undeclared_paths_and_unsupported_angles() {
    for (v, paths, angle) in [
        (KernelVariable::InputKet(0), BTreeSet::new(), ratio(1, 8)),
        (
            KernelVariable::PathKet { term: 0, path: 0 },
            BTreeSet::new(),
            ratio(1, 8),
        ),
        (
            KernelVariable::PathKet { term: 0, path: 0 },
            BTreeSet::from([KernelVariable::PathKet { term: 0, path: 0 }]),
            ratio(1, 3),
        ),
    ] {
        let t = WorkingTerm {
            paths,
            constraints: vec![],
            coefficient: KernelScalar::Rational(integer(1)),
            phase: phase(v, angle),
        };
        assert_eq!(closed_norm(t), None);
    }
}

#[test]
fn closed_trace_norm_matches_independent_complete_integer_histograms() {
    let vars: Vec<_> = (0..4)
        .map(|path| KernelVariable::PathKet { term: 0, path })
        .collect();
    let p: Vec<_> = vars
        .iter()
        .cloned()
        .map(KernelBooleanPolynomial::variable)
        .collect();
    for seed in 0..16 {
        let mut phase = KernelPhasePolynomial::default();
        for i in 0..4 {
            phase.add_boolean(
                &p[i].xor(&p[(i + 1) % 4].and(&p[(i + 2) % 4])),
                PhaseCoefficient::rational(ratio(((seed + i) % 8) as i64, 8)),
            );
        }
        let t = WorkingTerm {
            paths: vars.iter().cloned().collect(),
            constraints: vec![p[0].xor(&p[1].and(&p[2]))],
            coefficient: KernelScalar::Select {
                condition: p[3].clone(),
                when_true: Box::new(KernelScalar::Rational(ratio(-1, 16))),
                when_false: Box::new(KernelScalar::Rational(ratio(3, 16))),
            },
            phase,
        };
        let mut histogram = [0i64; 8];
        for bits in 0..16 {
            let bit = |i: usize| bits >> i & 1;
            if bit(0) != bit(1) * bit(2) {
                continue;
            }
            let power: usize = (0..4)
                .map(|i| (seed + i) % 8 * (bit(i) ^ (bit((i + 1) % 4) * bit((i + 2) % 4))))
                .sum();
            histogram[power % 8] += if bit(3) == 1 { -1 } else { 3 };
        }
        let mut norm = [0i64; 4];
        for i in 0..8 {
            for j in 0..8 {
                let power = (i + 8 - j) % 8;
                norm[power % 4] += histogram[i] * histogram[j] * if power >= 4 { -1 } else { 1 };
            }
        }
        let expected = norm
            .into_iter()
            .enumerate()
            .filter(|(_, n)| *n != 0)
            .map(|(i, n)| (i as u64 * (ORDER / 8), ratio(n, 256)))
            .collect();
        assert_eq!(closed_norm(t), Some(expected), "seed={seed}");
    }
}
fn atom(e: &mut Encoder, r: i64, p: u64) -> Atom {
    e.literal(integer(r), p, false).unwrap().remove(0)
}
fn status(q: &Query) -> SolverStatus {
    run_solver(Solver::Bitwuzla, &q.script).status
}
fn solve(q: &Query) -> DensityCounterexample {
    let r = run_solver(
        Solver::Bitwuzla,
        &format!("{}(get-value ({}))\n", q.script, q.names.join(" ")),
    );
    assert_eq!(r.status, SolverStatus::Sat, "{}", r.stderr);
    q.witness(&r.stdout, &kernel()).unwrap()
}

#[test]
fn work_ablation_removes_global_and_probe_cutoffs_without_dropping_terms() {
    let mut e = Encoder::new(&kernel()).unwrap();
    e.unlimited_work = false;
    e.work = 10;
    assert_eq!(e.probe_work_budget(4), 4);
    assert!(e.charge(11).is_none());
    let mut e = Encoder::new(&kernel()).unwrap();
    e.unlimited_work = true;
    e.work = usize::MAX;
    assert_eq!(e.probe_work_budget(4), usize::MAX);
    e.charge(MAX_WORK + 1).unwrap();
    assert_eq!(e.work, usize::MAX - MAX_WORK - 1);
    let p = e.literal(integer(3), ORDER / 8, false).unwrap();
    let q = e.literal(integer(2), 0, false).unwrap();
    let product = e.multiply(p, q).unwrap();
    assert!(product == e.literal(integer(6), ORDER / 8, false).unwrap());
}

#[test]
fn guard_mirror_keeps_independent_equalities_factored() {
    let mut k = kernel();
    k.input_pairs = (0..24)
        .map(|i| KernelInputPair {
            ket: KernelVariable::InputKet(i),
            bra: KernelVariable::InputBra(i),
        })
        .collect();
    let mut e = Encoder::new(&k).unwrap();
    let mut guard = "true".to_owned();
    for i in 0..24 {
        let a = KernelBooleanPolynomial::variable(KernelVariable::InputKet(i));
        let b = KernelBooleanPolynomial::variable(KernelVariable::InputBra(i));
        let parity = e.boolean(&a.xor(&b)).unwrap();
        let equality = e.not(parity).unwrap();
        guard = e.and(guard, equality).unwrap();
    }
    let graph = e.guard_graph(&guard).unwrap();
    assert!(!graph.is_algebraic());
    let (network, _) = crate::symbolic::BooleanPolynomial::graph_network(&[graph.as_graph()]);
    assert!(network.nodes.len() < 200);
    let mut assigned = graph;
    for i in 0..24 {
        let value = KernelBooleanPolynomial::from(i % 2 == 0);
        assigned = assigned.substitute(&KernelVariable::InputKet(i), &value);
        assigned = assigned.substitute(&KernelVariable::InputBra(i), &value);
    }
    assert!(assigned.is_one());
}

#[test]
fn product_certificate_requires_every_complete_factor_to_match() {
    let mut e = Encoder::new(&kernel()).unwrap();
    let mut first = e.literal(integer(2), 0, false).unwrap();
    first[0].guard = "u0".into();
    let mut split = e.literal(integer(1), 0, false).unwrap();
    split[0].guard = "u0".into();
    split.push(split[0].clone());
    let last = e.literal(integer(3), 0, false).unwrap();
    let a = vec![first, last.clone()];
    let mut b = vec![split, last];
    assert!(e.prove_factor_products(&a, &b, 1).is_some());
    b[1] = e.literal(integer(4), 0, false).unwrap();
    assert!(e.prove_factor_products(&a, &b, 1).is_none());
    assert!(e.prove_factor_products(&a, &b[..1], 1).is_none());
}

#[test]
fn factor_comparison_uses_only_the_domain_of_a_proved_common_factor() {
    let mut e = Encoder::new(&kernel()).unwrap();
    let mut selected = e.literal(integer(1), 0, false).unwrap();
    selected[0].guard = "u0".into();
    let one = e.literal(integer(1), 0, false).unwrap();
    let a = vec![selected.clone(), one];
    let mut b = vec![selected.clone(), selected];
    // u0 * 1 = u0 * u0; the second factors agree on the common domain.
    assert!(e.prove_factor_products(&a, &b, 1).is_some());
    b[0][0].guard = "u1".into();
    // u0 != u1*u0 in general; an unmatched guard cannot be assumed.
    assert!(e.prove_factor_products(&a, &b, 1).is_none());
}

#[test]
fn overlapping_guard_groups_sum_all_terms_and_keep_conditional_phases() {
    let mut e = Encoder::new(&kernel()).unwrap();
    let p = e
        .phase(&phase(KernelVariable::InputKet(0), ratio(1, 2)))
        .unwrap();
    let mut x = atom(&mut e, 1, 0);
    x.guard = "u0".into();
    x.power = p;
    let mut y = atom(&mut e, 3, 0);
    y.guard = "u1".into();
    let left = vec![x.clone(), x, y.clone()];
    let mut right = vec![atom(&mut e, -2, 0), y];
    right[0].guard = "u0".into();
    // On u0 the sign is -1, and on u0 && u1 BOTH groups contribute.
    assert!(e.prove_guard_groups(&left, &right, &[]).is_some());
    right[0].weight = integer(2);
    assert!(e.prove_guard_groups(&left, &right, &[]).is_none());
}

#[test]
fn failed_groups_do_not_reject_cross_guard_cancellation() {
    let mut e = Encoder::new(&kernel()).unwrap();
    let mut selected = atom(&mut e, 1, 0);
    selected.guard = "u0".into();
    let mut complement = selected.clone();
    complement.guard = e.not("u0".into()).unwrap();
    let left = vec![selected, complement];
    let right = vec![atom(&mut e, 1, 0)];
    assert!(e.prove_guard_groups(&left, &right, &[]).is_none());
    assert_eq!(
        status(&e.dense_product_query(vec![left], vec![right], 1).unwrap()),
        SolverStatus::Unsat
    );
}

#[test]
fn group_sat_is_inconclusive_even_with_identical_guard_keys() {
    let mut e = Encoder::new(&kernel()).unwrap();
    let mut a = atom(&mut e, 1, 0);
    a.guard = "u0".into();
    let mut b = a.clone();
    b.guard = e.define("Bool", "(and u0 true)".into()).unwrap();
    let left = vec![a.clone(), b.clone()];
    a.weight = integer(3);
    b.weight = integer(-1);
    let right = vec![a, b];
    // Same guard-key set, but each group differs. The TOTAL is still 2*[u0].
    assert!(e.prove_guard_groups(&left, &right, &[]).is_none());
    assert_eq!(
        status(&e.dense_product_query(vec![left], vec![right], 1).unwrap()),
        SolverStatus::Unsat
    );
}

#[test]
fn relative_phase_preserves_difference_and_cancels_common_selectors() {
    let mut e = Encoder::new(&kernel()).unwrap();
    let x = KernelVariable::InputKet(0);
    let y = KernelVariable::InputBra(0);
    let left = phase(x.clone(), ratio(1, 8));
    let mut right = left.clone();
    right.add_boolean(
        &KernelBooleanPolynomial::variable(y),
        PhaseCoefficient::rational(ratio(1, 2)),
    );
    let a = e.phase(&left).unwrap();
    let b = e.phase(&right).unwrap();
    let delta = e.relative_power(b.clone(), &a).unwrap();
    assert_eq!(delta.step(), HALF);
    assert!(
        !delta
            .form()
            .unwrap()
            .selectors
            .keys()
            .any(|s| s.variables().contains(&x))
    );
    let q = format!(
        "(set-logic QF_BV)\n{}(assert (distinct {} (bvsub {} {})))\n(check-sat)\n",
        e.definitions,
        delta.text(),
        b.text(),
        a.text()
    );
    assert_eq!(run_solver(Solver::Bitwuzla, &q).status, SolverStatus::Unsat);
    // Different input-dependent phases cannot be discarded independently.
    let mut l = atom(&mut e, 1, 0);
    l.power = a;
    let mut r = l.clone();
    r.power = b;
    assert!(e.prove_guard_groups(&vec![l], &vec![r], &[]).is_none());
}

#[test]
fn mixed_phase_normalization_matches_unreduced_bv_arithmetic() {
    let mut e = Encoder::new(&kernel()).unwrap();
    let x = KernelBooleanPolynomial::variable(KernelVariable::InputKet(0));
    let y = KernelBooleanPolynomial::variable(KernelVariable::InputBra(0));
    let mut form = PhaseForm::default();
    form.constant = ORDER - 3;
    form.add(x.clone(), HALF + 5);
    form.add(y.clone(), HALF);
    form.add(x.xor(&y), HALF);
    let actual = e.lower_phase_form(form).unwrap();
    // Three half-turn selectors cancel: x XOR y XOR (x XOR y) = 0.
    let expected = "(bvadd (_ bv4611686018427387901 62) (ite u0 (_ bv5 62) (_ bv0 62)))";
    let q = format!(
        "(set-logic QF_BV)\n{}(assert (distinct {} {expected}))\n(check-sat)\n",
        e.definitions,
        actual.text()
    );
    assert_eq!(run_solver(Solver::Bitwuzla, &q).status, SolverStatus::Unsat);
    let zero = e.relative_power(actual.clone(), &actual).unwrap();
    assert_eq!(zero, Power::Constant(0));
}

#[test]
fn external_relative_phase_moves_into_sum_without_dropping_weights_or_guards() {
    let mut e = Encoder::new(&kernel()).unwrap();
    let p = e
        .phase(&phase(KernelVariable::InputKet(0), ratio(1, 8)))
        .unwrap();
    let sign = e
        .phase(&phase(KernelVariable::InputBra(0), ratio(1, 2)))
        .unwrap();
    let mut l = atom(&mut e, 3, 0);
    l.guard = "u0".into();
    l.power = p.clone();
    let mut r = l.clone();
    r.power = e.plus_power(p, sign.clone()).unwrap();
    let one = atom(&mut e, 1, 0);
    let mut signed = one.clone();
    signed.power = sign;
    let a = vec![vec![l], vec![one.clone(), one]];
    let mut b = vec![vec![r], vec![signed.clone(), signed]];
    // exp(P)*3*[u0]*2 == exp(P+sign)*3*[u0]*(2*exp(sign)).
    assert!(e.prove_factor_products(&a, &b, 4).is_some());
    assert_eq!(
        status(
            &e.clone()
                .dense_product_query(a.clone(), b.clone(), 4)
                .unwrap()
        ),
        SolverStatus::Unsat
    );
    b[0][0].weight = integer(4);
    assert!(e.prove_factor_products(&a, &b, 4).is_none());
    assert_eq!(
        status(&e.dense_product_query(a, b, 4).unwrap()),
        SolverStatus::Sat
    );
}

#[test]
fn regional_certificate_covers_both_free_cofactors_and_overlapping_guards() {
    let mut e = Encoder::new(&kernel()).unwrap();
    let mut a = atom(&mut e, 1, 0);
    a.guard = "u0".into();
    let mut b = a.clone();
    b.guard = e.not("u0".into()).unwrap();
    let left = vec![vec![a.clone(), b]];
    let right = vec![vec![atom(&mut e, 1, 0)]];
    assert!(e.prove_regions(&left, &right).is_some());
    // Agreement on u0=true alone is not a complete certificate.
    assert!(e.prove_regions(&vec![vec![a]], &right).is_none());
    let mut unowned = atom(&mut e, 1, 0);
    unowned.guard = "unowned".into();
    e.guards.insert(
        "unowned".into(),
        KernelBooleanPolynomial::variable(KernelVariable::PathKet { term: 0, path: 0 }),
    );
    assert!(e.prove_regions(&vec![vec![unowned]], &right).is_none());
}

#[test]
fn opposite_factor_signs_must_cancel_in_the_complete_product() {
    let mut e = Encoder::new(&kernel()).unwrap();
    let a = vec![vec![atom(&mut e, 2, 0)], vec![atom(&mut e, 3, 0)]];
    let mut b = vec![vec![atom(&mut e, -2, 0)], vec![atom(&mut e, -3, 0)]];
    assert!(e.prove_factor_products(&a, &b, 1).is_some());
    b[1][0].weight = integer(3);
    assert!(e.prove_factor_products(&a, &b, 1).is_none());
}

#[test]
fn factor_contents_and_nonreal_unit_ratios_preserve_the_whole_product() {
    let mut e = Encoder::new(&kernel()).unwrap();
    let x = vec![atom(&mut e, 2, 0), atom(&mut e, 2, ORDER / 4)];
    let y = vec![atom(&mut e, 3, 0), atom(&mut e, 3, 3 * ORDER / 4)];
    let a = vec![x.clone(), y.clone()];
    let mut b = vec![y, x];
    assert!(e.prove_factor_products(&a, &b, 2).is_some());
    assert_eq!(
        status(
            &e.clone()
                .dense_product_query(a.clone(), b.clone(), 2)
                .unwrap()
        ),
        SolverStatus::Unsat
    );
    for atom in &mut b[0] {
        atom.weight *= integer(2);
    }
    assert!(e.prove_factor_products(&a, &b, 2).is_none());
    assert_eq!(
        status(&e.dense_product_query(a, b, 2).unwrap()),
        SolverStatus::Sat
    );
}

#[test]
fn variable_exponents_and_collision_folding_match_every_free_assignment() {
    // zeta^(u/8)-zeta^(v/8); a symbolic basis index must handle collisions,
    // not treat distinct phase syntax or every individual atom as nonzero.
    for denominator in [8u64, 16, ORDER] {
        for u in [false, true] {
            for v in [false, true] {
                let k = kernel();
                let mut e = Encoder::new(&k).unwrap();
                let mut source = ExactAggregate::new();
                let terms = BTreeMap::from([
                    (
                        phase(
                            KernelVariable::InputKet(0),
                            BigRational::new(1.into(), denominator.into()),
                        ),
                        KernelScalar::Rational(integer(1)),
                    ),
                    (
                        phase(
                            KernelVariable::InputBra(0),
                            BigRational::new(1.into(), denominator.into()),
                        ),
                        KernelScalar::Rational(integer(-1)),
                    ),
                ]);
                source.insert(
                    ExactEntry {
                        constraints: vec![],
                    },
                    terms,
                );
                let p = e.aggregate(&source).unwrap();
                let mut q = e.query(p).unwrap();
                q.script = q.script.replace(
                    "(check-sat)",
                    &format!("(assert (= u0 {u}))\n(assert (= u1 {v}))\n(check-sat)"),
                );
                assert_eq!(
                    status(&q),
                    if u == v {
                        SolverStatus::Unsat
                    } else {
                        SolverStatus::Sat
                    }
                );
                if u != v {
                    let w = solve(&q);
                    let p = ORDER / denominator;
                    let expected = if u {
                        vec![(0, integer(-1)), (p, integer(1))]
                    } else {
                        vec![(0, integer(1)), (p, integer(-1))]
                    };
                    assert_eq!(w.difference_coefficients, expected);
                }
            }
        }
    }
}

#[test]
fn rational_width_bounds_prevent_signed_overflow_and_do_not_bound_phase_wrap() {
    let k = kernel();
    let mut e = Encoder::new(&k).unwrap();
    let huge = BigRational::from_integer(BigInt::from(1) << 512);
    let mut a = e.literal(huge.clone(), 0, false).unwrap();
    // Different guard syntax, so coefficient cancellation must occur in SMT.
    let condition = e
        .boolean(&KernelBooleanPolynomial::variable(
            KernelVariable::InputKet(0),
        ))
        .unwrap();
    let mut b = e.literal(-huge, 0, false).unwrap();
    b[0].guard = condition;
    a.extend(b);
    a.extend(e.literal(ratio(1, 3), 0, false).unwrap());
    let q = e.query(a).unwrap();
    assert!(q.width > 512);
    assert_eq!(q.denominator, 3.into());
    assert_eq!(status(&q), SolverStatus::Sat);
    assert!(!solve(&q).difference_coefficients.is_empty());
    let mut e = Encoder::new(&k).unwrap();
    let p = e
        .plus_power(Power::Constant(ORDER - 1), Power::Constant(2))
        .unwrap();
    assert_eq!(p, Power::Constant(1));
}

#[test]
fn half_turn_fold_and_sqrt_three_extension_are_exact() {
    let k = kernel();
    let mut e = Encoder::new(&k).unwrap();
    let a = atom(&mut e, 7, 0);
    let b = atom(&mut e, 7, HALF);
    assert_eq!(status(&e.query(vec![a, b]).unwrap()), SolverStatus::Unsat);
    let mut e = Encoder::new(&k).unwrap();
    let root = KernelScalar::Sqrt(Box::new(KernelScalar::Rational(integer(3))));
    let a = e.scalar(&root, 0).unwrap();
    let b = e.scalar(&root, 0).unwrap();
    let mut square = e.multiply(a, b).unwrap();
    square.extend(e.literal(integer(-3), 0, false).unwrap());
    assert_eq!(status(&e.query(square).unwrap()), SolverStatus::Unsat);
    let mut e = Encoder::new(&k).unwrap();
    let mut irrational = e.scalar(&root, 0).unwrap();
    irrational.extend(e.literal(integer(-2), 0, false).unwrap());
    let w = solve(&e.query(irrational).unwrap());
    assert_eq!(w.difference_coefficients, vec![(0, integer(-2))]);
    assert_eq!(w.sqrt_three_coefficients, vec![(0, integer(1))]);
}

#[test]
fn complete_product_nonzero_retains_zero_common_factors() {
    let k = kernel();
    let mut e = Encoder::new(&k).unwrap();
    let a = atom(&mut e, 1, 0);
    let b = atom(&mut e, 1, HALF);
    let residual = e.literal(integer(1), 0, false).unwrap();
    let q = e.product_query(vec![residual, vec![a, b]]).unwrap();
    assert_eq!(status(&q), SolverStatus::Unsat);
    let mut e = Encoder::new(&k).unwrap();
    let factors = (0..24)
        .map(|i| e.literal(ratio(i + 1, i + 2), 0, false))
        .collect::<Option<Vec<_>>>()
        .unwrap();
    let q = e.product_query(factors).unwrap();
    let w = solve(&q);
    assert_eq!(w.exact_factors.len(), 23);
    assert!(w.exact_factors.iter().all(|f| !f.coefficients.is_empty()));
}

#[test]
fn selectors_scalar_branches_and_unsupported_domains_are_not_dropped() {
    let k = kernel();
    for invalid in [
        KernelScalar::Inverse(Box::new(KernelScalar::Rational(integer(0)))),
        KernelScalar::Sqrt(Box::new(KernelScalar::Rational(integer(-1)))),
    ] {
        for s in [
            invalid.clone(),
            KernelScalar::Mul(
                Box::new(KernelScalar::Rational(integer(0))),
                Box::new(invalid.clone()),
            ),
            KernelScalar::Select {
                condition: KernelBooleanPolynomial::zero(),
                when_true: Box::new(invalid),
                when_false: Box::new(KernelScalar::Rational(integer(1))),
            },
        ] {
            assert!(Encoder::new(&k).unwrap().scalar(&s, 0).is_none());
        }
    }
    let bad_phase = phase(KernelVariable::InputKet(0), ratio(1, 3));
    assert!(Encoder::new(&k).unwrap().phase(&bad_phase).is_none());
    let bad_var = KernelBooleanPolynomial::variable(KernelVariable::InputKet(99));
    assert!(Encoder::new(&k).unwrap().boolean(&bad_var).is_none());
    let mut e = Encoder::new(&k).unwrap();
    e.work = 0;
    assert!(e.scalar(&KernelScalar::Rational(integer(1)), 0).is_none());
}

#[test]
fn binders_are_complete_sums_not_existential_witnesses() {
    let k = kernel();
    let y = KernelVariable::PathKet { term: 0, path: 0 };
    let term = WorkingTerm {
        paths: BTreeSet::from([y.clone()]),
        constraints: vec![],
        phase: phase(y.clone(), ratio(1, 2)),
        coefficient: KernelScalar::Rational(integer(1)),
    };
    let mut e = Encoder::new(&k).unwrap();
    let p = e.bound_sum(term.clone()).unwrap();
    assert_eq!(status(&e.query(p).unwrap()), SolverStatus::Unsat);
    let mut e = Encoder::new(&k).unwrap();
    let mut vacuous = term.clone();
    vacuous.phase = KernelPhasePolynomial::default();
    let p = e.bound_sum(vacuous).unwrap();
    let w = solve(&e.query(p).unwrap());
    assert_eq!(w.difference_coefficients, vec![(0, integer(2))]);
    let mut e = Encoder::new(&k).unwrap();
    let mut unowned = term;
    unowned.paths.clear();
    assert!(e.bound_sum(unowned).is_none());
}

#[test]
fn raw_admission_precedes_phase_cancellation_and_checks_all_output_roles() {
    let mut k = kernel();
    k.terms.push(KernelTerm {
        ket_paths: BTreeSet::new(),
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
            ket: phase(KernelVariable::InputKet(0), ratio(1, 3)),
            bra: phase(KernelVariable::InputKet(0), ratio(1, 3)),
        },
    });
    assert!(Encoder::new(&k).unwrap().kernel_factors(&k).is_none());
    k.terms[0].phase = KernelPhaseDifference {
        ket: KernelPhasePolynomial::default(),
        bra: KernelPhasePolynomial::default(),
    };
    k.terms[0]
        .quantum_outputs_ket
        .push(KernelBooleanPolynomial::zero());
    assert!(Encoder::new(&k).unwrap().kernel_factors(&k).is_none());
}

#[test]
fn malformed_models_cannot_become_certificates() {
    let names = vec!["u0".to_owned()];
    assert!(model_values("sat\n((u0 true) (u0 false))", &names).is_none());
    assert!(model_values("sat\n()", &names).is_none());
    assert_eq!(boolean_value("unknown"), None);
    assert_eq!(bits("#bnot-a-value"), None);
}

#[test]
fn signed_integer_products_preserve_all_values_with_widening_and_denominators() {
    for u in [false, true] {
        for v in [false, true] {
            let k = kernel();
            let mut e = Encoder::new(&k).unwrap();
            let large = BigRational::new(BigInt::from(1) << 300, 3.into());
            let negative = ratio(-7, 5);
            let select = |variable, yes: BigRational, no: BigRational| KernelScalar::Select {
                condition: KernelBooleanPolynomial::variable(variable),
                when_true: Box::new(KernelScalar::Rational(yes)),
                when_false: Box::new(KernelScalar::Rational(no)),
            };
            let a = e
                .scalar(
                    &select(KernelVariable::InputKet(0), large.clone(), integer(0)),
                    0,
                )
                .unwrap();
            let b = e
                .scalar(
                    &select(KernelVariable::InputBra(0), negative.clone(), integer(2)),
                    0,
                )
                .unwrap();
            let one = e.literal(integer(1), 0, false).unwrap();
            let mut q = e.rational_product_query(vec![a, b], vec![one]).unwrap();
            q.script = q.script.replace(
                "(check-sat)",
                &format!("(assert (= u0 {u}))\n(assert (= u1 {v}))\n(check-sat)"),
            );
            let w = solve(&q);
            let expected = (if u { large } else { integer(0) })
                * (if v { negative } else { integer(2) })
                - integer(1);
            assert_eq!(w.difference_coefficients, vec![(0, expected)]);
        }
    }
    let k = kernel();
    let mut e = Encoder::new(&k).unwrap();
    let a = e
        .rational_literal((BigInt::from(1) << 20000) - 1, 1.into())
        .unwrap();
    let b = e
        .rational_literal((BigInt::from(1) << 20000) - 1, 1.into())
        .unwrap();
    assert!(e.rational_multiply(a, b).is_none());
    assert_eq!(Power::Constant(0).step(), ORDER);
    assert_eq!(Power::Constant(HALF).step(), HALF);
}

#[test]
fn dense_cyclotomic_products_match_literal_convolution_at_every_input() {
    for degree in [2usize, 4, 8] {
        for u in [false, true] {
            for v in [false, true] {
                let k = kernel();
                let mut e = Encoder::new(&k).unwrap();
                let stride = HALF / degree as u64;
                let mut a = e.literal(ratio(2, 3), 0, false).unwrap();
                let ap = e
                    .phase(&phase(
                        KernelVariable::InputKet(0),
                        BigRational::new((degree - 1).into(), (2 * degree).into()),
                    ))
                    .unwrap();
                let mut at = atom(&mut e, 1, 0);
                at.power = ap;
                a.push(at);
                let mut b = e.literal(ratio(-3, 5), 0, false).unwrap();
                let bp = e
                    .phase(&phase(
                        KernelVariable::InputBra(0),
                        BigRational::new(1.into(), (2 * degree).into()),
                    ))
                    .unwrap();
                let mut bt = atom(&mut e, 2, 0);
                bt.power = bp;
                b.push(bt);
                let mut q = e
                    .dense_product_query(vec![a, b], vec![vec![]], degree)
                    .unwrap();
                q.script = q.script.replace(
                    "(check-sat)",
                    &format!("(assert (= u0 {u}))\n(assert (= u1 {v}))\n(check-sat)"),
                );
                let pa = if u { (degree - 1) as u64 * stride } else { 0 };
                let pb = if v { stride } else { 0 };
                let mut expected = BTreeMap::new();
                for (x, c) in [(0, ratio(2, 3)), (pa, integer(1))] {
                    for (y, d) in [(0, ratio(-3, 5)), (pb, integer(2))] {
                        let p = (x + y) % ORDER;
                        let r = if p >= HALF { -(&c * d) } else { &c * d };
                        *expected.entry(p % HALF).or_insert_with(|| integer(0)) += r;
                    }
                }
                expected.retain(|_, r| *r != integer(0));
                if expected.is_empty() {
                    assert_eq!(status(&q), SolverStatus::Unsat);
                } else {
                    assert_eq!(
                        solve(&q).difference_coefficients,
                        expected.into_iter().collect::<Vec<_>>()
                    );
                }
            }
        }
    }
}
