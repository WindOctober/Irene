use super::*;

fn bit(v: &KernelVariable) -> KernelBooleanPolynomial {
    KernelBooleanPolynomial::variable(v.clone())
}

fn unchanged(a: &WorkingTerm, b: &WorkingTerm) {
    assert_eq!(a.paths, b.paths);
    assert_eq!(a.constraints, b.constraints);
    assert_eq!(a.coefficient, b.coefficient);
    assert_eq!(a.phase, b.phase);
}

fn boolean(row: &KernelBooleanPolynomial, point: &BTreeMap<KernelVariable, bool>) -> bool {
    row.terms()
        .fold(false, |a, m| a ^ m.variables().all(|v| point[v]))
}

fn scalar(s: &KernelScalar, point: &BTreeMap<KernelVariable, bool>) -> BigRational {
    match s {
        KernelScalar::Rational(r) => r.clone(),
        KernelScalar::Select {
            condition,
            when_true,
            when_false,
        } => scalar(
            if boolean(condition, point) {
                when_true
            } else {
                when_false
            },
            point,
        ),
        _ => panic!("unsupported test scalar"),
    }
}

// Independent literal finite entry in Q[z]/(z^4+1). No production
// substitution/reduction, no numeric phase sampling or verdict oracle.
fn entry(source: &WorkingTerm, free: &BTreeMap<KernelVariable, bool>) -> [BigRational; 4] {
    let mut sum = std::array::from_fn(|_| integer(0));
    for bits in 0..1usize << source.paths.len() {
        let mut point = free.clone();
        for (i, v) in source.paths.iter().enumerate() {
            point.insert(v.clone(), bits & (1 << i) != 0);
        }
        if source.constraints.iter().any(|r| boolean(r, &point)) {
            continue;
        }
        let mut power = integer(0);
        for (m, c) in source.phase.terms() {
            if m.variables().all(|v| point[v]) {
                power += c.as_rational().unwrap() * integer(8);
            }
        }
        assert!(power.is_integer());
        let power = i64::try_from(power.to_integer()).unwrap().rem_euclid(8) as usize;
        sum[power % 4] +=
            scalar(&source.coefficient, &point) * integer(if power < 4 { 1 } else { -1 });
    }
    sum
}

fn fixture() -> (WorkingTerm, KernelVariable, KernelBooleanPolynomial) {
    let v = KernelVariable::PathKet { term: 0, path: 0 };
    let b = KernelVariable::PathBra { term: 0, path: 0 };
    let a = KernelVariable::InputKet(0);
    let replacement = bit(&a).xor(&bit(&b));
    (
        WorkingTerm {
            paths: BTreeSet::from([v.clone(), b]),
            constraints: vec![bit(&v).xor(&replacement)],
            coefficient: KernelScalar::Rational(integer(1)),
            phase: KernelPhasePolynomial::default(),
        },
        v,
        replacement,
    )
}

#[test]
fn affine_pair_preserves_all_weighted_entries_and_cross_output_collisions() {
    let (base, v, replacement) = fixture();
    let w = KernelVariable::PathKet { term: 1, path: 0 };
    let a = KernelVariable::InputKet(0);
    let b = KernelVariable::PathBra { term: 0, path: 0 };
    let x = KernelVariable::QuantumOutputBra(0);
    let vars = [a.clone(), b, x.clone()];
    for seed in 0..64 {
        let mut source = base.clone();
        source.paths.insert(w.clone());
        source.constraints.push(bit(&w).xor(&replacement));
        source.constraints.push(bit(&v).and(&bit(&w)).xor(&bit(&x)));
        source.coefficient = KernelScalar::Select {
            condition: bit(&v),
            when_true: Box::new(KernelScalar::Select {
                condition: bit(&w),
                when_true: Box::new(KernelScalar::Rational(integer(-3))),
                when_false: Box::new(KernelScalar::Rational(integer(2))),
            }),
            when_false: Box::new(KernelScalar::Rational(integer(seed % 5))),
        };
        for mask in 0..8 {
            let rest = vars
                .iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, v)| v.clone())
                .collect::<Vec<_>>();
            for (binder, c) in [
                (Some(v.clone()), (seed + mask * 3 + 1) % 8),
                (
                    Some(w.clone()),
                    if seed % 2 == 0 {
                        -(seed + mask * 3 + 1) % 8
                    } else {
                        (seed + mask + 1) % 8
                    },
                ),
                (None, (seed + mask * 5) % 8),
            ] {
                source.phase.add_term(
                    KernelMonomial::from_variables(rest.iter().cloned().chain(binder)),
                    PhaseCoefficient::rational(ratio(c, 8)),
                );
            }
        }
        source.phase.index_occurrences();
        let before = source.clone();
        assert!(apply(&mut source, &v, &replacement, &mut { WORK_CELLS }));
        assert!(!source.paths.contains(&v) && !source.paths.contains(&w));
        let mut generic = before.clone();
        generic.substitute(&v, &replacement);
        generic.paths.remove(&v);
        generic.substitute(&w, &replacement);
        generic.paths.remove(&w);
        unchanged(&source, &generic);
        for bits in 0..4 {
            let free = BTreeMap::from([(a.clone(), bits & 1 != 0), (x.clone(), bits & 2 != 0)]);
            assert_eq!(entry(&before, &free), entry(&source, &free));
        }
        // Even if only enough work remains for the primary, it is a
        // COMPLETE single substitution, not a partially applied pair.
        let mut allowance = WORK_CELLS;
        let mut stage = "test";
        let primary = plan(&before, &v, &replacement, &mut allowance, &mut stage).unwrap();
        assert!(primary.partner.is_some());
        let primary_cost = WORK_CELLS - allowance;
        let mut counters = primary;
        let (partner, rhs) = counters.partner.take().unwrap();
        assert!(
            extend_pair(
                &before,
                &mut counters,
                &partner,
                &rhs,
                &mut allowance,
                &mut stage
            )
            .is_some()
        );
        assert_eq!(counters.final_terms, generic.phase.term_count());
        assert_eq!(
            counters.final_cells,
            generic
                .phase
                .terms()
                .map(|(m, _)| 1 + m.variables().count())
                .sum::<usize>()
        );
        let mut single = before.clone();
        assert!(apply(&mut single, &v, &replacement, &mut { primary_cost }));
        let mut expected = before;
        expected.substitute(&v, &replacement);
        expected.paths.remove(&v);
        unchanged(&single, &expected);
    }
}

#[test]
fn affine_pair_rejects_dependent_or_overlapping_proposals_and_keeps_primary() {
    let (base, v, replacement) = fixture();
    let w = KernelVariable::PathKet { term: 1, path: 0 };
    let x = KernelVariable::InputKet(7);
    for mode in 0..4 {
        let mut source = base.clone();
        source.paths.insert(w.clone());
        source.constraints.push(bit(&w).xor(&if mode == 0 {
            bit(&v).xor(&bit(&x))
        } else {
            replacement.clone()
        }));
        source.phase.add_term(
            KernelMonomial::variable(w.clone()),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
        if mode == 1 {
            source.phase.add_term(
                KernelMonomial::from_variables([v.clone(), w.clone()]),
                PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
        if mode == 2 {
            // First plan is valid; the second touched coefficient is not
            // admitted. A failed SECOND plan must not corrupt the first.
            source.phase.add_term(
                KernelMonomial::from_variables([w.clone(), x.clone()]),
                PhaseCoefficient::rational(BigRational::new(
                    BigInt::from(1),
                    BigInt::from(1) << 257,
                )),
            );
        }
        if mode == 3 {
            source.paths.remove(&w); // late ownership refuses EVERYTHING.
            let before = source.clone();
            assert!(!apply(&mut source, &v, &replacement, &mut { WORK_CELLS }));
            unchanged(&source, &before);
            continue;
        }
        let mut expected = source.clone();
        expected.substitute(&v, &replacement);
        expected.paths.remove(&v);
        assert!(apply(&mut source, &v, &replacement, &mut { WORK_CELLS }));
        unchanged(&source, &expected);
    }
}

#[test]
fn affine_pair_constants_distinct_rhs_and_late_guard_failure_are_complete() {
    let (base, v, replacement) = fixture();
    let w = KernelVariable::PathKet { term: 1, path: 0 };
    let a = KernelVariable::InputKet(0);
    let b = KernelVariable::PathBra { term: 0, path: 0 };
    let x = KernelVariable::InputBra(0);
    for rhs in [
        bit(&b).complement(),
        bit(&x).complement(),
        bit(&a).xor(&bit(&x)),
    ] {
        let mut source = base.clone();
        source.paths.insert(w.clone());
        source.constraints.push(bit(&w).xor(&rhs));
        for (vars, c) in [
            (vec![v.clone(), a.clone()], 1),
            (vec![w.clone(), a.clone()], 3),
            (vec![w.clone(), b.clone()], 2),
        ] {
            source.phase.add_term(
                KernelMonomial::from_variables(vars),
                PhaseCoefficient::rational(ratio(c, 8)),
            );
        }
        let before = source.clone();
        assert!(apply(&mut source, &v, &replacement, &mut { WORK_CELLS }));
        assert!(!source.paths.contains(&w));
        let mut expected = before.clone();
        expected.substitute(&v, &replacement);
        expected.paths.remove(&v);
        expected.substitute(&w, &rhs);
        expected.paths.remove(&w);
        unchanged(&source, &expected);
        for bits in 0..4 {
            let free = BTreeMap::from([(a.clone(), bits & 1 != 0), (x.clone(), bits & 2 != 0)]);
            assert_eq!(entry(&source, &free), entry(&before, &free));
        }
    }

    let mut source = base;
    source.paths.insert(w.clone());
    source.constraints.push(bit(&w).xor(&replacement));
    source.phase.add_term(
        KernelMonomial::variable(w.clone()),
        PhaseCoefficient::rational(ratio(1, 8)),
    );
    source
        .constraints
        .push(KernelBooleanPolynomial::from_monomials((0..60000).map(
            |i| KernelMonomial::from_variables([w.clone(), KernelVariable::QuantumOutputKet(i)]),
        )));
    let mut expected = source.clone();
    expected.substitute(&v, &replacement);
    expected.paths.remove(&v);
    assert!(apply(&mut source, &v, &replacement, &mut { WORK_CELLS }));
    unchanged(&source, &expected); // Second guard exceeds original100000term bound.
}

#[test]
fn affine_owned_boolean_construction_toggles_every_duplicate() {
    let a = KernelMonomial::variable(KernelVariable::InputKet(0));
    let b = KernelMonomial::variable(KernelVariable::InputBra(0));
    let monomials = [KernelMonomial::one(), a.clone(), b.clone(), a.multiply(&b)];
    for digits in 0..256usize {
        let mut supplied = Vec::new();
        let mut expected = KernelBooleanPolynomial::zero();
        for (i, m) in monomials.iter().enumerate() {
            let count = (digits >> (2 * i)) & 3;
            supplied.extend(std::iter::repeat_n(m.clone(), count));
            if count % 2 != 0 {
                expected = expected.xor(&KernelBooleanPolynomial::from_monomial(m.clone()));
            }
        }
        supplied.reverse();
        assert_eq!(KernelBooleanPolynomial::from_monomials(supplied), expected);
    }
}

#[test]
fn affine_pair_genuine_secondary_phase_overflow_keeps_complete_primary() {
    let (mut source, v, replacement) = fixture();
    let w = KernelVariable::PathKet { term: 1, path: 0 };
    source.paths.insert(w.clone());
    source.constraints.push(bit(&w).xor(&replacement));
    for i in 0..20000 {
        source.phase.add_term(
            KernelMonomial::from_variables([w.clone(), KernelVariable::QuantumOutputKet(i)]),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    for i in 0..50000 {
        source.phase.add_term(
            KernelMonomial::variable(KernelVariable::InputBra(i)),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    let mut stage = "test";
    let mut work = WORK_CELLS * 10; // TEST only: isolate unchanged output cap.
    let mut primary = plan(&source, &v, &replacement, &mut work, &mut stage).unwrap();
    assert!(
        extend_pair(
            &source,
            &mut primary,
            &w,
            &replacement,
            &mut work,
            &mut stage
        )
        .is_none()
    );
    assert_eq!(stage, "pair-output-cap");
    let mut expected = source.clone();
    expected.substitute(&v, &replacement);
    expected.paths.remove(&v);
    assert!(apply(&mut source, &v, &replacement, &mut {
        WORK_CELLS * 10
    }));
    unchanged(&source, &expected);
}

#[test]
fn affine_pair_reserves_primary_keys_before_secondary_delta_construction() {
    let (mut source, v, replacement) = fixture();
    let w = KernelVariable::PathKet { term: 1, path: 0 };
    source.paths.insert(w.clone());
    source.constraints.push(bit(&w).xor(&replacement));
    for (binder, start, end) in [(&v, 0, 21000), (&w, 21000, 22000)] {
        for i in start..end {
            source.phase.add_term(
                KernelMonomial::from_variables([
                    binder.clone(),
                    KernelVariable::QuantumOutputKet(i),
                ]),
                PhaseCoefficient::rational(ratio(1, 8)),
            );
        }
    }
    let mut work = WORK_CELLS * 10; // TEST only: isolate combined storage.
    let mut stage = "test";
    let mut primary = plan(&source, &v, &replacement, &mut work, &mut stage).unwrap();
    assert_eq!(primary.updates.term_count(), 63000);
    let updates = primary.updates.clone();
    assert!(
        extend_pair(
            &source,
            &mut primary,
            &w,
            &replacement,
            &mut work,
            &mut stage
        )
        .is_none()
    );
    assert_eq!(stage, "pair-phase-delta");
    assert_eq!(primary.updates, updates);
    assert_eq!(primary.final_terms, 64000);
    assert!(primary.cancellations.is_empty());
}

#[test]
fn affine_collision_substitution_preserves_complete_weighted_entries() {
    let (base, v, replacement) = fixture();
    let a = KernelVariable::InputKet(0);
    let x = KernelVariable::QuantumOutputBra(0);
    let b = KernelVariable::PathBra { term: 0, path: 0 };
    let w = KernelVariable::PathBra { term: 0, path: 1 };
    let vars = [v.clone(), a.clone(), b, x.clone()];
    for seed in 0..64 {
        let mut source = base.clone();
        source.paths.insert(w.clone());
        source.constraints.push(bit(&v).and(&bit(&w)).xor(&bit(&x)));
        source.coefficient = KernelScalar::Select {
            condition: bit(&v),
            when_true: Box::new(KernelScalar::Rational(integer(seed % 5 - 2))),
            when_false: Box::new(KernelScalar::Rational(integer(3))),
        };
        for mask in 0..16 {
            source.phase.add_term(
                KernelMonomial::from_variables(
                    vars.iter()
                        .enumerate()
                        .filter(|(i, _)| mask & (1 << i) != 0)
                        .map(|(_, v)| v.clone()),
                ),
                PhaseCoefficient::rational(ratio((seed * (mask + 3) + mask * mask) % 8, 8)),
            );
        }
        if seed % 2 == 0 {
            source.phase.index_occurrences();
        }
        let before = source.clone();
        let mut work = WORK_CELLS;
        assert!(apply(&mut source, &v, &replacement, &mut work));
        assert!(!source.paths.contains(&v));
        assert!(source.paths.contains(&w));
        let mut generic = before.clone();
        generic.substitute(&v, &replacement);
        generic.paths.remove(&v);
        unchanged(&source, &generic);
        for bits in 0..4 {
            let free = BTreeMap::from([(a.clone(), bits & 1 != 0), (x.clone(), bits & 2 != 0)]);
            assert_eq!(entry(&before, &free), entry(&source, &free));
        }
        // Every insufficient allowance refuses without a source mutation.
        let cost = WORK_CELLS - work;
        for limit in [0, cost / 2, cost - 1] {
            let mut refused = before.clone();
            assert!(!apply(&mut refused, &v, &replacement, &mut { limit }));
            unchanged(&before, &refused);
        }
    }
}

#[test]
fn affine_collision_refusals_preserve_late_guards_ownership_and_scalar_domains() {
    let (base, v, replacement) = fixture();
    let mut source = base.clone();
    source.constraints.clear();
    assert!(!apply(
        &mut source,
        &v,
        &replacement,
        &mut WORK_CELLS.clone()
    ));
    unchanged(
        &source,
        &WorkingTerm {
            constraints: vec![],
            ..base.clone()
        },
    );
    for scalar in [
        KernelScalar::Inverse(Box::new(KernelScalar::Rational(integer(0)))),
        KernelScalar::Select {
            condition: KernelBooleanPolynomial::zero(),
            when_true: Box::new(KernelScalar::Select {
                condition: bit(&KernelVariable::PathKet { term: 99, path: 99 }),
                when_true: Box::new(KernelScalar::Rational(integer(1))),
                when_false: Box::new(KernelScalar::Rational(integer(2))),
            }),
            when_false: Box::new(KernelScalar::Rational(integer(1))),
        },
    ] {
        let mut source = WorkingTerm {
            coefficient: scalar,
            ..base.clone()
        };
        let before = source.clone();
        assert!(!apply(&mut source, &v, &replacement, &mut { WORK_CELLS }));
        unchanged(&source, &before);
    }
    let missing = KernelVariable::PathKet { term: 7, path: 9 };
    for late_phase in [false, true] {
        let mut source = base.clone();
        if late_phase {
            source.phase.add_term(
                KernelMonomial::variable(missing.clone()),
                PhaseCoefficient::rational(ratio(1, 8)),
            );
        } else {
            source.constraints.push(bit(&missing));
        }
        let before = source.clone();
        assert!(!apply(&mut source, &v, &replacement, &mut { WORK_CELLS }));
        unchanged(&source, &before);
    }
    let mut source = base.clone();
    source.phase.add_term(
        KernelMonomial::variable(v.clone()),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(1) << 257)),
    );
    let before = source.clone();
    assert!(!apply(&mut source, &v, &replacement, &mut { WORK_CELLS }));
    unchanged(&source, &before);
    assert!(!apply(
        &mut source,
        &KernelVariable::InputKet(0),
        &replacement,
        &mut { WORK_CELLS }
    ));
}

#[test]
fn affine_collision_constant_and_bound_free_replacements_keep_vacuous_counts() {
    let (base, v, _) = fixture();
    let a = KernelVariable::InputKet(0);
    let x = KernelVariable::QuantumOutputBra(0);
    let b = KernelVariable::PathBra { term: 0, path: 0 };
    let w = KernelVariable::PathBra { term: 0, path: 1 };
    for replacement in [
        KernelBooleanPolynomial::one().xor(&bit(&b)),
        KernelBooleanPolynomial::one().xor(&bit(&x)),
        bit(&a).xor(&bit(&x)),
        bit(&b).xor(&bit(&w)),
    ] {
        let mut source = base.clone();
        source.paths.insert(w.clone());
        source.constraints = vec![bit(&v).xor(&replacement), bit(&v).and(&bit(&x))];
        source.coefficient = KernelScalar::Select {
            condition: bit(&v),
            when_true: Box::new(KernelScalar::Rational(integer(-2))),
            when_false: Box::new(KernelScalar::Rational(integer(3))),
        };
        for (vars, c) in [
            (vec![v.clone()], 1),
            (vec![v.clone(), b.clone()], 2),
            (vec![v.clone(), x.clone()], 3),
            (vec![v.clone(), b.clone(), x.clone()], 5),
        ] {
            source.phase.add_term(
                KernelMonomial::from_variables(vars),
                PhaseCoefficient::rational(ratio(c, 8)),
            );
        }
        let before = source.clone();
        assert!(apply(&mut source, &v, &replacement, &mut { WORK_CELLS }));
        assert_eq!(source.paths, BTreeSet::from([b.clone(), w.clone()]));
        for bits in 0..4 {
            let free = BTreeMap::from([(a.clone(), bits & 1 != 0), (x.clone(), bits & 2 != 0)]);
            assert_eq!(entry(&before, &free), entry(&source, &free));
        }
    }
}

#[test]
fn affine_collision_crosses_loose_bound_without_raising_global_cap() {
    let (mut source, v, replacement) = fixture();
    let a = KernelVariable::InputKet(0);
    let b = KernelVariable::PathBra { term: 0, path: 0 };
    let mut expected = KernelPhasePolynomial::default();
    for i in 0..80000 {
        expected.add_term(
            KernelMonomial::variable(KernelVariable::InputBra(i)),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    source.phase = expected.clone();
    for i in 0..4000 {
        let z = KernelVariable::QuantumOutputKet(i);
        for (vars, c) in [
            (vec![v.clone(), z.clone()], ratio(1, 8)),
            (vec![a.clone(), z.clone()], ratio(-1, 8)),
            (vec![b.clone(), z.clone()], ratio(-1, 8)),
            (vec![a.clone(), b.clone(), z], ratio(1, 4)),
        ] {
            source.phase.add_term(
                KernelMonomial::from_variables(vars),
                PhaseCoefficient::rational(c),
            );
        }
    }
    assert_eq!(source.phase.term_count(), 96000);
    assert!(!source.substitution_within_budget(&v, &replacement));
    let whole_source = source.clone();
    assert!(apply(&mut source, &v, &replacement, &mut { WORK_CELLS }));
    assert_eq!(source.phase, expected);
    let Reduction::Exact(result) = reduce_working_term(whole_source) else {
        panic!("complete enclosing reduction must preserve the exact rewrite");
    };
    assert_eq!(result.phase, expected);
    assert!(result.constraints.is_empty());
    assert_eq!(result.coefficient, KernelScalar::Rational(integer(2)));

    // Genuine output expansion beyond the original global cap still refuses.
    let (mut source, v, replacement) = fixture();
    source.phase = expected;
    for i in 0..10000 {
        source.phase.add_term(
            KernelMonomial::from_variables([v.clone(), KernelVariable::QuantumOutputKet(i)]),
            PhaseCoefficient::rational(ratio(1, 8)),
        );
    }
    let before = source.clone();
    // Use a larger TEST-only work allowance to isolate the unchanged output
    // term limit rather than the production work refusal.
    assert!(!apply(&mut source, &v, &replacement, &mut {
        WORK_CELLS * 10
    }));
    unchanged(&source, &before);
}
