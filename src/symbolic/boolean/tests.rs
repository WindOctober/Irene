use super::*;
use crate::symbolic::{PhaseCoefficient, PhasePolynomial};
use num_rational::BigRational;
use std::convert::Infallible;

fn v(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(i))
}
fn value(p: &BooleanPolynomial, bits: u64) -> bool {
    p.evaluate::<Infallible>(|v| match v {
        Variable::Path(i) => Ok(bits & (1u64 << i) != 0),
        _ => unreachable!(),
    })
    .unwrap()
}
fn complement_product(n: usize) -> BooleanPolynomial {
    (0..n).fold(BooleanPolynomial::one(), |p, i| p.and(&v(i).complement()))
}

#[test]
fn flattened_conjunction_preserves_composite_complement_cancellation() {
    let a = v(0).xor(&v(1));
    let b = v(2).and(&v(3));
    let ab = a.and(&b);
    assert!(BooleanPolynomial::and_all([a.clone(), b.clone(), ab.complement()]).is_zero());
    assert!(ab.complement().and(&a).and(&b).is_zero());
    // Partial overlap must not be mistaken for a contradiction.
    let partial = a.and(&ab.complement());
    for bits in 0..16 {
        assert_eq!(value(&partial, bits), value(&a, bits) && !value(&ab, bits));
    }
    assert!(!partial.is_zero());
}

#[test]
fn exponential_anf_stays_linear_and_refusal_preserves_the_expression() {
    let p = complement_product(60);
    let before = p.clone();
    assert!(p.storage_size() < 500);
    assert!(p.expanded_terms(65536).is_none());
    assert_eq!(p, before);
    assert!(value(&p, 0));
    for i in 0..60 {
        assert!(!value(&p, 1 << i));
    }
    assert!(p.to_string().len() < 12000);
}

#[test]
fn dag_evaluation_expansion_and_substitution_agree_exhaustively() {
    let base = complement_product(7); // 128 ANF terms; retained as a graph.
    let p = base.xor(&v(1).and(&v(2))).and(&v(6).xor(&v(7)));
    let terms = p.expanded_terms(2048).unwrap();
    let replacement = v(2).xor(&v(3).and(&v(4))).complement();
    let substituted = p.substitute(&Variable::Path(1), &replacement);
    for bits in 0..256 {
        let expanded = terms.iter().fold(false, |sum, m| {
            sum ^ m.variables().all(|v| {
                let Variable::Path(i) = v else { unreachable!() };
                bits & (1 << i) != 0
            })
        });
        assert_eq!(value(&p, bits), expanded);
        let rewritten_bits = (bits & !2) | (u64::from(value(&replacement, bits)) << 1);
        assert_eq!(value(&substituted, bits), value(&p, rewritten_bits));
    }
}

#[test]
fn substitution_shares_replacements_and_is_simultaneous() {
    let p = complement_product(50);
    let a = v(61).substitute(&Variable::Path(61), &p);
    let b = v(62).substitute(&Variable::Path(62), &p);
    assert!(std::sync::Arc::ptr_eq(&a.0, &p.0));
    assert!(std::sync::Arc::ptr_eq(&b.0, &p.0));
    assert!(a.and(&b).storage_size() <= p.storage_size());
    let flip = v(0).complement();
    assert_eq!(v(0).substitute(&Variable::Path(0), &flip), flip);
}

#[test]
fn rename_is_capture_free_on_shared_nodes() {
    let p = complement_product(7).xor(&v(7));
    let renamed = p.map_variables(|var| match var {
        Variable::Path(0) => v(7),
        Variable::Path(7) => v(0),
        _ => BooleanPolynomial::variable(var.clone()),
    });
    for bits in 0..256 {
        let swap = (bits & !129) | ((bits & 1) << 7) | ((bits & 128) >> 7);
        assert_eq!(value(&renamed, bits), value(&p, swap));
    }
}

#[test]
fn factored_rational_phases_preserve_exact_arithmetic_not_boolean_addition() {
    let p = complement_product(7).xor(&v(2));
    for denominator in [2, 3, 4, 8] {
        let c = BigRational::new(1.into(), denominator.into());
        let mut phase = PhasePolynomial::zero();
        phase.add_boolean(&p, PhaseCoefficient::rational(c.clone()));
        assert!(phase.storage_size() < 200);
        let expanded = phase.expanded_terms(16384).unwrap();
        for bits in 0..128 {
            let actual = expanded
                .iter()
                .filter(|(m, _)| {
                    m.variables().all(|v| {
                        let Variable::Path(i) = v else { unreachable!() };
                        bits & (1 << i) != 0
                    })
                })
                .fold(BigRational::from_integer(0.into()), |sum, (_, c)| {
                    sum + c.as_rational().unwrap()
                });
            let expected = if value(&p, bits) {
                c.clone()
            } else {
                BigRational::from_integer(0.into())
            };
            assert!((actual - expected).is_integer());
        }
    }
}

#[test]
fn large_phase_substitution_needs_no_arithmetic_expansion() {
    let p = complement_product(40);
    let mut phase = PhasePolynomial::zero();
    phase.add_boolean(
        &v(61),
        PhaseCoefficient::rational(BigRational::new(1.into(), 3.into())),
    );
    phase.substitute(&Variable::Path(61), &p);
    assert!(phase.storage_size() < 500);
    assert!(phase.expanded_terms(8192).is_none());
    assert_eq!(phase.selectors().next().unwrap().0, p);
    assert!(!phase.variables().contains(&Variable::Path(61)));
}

#[test]
fn successive_phase_substitutions_do_not_multiply_the_eager_term_budget() {
    let product = (0..20).fold(BooleanPolynomial::one(), |p, i| p.and(&v(i)));
    let mut phase = PhasePolynomial::zero();
    phase.add_boolean(
        &product,
        PhaseCoefficient::rational(BigRational::new(1.into(), 8.into())),
    );
    for i in 0..20 {
        phase.substitute(&Variable::Path(i), &v(i + 20).xor(&v(i + 40)));
        assert!(
            phase.selectors().count() < 400,
            "step {i}: {} selectors",
            phase.selectors().count()
        );
        assert!(
            phase.storage_size() < 10000,
            "step {i}: {} selectors, {} stored nodes",
            phase.selectors().count(),
            phase.storage_size()
        );
    }
    assert!(phase.expanded_terms(1024).is_none());
    assert!(
        phase
            .variables()
            .iter()
            .all(|v| matches!(v,Variable::Path(i) if *i >= 20))
    );
}

#[test]
fn wide_xor_cancellation_removes_false_output_dependencies_without_anf() {
    let f = (0..96).fold(BooleanPolynomial::zero(), |sum, i| {
        sum.xor(&v(i).and(&v(i + 100)))
    });
    let result = v(300).xor(&f).xor(&f);
    assert_eq!(result, v(300));
    assert_eq!(result.variables(), BTreeSet::from([Variable::Path(300)]));
    assert!(result.expanded_terms(1).is_some());
}

#[test]
fn graph_factoring_preserves_every_assignment() {
    let atoms = [v(0), v(1), v(2), v(0).xor(&v(1)), v(2).complement()];
    for a in &atoms {
        for b in &atoms {
            for c in &atoms {
                let source = a.and(b).xor(&a.and(c)).xor(b);
                let factored = source.factored();
                for bits in 0..8 {
                    assert_eq!(value(&source, bits), value(&factored, bits));
                }
            }
        }
    }
}

#[test]
fn smt_encoding_preserves_sharing_without_requesting_anf() {
    let p = complement_product(60);
    assert!(p.expanded_terms(65536).is_none());
    let text = p.smt_expression(|v| Some(v.to_string())).unwrap();
    assert!(text.len() < 20000);
    assert!(text.contains("(and "));
    assert!(p.smt_expression(|_| None).is_none());
}

#[test]
fn smt_graph_bindings_do_not_capture_free_variable_names() {
    let text = v(0)
        .xor(&v(1))
        .smt_expression(|variable| match variable {
            Variable::Path(0) => Some("irene_xag_0".to_owned()),
            Variable::Path(1) => Some("irene_xag__0".to_owned()),
            _ => None,
        })
        .unwrap();
    assert!(!text.contains("(let ((irene_xag_0 "));
    assert!(!text.contains("(let ((irene_xag__0 "));
    assert!(text.contains("(let ((irene_xag___0 "));
}

#[test]
fn wide_materialized_xor_has_no_admission_budget() {
    let terms: Vec<_> = (0..8192).map(|i| v(i).and(&v(i + 8192))).collect();
    let left = BooleanPolynomial::xor_all(terms.iter().cloned());
    let right = BooleanPolynomial::xor_all(terms.into_iter().rev().chain([v(20000)]));
    assert_eq!(left.xor(&right), v(20000));
    assert_eq!(right.xor(&left), v(20000));
}

#[test]
fn nested_factoring_cancels_dependencies_without_distributing_products() {
    let a = v(0);
    let b = v(1);
    let c = v(2);
    let d = v(3);
    let k = v(4);
    let nested = k.and(&a.and(&b.xor(&c)).xor(&a.and(&b.xor(&d))));
    let simplified = nested.factored();
    assert_eq!(simplified, k.and(&a).and(&c.xor(&d)));
    assert!(!simplified.variables().contains(&Variable::Path(1)));
    for bits in 0..32 {
        assert_eq!(value(&nested, bits), value(&simplified, bits));
    }
    let huge = BooleanPolynomial::and_all((100..160).map(|i| v(i).complement())).and(&nested);
    assert!(huge.expanded_terms(65536).is_none());
    assert!(huge.factored().storage_size() <= huge.storage_size());
}

#[test]
fn graph_factoring_preserves_all_assignments_of_shared_boolean_circuits() {
    for seed in 1..=96_u64 {
        let mut state = seed;
        let mut pool: Vec<_> = (0..6).map(v).chain([BooleanPolynomial::one()]).collect();
        for _ in 0..32 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let a = &pool[(state as usize) % pool.len()];
            let b = &pool[((state >> 32) as usize) % pool.len()];
            let next = match (state >> 16) % 3 {
                0 => a.xor(b),
                1 => a.and(b),
                _ => a.xor(&a.and(b)).complement(),
            };
            pool.push(next);
        }
        for original in pool.iter().skip(7) {
            let reduced = original.factored();
            for bits in 0..64 {
                assert_eq!(
                    value(original, bits),
                    value(&reduced, bits),
                    "seed={seed}, bits={bits}"
                );
            }
        }
    }
}

#[test]
fn normalized_node_cache_reuses_results_without_retaining_the_source_root() {
    let original = v(0).and(&v(1).xor(&v(2))).xor(&v(0).and(&v(1).xor(&v(3))));
    let source = std::sync::Arc::downgrade(&original.0);
    let reduced = original.factored();
    assert!(std::sync::Arc::ptr_eq(&reduced.0, &original.factored().0));
    drop(original);
    assert!(source.upgrade().is_none());

    let stable = v(0).xor(&v(1));
    let source = std::sync::Arc::downgrade(&stable.0);
    assert!(std::sync::Arc::ptr_eq(&stable.0, &stable.factored().0));
    drop(stable);
    assert!(
        source.upgrade().is_none(),
        "normal-form markers must not retain self"
    );
}

#[test]
fn populating_normalization_caches_does_not_change_ordered_keys() {
    let keys = (0..32)
        .map(|i| {
            v(i).and(&v(40).xor(&v(41)))
                .xor(&v(i).and(&v(40).xor(&v(42))))
        })
        .collect::<Vec<_>>();
    let set = keys.iter().cloned().collect::<BTreeSet<_>>();
    let before = set.iter().cloned().collect::<Vec<_>>();
    for key in keys.iter().rev() {
        key.factored();
    }
    assert_eq!(set.iter().cloned().collect::<Vec<_>>(), before);
    assert!(keys.iter().all(|key| set.contains(key)));
}
#[test]
fn shared_root_mapping_is_simultaneous_and_reuses_common_subgraphs() {
    let v = |i| BooleanPolynomial::variable(Variable::Path(i));
    let common = v(0).and(&v(1));
    let roots = vec![common.clone(), common.xor(&v(2)), common.clone()];
    // A swap would be destroyed by sequential substitution. Also check that
    // the replacement's existing source variable is not recursively mapped.
    let rename = |x: &Variable| match x {
        Variable::Path(0) => v(1),
        Variable::Path(1) => v(0).xor(&v(2)),
        _ => BooleanPolynomial::variable(x.clone()),
    };
    let actual = BooleanPolynomial::map_roots(&roots, rename);
    let expected: Vec<_> = roots.iter().map(|p| p.map_variables(rename)).collect();
    assert_eq!(actual, expected);
    assert!(std::sync::Arc::ptr_eq(&actual[0].0, &actual[2].0));
    for bits in 0..8 {
        let eval = |p: &BooleanPolynomial| {
            p.evaluate::<std::convert::Infallible>(|x| {
                let Variable::Path(i) = x else { unreachable!() };
                Ok(bits & (1 << i) != 0)
            })
            .unwrap()
        };
        assert_eq!(
            eval(&actual[0]),
            (bits & 2 != 0) && ((bits & 1 != 0) ^ (bits & 4 != 0))
        );
        assert_eq!(eval(&actual[1]), eval(&actual[0]) ^ (bits & 4 != 0));
    }
}
