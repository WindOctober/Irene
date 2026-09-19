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

fn reference_circuits() -> Vec<(BooleanPolynomial, u16)> {
    let mut pool = vec![
        (v(0), 0xaaaa),
        (v(1), 0xcccc),
        (v(2), 0xf0f0),
        (v(3), 0xff00),
        (BooleanPolynomial::zero(), 0),
        (BooleanPolynomial::one(), u16::MAX),
    ];
    for i in 0..64 {
        let (a, av) = &pool[(i * 7 + 1) % pool.len()];
        let (b, bv) = &pool[(i * 11 + 3) % pool.len()];
        let next = match i % 3 {
            0 => (a.xor(b), av ^ bv),
            1 => (a.and(b), av & bv),
            _ => (a.complement(), !av),
        };
        pool.push(next);
    }
    pool
}

#[test]
fn shared_circuits_agree_with_independent_truth_tables() {
    for (p, table) in reference_circuits() {
        for bits in 0..16 {
            assert_eq!(value(&p, bits), table & (1 << bits) != 0);
        }
    }
}

#[test]
#[ignore = "requires the Bitwuzla executable on PATH"]
fn bitwuzla_checks_graph_encoding_against_independent_truth_tables() {
    use std::io::Write;
    use std::process::{Command, Stdio};
    // Deliberately use a name that collides with the encoder's default prefix.
    let names = ["irene_xag_0", "b", "c", "d"];
    let mut query = String::from("(set-logic QF_BV)\n");
    for name in names {
        query.push_str(&format!("(declare-fun {name} () Bool)\n"));
    }
    let mut differences = Vec::new();
    for (p, table) in reference_circuits() {
        let encoded = p
            .smt_expression(|variable| {
                let Variable::Path(i) = variable else {
                    return None;
                };
                Some(names[*i].to_owned())
            })
            .unwrap();
        let minterms = (0..16)
            .filter(|bits| table & (1 << bits) != 0)
            .map(|bits| {
                let literals = names
                    .iter()
                    .enumerate()
                    .map(|(i, name)| {
                        if bits & (1 << i) != 0 {
                            name.to_string()
                        } else {
                            format!("(not {name})")
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("(and {literals})")
            })
            .collect::<Vec<_>>();
        let reference = if minterms.is_empty() {
            "false".to_owned()
        } else if minterms.len() == 1 {
            minterms[0].clone()
        } else {
            format!("(or {})", minterms.join(" "))
        };
        differences.push(format!("(xor {encoded} {reference})"));
    }
    for i in 0..60 {
        query.push_str(&format!("(declare-fun w{i} () Bool)\n"));
    }
    let p = complement_product(60);
    assert!(p.expanded_terms(1024).is_none());
    let encoded = p
        .smt_expression(|variable| {
            let Variable::Path(i) = variable else {
                return None;
            };
            Some(format!("w{i}"))
        })
        .unwrap();
    let reference = (0..60)
        .map(|i| format!("(not w{i})"))
        .collect::<Vec<_>>()
        .join(" ");
    differences.push(format!("(xor {encoded} (and {reference}))"));
    query.push_str(&format!(
        "(assert (or {}))\n(check-sat)\n",
        differences.join(" ")
    ));
    let mut child = Command::new("bitwuzla")
        .args(["--time-limit", "10000"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("Bitwuzla is required for this explicitly selected test");
    child
        .stdin
        .take()
        .unwrap()
        .write_all(query.as_bytes())
        .unwrap();
    let result = child.wait_with_output().unwrap();
    assert!(
        result.status.success(),
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(
        String::from_utf8_lossy(&result.stdout).trim(),
        "unsat",
        "{}",
        String::from_utf8_lossy(&result.stderr)
    );
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
