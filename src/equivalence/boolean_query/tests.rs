use super::*;

fn q(i: usize) -> Qubit {
    Qubit {
        register: crate::ir::SymbolId(7),
        index: i,
    }
}
fn x(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Input(q(i)))
}
fn positions(n: usize) -> BTreeMap<Qubit, usize> {
    (0..n).map(|i| (q(i), i)).collect()
}

#[test]
fn output_miter_declares_one_input_namespace_and_preserves_shared_roots() {
    let shared = x(0).and(&x(1));
    let query = boolean_miter(&[shared.clone(), shared.xor(&x(0))], &positions(2), "x").unwrap();
    assert_eq!(query.matches("(declare-fun x").count(), 2);
    assert!(!query.contains("(declare-fun z"));
    assert!(!query.contains("get-value"));
    assert!(query.contains("(check-sat)"));
}

#[test]
fn injectivity_declares_independent_inputs_and_handles_empty_output_vectors() {
    let query = injectivity_query(&[x(0), x(1)], &positions(2)).unwrap();
    assert_eq!(query.matches("(declare-fun x").count(), 2);
    assert_eq!(query.matches("(declare-fun z").count(), 2);
    assert!(query.contains("(xor x0 z0)"));
    // The Boolean encoder may wrap even a variable in a shared expression;
    // formula semantics are checked against truth tables in the solver test.
    assert!(query.contains("(= "));
    assert!(
        injectivity_query(&[], &positions(0))
            .unwrap()
            .contains("(and false true)")
    );
    assert!(
        boolean_miter(&[], &positions(0), "x")
            .unwrap()
            .contains("(assert false)")
    );
}

#[test]
fn path_variables_and_unknown_inputs_are_refused() {
    for p in [x(2), BooleanPolynomial::variable(Variable::Path(0))] {
        assert!(boolean_miter(std::slice::from_ref(&p), &positions(2), "x").is_none());
        assert!(injectivity_query(&[p], &positions(2)).is_none());
    }
}


#[test]
fn actual_parsed_outputs_use_canonical_inputs_for_both_sides() {
    use crate::{
        equivalence::{EquivalenceConfig, prepare_comparison},
        frontend::openqasm3,
    };
    let left = openqasm3::parse_str(
        "OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] a; cx a[0],a[1];",
        "left.qasm",
    )
    .unwrap();
    let right = openqasm3::parse_str(
        "OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] b; cx b[0],b[1];",
        "right.qasm",
    )
    .unwrap();
    let p = prepare_comparison(
        &left,
        &right,
        &EquivalenceConfig::positional(&left, &right).unwrap(),
    )
    .unwrap();
    let pos = p
        .left
        .hps
        .input
        .quantum
        .keys()
        .cloned()
        .enumerate()
        .map(|(i, q)| (q, i))
        .collect();
    let diffs = p.left.terminals[0]
        .outputs
        .iter()
        .zip(&p.right.terminals[0].outputs)
        .map(|(a, b)| a.value.xor(&b.value))
        .collect::<Vec<_>>();
    assert!(diffs.iter().all(BooleanPolynomial::is_zero));
    assert!(boolean_miter(&diffs, &pos, "x").is_some());
    let outputs = p.left.terminals[0]
        .outputs
        .iter()
        .map(|o| o.value.clone())
        .collect::<Vec<_>>();
    assert!(injectivity_query(&outputs, &pos).is_some());
}

fn polynomial(mask: usize) -> BooleanPolynomial {
    [BooleanPolynomial::one(), x(0), x(1), x(0).and(&x(1))]
        .iter()
        .enumerate()
        .filter(|(i, _)| mask & (1 << i) != 0)
        .fold(BooleanPolynomial::zero(), |p, (_, term)| p.xor(term))
}

// Independent two-input ANF truth table; does not call graph evaluation.
fn value(polynomial: usize, input: usize) -> bool {
    let terms = 1 | ((input & 1) << 1) | ((input & 2) << 1) | if input == 3 { 8 } else { 0 };
    (polynomial & terms).count_ones() % 2 != 0
}

#[test]
#[ignore = "requires external Z3; checks generated formulas against complete truth tables"]
fn generated_queries_match_all_two_input_maps_and_fixed_assignments() {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };
    // One small solver process per map avoids pipe backpressure from a large
    // monolithic script, while testing every fixed pair of assignments.
    for a in 0..16 {
        for b in 0..16 {
            let mut script = String::new();
            let mut expected = Vec::new();
            let difference =
                boolean_miter(&[polynomial(a).xor(&polynomial(b))], &positions(2), "x").unwrap();
            script.push_str(&difference.replace("(check-sat)\n", ""));
            for input in 0..4 {
                script.push_str("(push 1)\n");
                for i in 0..2 {
                    script.push_str(&format!("(assert (= x{i} {}))\n", input & (1 << i) != 0));
                }
                script.push_str("(check-sat)\n(pop 1)\n");
                expected.push(if value(a, input) != value(b, input) {
                    "sat"
                } else {
                    "unsat"
                });
            }
            script.push_str("(reset)\n");
            let collision =
                injectivity_query(&[polynomial(a), polynomial(b)], &positions(2)).unwrap();
            script.push_str(&collision.replace("(check-sat)\n", ""));
            for l in 0..4 {
                for r in 0..4 {
                    script.push_str("(push 1)\n");
                    for (name, input) in [("x", l), ("z", r)] {
                        for i in 0..2 {
                            script.push_str(&format!(
                                "(assert (= {name}{i} {}))\n",
                                input & (1 << i) != 0
                            ));
                        }
                    }
                    script.push_str("(check-sat)\n(pop 1)\n");
                    let sat = l != r && value(a, l) == value(a, r) && value(b, l) == value(b, r);
                    expected.push(if sat { "sat" } else { "unsat" });
                }
            }
            let mut child = Command::new("z3")
                .args(["-in", "-T:10"])
                .stdin(Stdio::piped())
                .stdout(Stdio::piped())
                .stderr(Stdio::piped())
                .spawn()
                .expect("install Z3 to run this explicit test");
            child
                .stdin
                .take()
                .unwrap()
                .write_all(script.as_bytes())
                .unwrap();
            let result = child.wait_with_output().unwrap();
            assert!(
                result.status.success(),
                "{}",
                String::from_utf8_lossy(&result.stderr)
            );
            let output = String::from_utf8(result.stdout).unwrap();
            assert_eq!(
                output.lines().collect::<Vec<_>>(),
                expected,
                "functions {a} {b}"
            );
        }
    }
}
