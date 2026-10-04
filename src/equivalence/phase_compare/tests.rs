use super::*;
use crate::symbolic::PhaseCoefficient;

fn r(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}
fn q(i: usize) -> Qubit {
    Qubit {
        register: crate::ir::SymbolId(4),
        index: i,
    }
}
fn x(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Input(q(i)))
}
fn positions() -> BTreeMap<Qubit, usize> {
    [(q(0), 0), (q(1), 1)].into()
}
fn bindings(mask: usize) -> BTreeMap<Variable, bool> {
    (0..2)
        .map(|i| (Variable::Input(q(i)), mask & (1 << i) != 0))
        .collect()
}
fn phase(terms: &[(BooleanPolynomial, BigRational)]) -> PhasePolynomial {
    let mut p = PhasePolynomial::zero();
    for (selector, coefficient) in terms {
        p.add_boolean(selector, PhaseCoefficient::rational(coefficient.clone()));
    }
    p
}

#[test]
fn differences_cancel_and_normalize_negative_and_whole_turns_exactly() {
    let left = phase(&[
        (x(0), r(1, 3)),
        (x(1), r(-1, 4)),
        (BooleanPolynomial::one(), r(7, 6)),
    ]);
    let right = phase(&[
        (x(0), r(1, 3)),
        (x(1), r(1, 4)),
        (BooleanPolynomial::one(), r(1, 6)),
    ]);
    let delta = rational_phase_difference(&left, &right).unwrap();
    assert_eq!(delta, [(x(1), r(1, 2))].into());
    assert!(rational_phase_difference(&left, &left).unwrap().is_empty());
    for mask in 0..4 {
        assert_eq!(
            evaluate_phase(&delta, &bindings(mask)),
            if mask & 2 == 0 { r(0, 1) } else { r(1, 2) }
        );
    }
}

#[test]
fn constant_global_phase_needs_no_variation_query() {
    let p = [(BooleanPolynomial::one(), r(1, 4))].into();
    assert!(phase_variation_query(&p, &positions()).is_none());
    for mask in 0..4 {
        assert_eq!(evaluate_phase(&p, &bindings(mask)), r(1, 4));
    }
    assert!(phase_variation_query(&RationalPhase::new(), &positions()).is_none());
}

#[test]
fn fse_missing_bindings_default_to_false_and_foreign_query_variables_refuse() {
    let p = [(x(0).and(&x(1)), r(1, 3))].into();
    let incomplete = [(Variable::Input(q(0)), false)].into();
    assert_eq!(evaluate_phase(&p, &incomplete), r(0, 1));
    let foreign = [(x(2), r(1, 3))].into();
    assert!(phase_variation_query(&foreign, &positions()).is_none());
    let path = [(BooleanPolynomial::variable(Variable::Path(0)), r(1, 3))].into();
    assert!(phase_variation_query(&path, &positions()).is_none());
}

#[test]
fn nonrational_phase_is_not_approximated_even_if_both_sides_match() {
    use crate::ir::{AstIdGenerator, NumericExprKind};
    let mut ids = AstIdGenerator::default();
    let angle = ids.node(NumericExprKind::Rational(r(1, 10)));
    let mut p = PhasePolynomial::zero();
    p.add_boolean(&x(0), PhaseCoefficient::angle(angle, r(1, 1)));
    assert!(rational_phase_difference(&p, &p).is_none());
}

#[test]
fn common_denominator_and_width_cover_the_entire_unreduced_sum() {
    let p = [(x(0), r(5, 6)), (x(1), r(5, 6)), (x(0).xor(&x(1)), r(5, 6))].into();
    let query = phase_variation_query(&p, &positions()).unwrap();
    // Three terms can sum to 15. Three bits (enough for modulus 6) are NOT
    // enough for this sum: the encoder must use four bits before remainder.
    assert!(query.contains("(_ bv5 4)"));
    assert!(query.contains("(_ bv6 4)"));
    assert!(!query.contains("get-value"));
    assert_eq!(evaluate_phase(&p, &bindings(1)), r(2, 3));
    let p = [(x(0), r(1, 3)), (x(1), r(1, 4))].into();
    let query = phase_variation_query(&p, &positions()).unwrap();
    assert!(query.contains("(_ bv12 "));
}

#[test]
fn nonlinear_selector_dependencies_do_not_imply_phase_variation() {
    // x XOR y = x + y - 2xy over integers. The whole phase is zero,
    // despite having several nonconstant selectors and nonzero coefficients.
    let p = [
        (x(0), r(1, 3)),
        (x(1), r(1, 3)),
        (x(0).xor(&x(1)), r(-1, 3)),
        (x(0).and(&x(1)), r(-2, 3)),
    ]
    .into();
    assert!(phase_variation_query(&p, &positions()).is_some());
    for mask in 0..4 {
        assert_eq!(evaluate_phase(&p, &bindings(mask)), r(0, 1));
    }
}

#[test]
fn parsed_program_phases_are_compared_in_turns_not_radians() {
    use crate::{
        equivalence::{EquivalenceConfig, prepare_comparison},
        frontend::openqasm3,
    };
    let parse = |body| {
        openqasm3::parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit q; {body}"),
            "phase-query.qasm",
        )
        .unwrap()
    };
    let z = parse("z q;");
    let identity = parse("");
    let p = prepare_comparison(
        &z,
        &identity,
        &EquivalenceConfig::positional(&z, &identity).unwrap(),
    )
    .unwrap();
    let delta = rational_phase_difference(
        &p.left.hps.components[0].phase,
        &p.right.hps.components[0].phase,
    )
    .unwrap();
    let input = p.left.hps.input.quantum.keys().next().unwrap().clone();
    for b in [false, true] {
        assert_eq!(
            evaluate_phase(&delta, &[(Variable::Input(input.clone()), b)].into()),
            if b { r(1, 2) } else { r(0, 1) }
        );
    }
}

#[test]
#[ignore = "requires an external Z3 executable; validates generated SMT-LIB"]
fn generated_queries_match_all_fixed_assignments_with_z3() {
    use std::{
        io::Write,
        process::{Command, Stdio},
    };
    for seed in 0..12i64 {
        let a = r(seed - 5, 3);
        let b = r(7 - seed, 4);
        let c = r(2 * seed - 3, 6);
        let p = [
            (x(0), a.clone()),
            (x(1), b.clone()),
            (x(0).and(&x(1)), c.clone()),
            (BooleanPolynomial::one(), r(1, 5)),
        ]
        .into();
        let query = phase_variation_query(&p, &positions()).unwrap();
        let mut script = query.replace("(check-sat)\n", "");
        let value = |mask: usize| {
            let sum = if mask & 1 != 0 { a.clone() } else { r(0, 1) }
                + if mask & 2 != 0 { b.clone() } else { r(0, 1) }
                + if mask == 3 { c.clone() } else { r(0, 1) };
            // Independent integer remainder oracle, not evaluate_phase.
            let d = sum.denom();
            let n = ((sum.numer() % d) + d) % d;
            BigRational::new(n, d.clone())
        };
        let mut expected = Vec::new();
        for l in 0..4 {
            for r in 0..4 {
                script.push_str("(push 1)\n");
                for (name, mask) in [("x", l), ("z", r)] {
                    for i in 0..2 {
                        script.push_str(&format!(
                            "(assert (= {name}{i} {}))\n",
                            mask & (1 << i) != 0
                        ));
                    }
                }
                script.push_str("(check-sat)\n(pop 1)\n");
                expected.push(if value(l) != value(r) { "sat" } else { "unsat" });
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
        assert_eq!(output.lines().collect::<Vec<_>>(), expected, "seed {seed}");
    }
}
