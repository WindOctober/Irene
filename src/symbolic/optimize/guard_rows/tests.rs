use super::*;
use crate::ir::{ClassicalBit, Qubit, SymbolId};
use crate::symbolic::{HistoryEntry, HybridMemory, PhaseCoefficient, PhasePolynomial, Scalar};
use num_rational::BigRational;
use std::collections::BTreeMap;

#[test]
fn nonlinear_row_combinations_expose_unique_paths_with_or_without_history() {
    for hidden in [false, true] {
        let mut c = fixture();
        let product = x(0).and(&p(9)).xor(&x(0).and(&p(1))).xor(&x(0).and(&x(1)));
        c.guard = vec![p(9).xor(&product), p(1).xor(&product)];
        c.output.quantum.insert(q(2), p(9).xor(&x(1)));
        c.output.classical.insert(
            ClassicalBit {
                register: SymbolId(1),
                index: 0,
            },
            p(1),
        );
        c.phase
            .add_boolean(&p(9), PhaseCoefficient::rational(ratio(1, 8)));
        c.scalar = Scalar::select(
            p(1),
            Scalar::rational(ratio(2, 3)),
            Scalar::rational(ratio(-1, 3)),
        );
        if hidden {
            c.output.history.push(HistoryEntry::Discard { value: p(9) });
        }
        let before = c.clone();
        assert!(super::super::simplify_component(&mut c));
        assert!(c.path_support.is_empty());
        assert!(c.guard.is_empty());
        assert_eq!(vector(&before), vector(&c));
        assert_eq!(c.output.history.len(), usize::from(hidden));
    }
}

#[test]
fn formal_product_columns_are_not_independent_variables_or_self_replacements() {
    let mut c = fixture();
    c.path_support = [9].into();
    c.guard = vec![p(9).xor(&p(9).and(&x(0)))];
    let before = c.clone();
    assert_eq!(eliminate_guard_path(&mut c), Ok(false));
    assert_eq!(c, before);
    assert_eq!(vector(&before), vector(&c));
}

#[test]
fn row_order_and_duplicate_equations_do_not_change_exact_substitution() {
    let mut first = fixture();
    first.guard.push(p(1).xor(&x(0).and(&x(1))));
    let mut other = first.clone();
    other.guard.reverse();
    other.guard.extend(other.guard.clone());
    let before = vector(&first);
    assert!(super::super::simplify_component(&mut first));
    assert!(super::super::simplify_component(&mut other));
    assert_eq!(vector(&first), before);
    assert_eq!(vector(&other), before);
    assert!(first.path_support.is_empty() && other.path_support.is_empty());
}

#[test]
fn unique_nonlinear_value_is_shared_across_many_outputs() {
    let mut c = fixture();
    let rhs = (0..10).fold(BooleanPolynomial::zero(), |p, i| {
        p.xor(&x(2 * i).and(&x(2 * i + 1)))
    });
    c.guard = vec![p(9).xor(&rhs)];
    c.path_support = [9].into();
    for i in 0..20 {
        c.output.quantum.insert(q(i), p(9));
    }
    assert_eq!(eliminate_guard_path(&mut c), Ok(true));
    assert!(c.path_support.is_empty());
    assert!(c.output.quantum.values().all(|value| value == &rhs));
}

#[test]
fn factored_guard_columns_do_not_expand_products_or_become_free_paths() {
    let rhs = (0..30).fold(BooleanPolynomial::one(), |p, i| p.and(&x(i).complement()));
    assert!(rhs.expanded_terms(1024).is_none());
    let mut c = fixture();
    c.path_support = [9].into();
    c.guard = vec![p(9).xor(&rhs)];
    c.output.quantum.insert(q(30), p(9));
    assert_eq!(eliminate_guard_path(&mut c), Ok(true));
    assert!(c.path_support.is_empty());
    assert_eq!(c.output.quantum[&q(30)], rhs);
    assert!(super::super::simplify_component(&mut c));
    assert!(c.guard.is_empty());

    // The same formal product may NOT be treated as an independent input.
    let recursive = p(9).and(&rhs);
    c.path_support.insert(9);
    c.guard = vec![p(9).xor(&recursive)];
    let before = c.clone();
    assert_eq!(eliminate_guard_path(&mut c), Ok(false));
    assert_eq!(c, before);
}

#[test]
fn wide_row_removes_the_pivot_structurally_not_just_modulo_xor() {
    let rhs = (0..80).fold(BooleanPolynomial::zero(), |sum, i| sum.xor(&x(i)));
    let mut c = fixture();
    c.path_support = [9].into();
    c.guard = vec![p(9).xor(&rhs)];
    c.output.quantum.insert(q(80), p(9));
    assert_eq!(eliminate_guard_path(&mut c), Ok(true));
    assert!(c.path_support.is_empty());
    assert!(
        !c.output.quantum[&q(80)]
            .variables()
            .contains(&Variable::Path(9))
    );
    assert_eq!(
        c.output.quantum[&q(80)].expanded_terms(1024),
        rhs.expanded_terms(1024)
    );
    assert!(super::super::simplify_component(&mut c));
    assert!(c.guard.is_empty());
}

#[test]
fn matrix_budget_refusal_does_not_change_the_component() {
    let mut c = fixture();
    c.guard = (0..1100).map(|i| p(i).xor(&x(i).and(&x(i + 1)))).collect();
    c.path_support = (0..1100).collect();
    let before = c.clone();
    assert_eq!(eliminate_guard_path(&mut c), Ok(false));
    assert_eq!(c, before);
}

fn ratio(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}
fn q(i: usize) -> Qubit {
    Qubit {
        register: SymbolId(0),
        index: i,
    }
}
fn x(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Input(q(i)))
}
fn p(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(i))
}
fn fixture() -> Component {
    Component {
        guard: vec![p(9).xor(&p(1)).xor(&x(0).and(&x(1)))],
        scalar: Scalar::rational(ratio(1, 3)),
        path_support: [1, 9].into(),
        phase: PhasePolynomial::zero(),
        output: HybridMemory::default(),
    }
}

// Exact amplitude comparison in Q(zeta_8), including classical memory and
// the unchanged history environment. Stronger than a density-only comparison.
type Vector = BTreeMap<(usize, Vec<bool>), [BigRational; 4]>;
fn vector(c: &Component) -> Vector {
    let mut out = Vector::new();
    for inputs in 0..4 {
        for paths in 0..1usize << c.path_support.len() {
            let mut assignment = BTreeMap::from([
                (Variable::Input(q(0)), inputs & 1 != 0),
                (Variable::Input(q(1)), inputs & 2 != 0),
            ]);
            for (i, path) in c.path_support.iter().enumerate() {
                assignment.insert(Variable::Path(*path), paths & (1 << i) != 0);
            }
            let eval = |value: &BooleanPolynomial| {
                value
                    .terms()
                    .filter(|m| m.variables().all(|v| assignment[v]))
                    .count()
                    % 2
                    == 1
            };
            if c.guard.iter().any(eval) {
                continue;
            }
            let signature = c
                .output
                .quantum
                .values()
                .chain(c.output.classical.values())
                .chain(c.output.history.iter().map(|h| match h {
                    HistoryEntry::Write { value, .. } | HistoryEntry::Discard { value } => value,
                }))
                .map(eval)
                .collect();
            fn scalar(s: &Scalar, eval: &impl Fn(&BooleanPolynomial) -> bool) -> BigRational {
                match s {
                    Scalar::Rational(r) => r.clone(),
                    Scalar::Select {
                        condition,
                        when_true,
                        when_false,
                    } => scalar(
                        if eval(condition) {
                            when_true
                        } else {
                            when_false
                        },
                        eval,
                    ),
                    _ => panic!("unexpected scalar in exact test"),
                }
            }
            let mut exponent = ratio(0, 1);
            for (term, coefficient) in c.phase.terms() {
                if term.variables().all(|v| assignment[v]) {
                    exponent += coefficient.as_rational().unwrap() * ratio(8, 1);
                }
            }
            assert!(exponent.is_integer());
            let exponent = exponent.to_integer().to_string().parse::<usize>().unwrap() % 8;
            let value = out
                .entry((inputs, signature))
                .or_insert_with(|| std::array::from_fn(|_| ratio(0, 1)));
            value[exponent % 4] +=
                scalar(&c.scalar, &eval) * ratio(if exponent >= 4 { -1 } else { 1 }, 1);
        }
    }
    out.retain(|_, coefficients| coefficients.iter().any(|r| *r != ratio(0, 1)));
    out
}

#[test]
fn nonlinear_remainder_updates_every_field_with_exact_amplitudes() {
    for phase_numerator in 0..8 {
        let mut before = fixture();
        before
            .guard
            .push(p(9).and(&x(0)).xor(&p(1).and(&x(0))).xor(&x(0).and(&x(1))));
        before.scalar = Scalar::select(
            p(9),
            Scalar::rational(ratio(1, 2)),
            Scalar::rational(ratio(-1, 3)),
        );
        before.phase.add_boolean(
            &p(9).and(&x(0)),
            PhaseCoefficient::rational(ratio(phase_numerator, 8)),
        );
        before.output.quantum.insert(q(2), p(9).xor(&p(1)));
        before.output.classical.insert(
            ClassicalBit {
                register: SymbolId(1),
                index: 0,
            },
            p(9),
        );
        before.output.history = vec![
            HistoryEntry::Discard { value: p(9) },
            HistoryEntry::Discard { value: p(1) },
        ];
        let mut after = before.clone();
        assert!(eliminate_guard_path(&mut after) == Ok(true));
        assert!(!after.path_support.contains(&9));
        assert_eq!(vector(&before), vector(&after));
    }
}

#[test]
fn target_linear_equation_does_not_need_a_small_support_truth_table() {
    let mut c = fixture();
    c.path_support = [9].into();
    let mut rhs = BooleanPolynomial::zero();
    for i in 0..10 {
        rhs = rhs.xor(&x(2 * i).and(&x(2 * i + 1)));
    }
    c.guard = vec![p(9).xor(&rhs)];
    c.phase
        .add_boolean(&p(9), PhaseCoefficient::rational(ratio(1, 2)));
    c.output.quantum.insert(q(30), p(9));
    let scalar = c.scalar.clone();
    assert!(eliminate_guard_path(&mut c) == Ok(true));
    assert!(c.guard.is_empty());
    assert!(c.path_support.is_empty());
    assert_eq!(c.output.quantum[&q(30)], rhs);
    assert_eq!(c.scalar, scalar); // Unique witness: no extra factor of two.
}

#[test]
fn nonunit_coefficient_and_unowned_or_free_pivots_are_not_solved() {
    for equation in [
        p(9).and(&x(0)).xor(&x(1)),
        p(9).xor(&p(9).and(&x(0))).xor(&x(1)),
        x(0).xor(&p(9).and(&x(1))),
        p(99).xor(&x(0).and(&x(1))),
    ] {
        let mut c = fixture();
        c.path_support = [9].into();
        c.guard = vec![equation];
        let before = c.clone();
        assert_eq!(eliminate_guard_path(&mut c), Ok(false));
        assert_eq!(c, before);
    }
}

#[test]
fn non_clifford_phase_substitution_retains_a_factored_selector() {
    let mut c = fixture();
    let rhs = (0..14).fold(BooleanPolynomial::zero(), |sum, i| sum.xor(&x(i)));
    c.guard = vec![p(9).xor(&rhs)];
    c.phase
        .add_boolean(&p(9), PhaseCoefficient::rational(ratio(1, 3)));
    assert_eq!(eliminate_guard_path(&mut c), Ok(true));
    assert!(!c.path_support.contains(&9));
    assert!(c.phase.storage_size() < 100);
    assert!(c.phase.expanded_terms(128).is_none());
    let selectors = c.phase.selectors().collect::<Vec<_>>();
    assert_eq!(selectors.len(), 1);
    assert_eq!(selectors[0].0, rhs);
    assert_eq!(selectors[0].1.as_rational(), Some(ratio(1, 3)));
}

#[test]
fn dense_matrix_budget_is_checked_before_any_write() {
    let mut c = fixture();
    c.guard
        .extend((0..1100).map(|i| x(2 * i).and(&x(2 * i + 1))));
    let before = c.clone();
    assert_eq!(eliminate_guard_path(&mut c), Ok(false));
    assert_eq!(c, before);
}

#[test]
fn conflicting_unique_witness_equations_remain_unsatisfiable() {
    let mut c = fixture();
    c.guard.push(c.guard[0].complement());
    assert_eq!(eliminate_guard_path(&mut c), Err(()));
    assert!(!super::super::simplify_component(&mut c));
}

#[test]
fn local_history_alignment_exceeds_the_old_enumeration_support() {
    let mut c = fixture();
    let mut rhs = p(1);
    for i in 0..10 {
        rhs = rhs.xor(&x(2 * i).and(&x(2 * i + 1)));
    }
    c.guard = vec![p(9).xor(&rhs)];
    c.output.quantum.insert(q(30), x(0));
    c.output.history.push(HistoryEntry::Discard { value: p(1) });
    super::super::local_history::collapse_local_history(&mut c);
    assert!(c.path_support.is_empty());
    assert!(c.output.history.is_empty());
    assert!(c.guard.is_empty());
    assert_eq!(c.output.quantum[&q(30)], x(0));
    assert_eq!(
        c.scalar,
        Scalar::rational(ratio(1, 3)).multiply(Scalar::sqrt(Scalar::rational(ratio(2, 1))))
    );
}

#[test]
fn path_inference_preserves_amplitudes_even_when_history_cannot_collapse() {
    let mut c = fixture();
    c.output.quantum.insert(q(2), x(0));
    c.output.history.push(HistoryEntry::Discard { value: p(1) });
    // This input-dependent phase is NOT a pure hidden-history phase.
    c.phase
        .add_boolean(&p(1).and(&x(0)), PhaseCoefficient::rational(ratio(1, 8)));
    let before = c.clone();
    assert!(super::super::simplify_component(&mut c));
    assert_eq!(c.output.history, before.output.history);
    assert!(c.path_support.len() < before.path_support.len());
    assert_eq!(vector(&before), vector(&c));
}

#[test]
fn guard_alignment_exposes_the_hidden_history_factor() {
    let mut c = fixture();
    c.guard
        .push(x(0).and(&p(9).xor(&p(1))).xor(&x(0).and(&x(1))));
    c.output.quantum.insert(q(2), x(0));
    c.output.history.push(HistoryEntry::Discard { value: p(1) });
    super::super::local_history::collapse_local_history(&mut c);
    assert!(c.path_support.is_empty());
    assert!(c.output.history.is_empty());
    // The history contributes sqrt(2), while solving its partner contributes 1.
    assert_eq!(
        c.scalar,
        Scalar::rational(ratio(1, 3)).multiply(Scalar::sqrt(Scalar::rational(ratio(2, 1))))
    );
}
