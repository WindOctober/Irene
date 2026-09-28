use super::*;
use crate::ir::{Qubit, SymbolId};
use crate::symbolic::HybridMemory;
use std::convert::Infallible;

fn x(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Input(Qubit {
        register: SymbolId(0),
        index: i,
    }))
}
fn y() -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(0))
}
fn fixture() -> Component {
    Component {
        guard: vec![],
        scalar: Scalar::one(),
        path_support: [0].into(),
        phase: PhasePolynomial::zero(),
        output: HybridMemory {
            quantum: Default::default(),
            classical: Default::default(),
            history: vec![],
        },
    }
}
fn add(c: &mut Component, selector: BooleanPolynomial, n: i64, d: i64) {
    c.phase
        .add_boolean(&selector, PhaseCoefficient::rational(ratio(n, d)));
}
fn boolean(p: &BooleanPolynomial, input: usize, path: bool) -> bool {
    p.evaluate::<Infallible>(|v| {
        Ok(match v {
            Variable::Input(q) => input & (1 << q.index) != 0,
            Variable::Path(0) => path,
            _ => panic!("unexpected path"),
        })
    })
    .unwrap()
}
fn phase(p: &PhasePolynomial, input: usize, path: bool) -> BigRational {
    let value = p
        .selectors()
        .filter(|(b, _)| boolean(b, input, path))
        .fold(integer(0), |s, (_, a)| s + a.as_rational().unwrap());
    PhaseCoefficient::rational(value).as_rational().unwrap()
}
fn verify_profile(c: &Component, result: &PhaseProfile, inputs: usize) {
    for input in 0..(1 << inputs) {
        let delta = PhaseCoefficient::rational(
            phase(&c.phase, input, true) - phase(&c.phase, input, false),
        )
        .as_rational()
        .unwrap();
        let expected = match result {
            PhaseProfile::Fourier(f) => {
                if boolean(f, input, false) {
                    ratio(1, 2)
                } else {
                    integer(0)
                }
            }
            PhaseProfile::Omega { parity, sign } => {
                let base = match sign {
                    OmegaSign::Positive => ratio(1, 4),
                    OmegaSign::Negative => ratio(3, 4),
                };
                PhaseCoefficient::rational(
                    base + if boolean(parity, input, false) {
                        ratio(1, 2)
                    } else {
                        integer(0)
                    },
                )
                .as_rational()
                .unwrap()
            }
            _ => panic!("joint analysis must return a sum rule, not an absent-phase shortcut"),
        };
        assert_eq!(delta, expected, "input={input}");
    }
}

#[test]
fn complementary_quarter_terms_reveal_fourier_and_keep_zero_cofactor() {
    let mut c = fixture();
    let b = y().xor(&x(1));
    add(&mut c, x(0).and(&b), 1, 4);
    add(&mut c, x(0).and(&b.complement()), 1, 4);
    add(&mut c, y().and(&x(2)), 1, 2);
    add(&mut c, x(3), 1, 8);
    assert!(matches!(
        super::super::phase_profile(&c, &Variable::Path(0)),
        PhaseProfile::Unsupported
    ));
    let result = analyze(&c, &Variable::Path(0)).unwrap();
    verify_profile(&c, &result, 4);
    assert!(matches!(result, PhaseProfile::Fourier(_)));
    let before = c.clone();
    super::super::PathRule::Fourier.apply(&mut c, &Variable::Path(0), result);
    assert!(!c.path_support.contains(&0));
    assert_eq!(c.scalar, Scalar::rational(integer(2)));
    assert!(!c.phase.variables().contains(&Variable::Path(0)));
    for input in 0..16 {
        assert_eq!(
            phase(&c.phase, input, false),
            phase(&before.phase, input, false)
        );
    }
}

#[test]
fn complementary_quarter_terms_reveal_both_omega_signs() {
    for sign in [-1, 1] {
        let mut c = fixture();
        add(&mut c, y().and(&x(0)), sign, 4);
        add(&mut c, y().and(&x(0).complement()), sign, 4);
        add(&mut c, y().and(&x(1)), 1, 2);
        add(&mut c, x(2), 1, 8);
        let result = analyze(&c, &Variable::Path(0)).unwrap();
        verify_profile(&c, &result, 3);
        assert!(matches!(result, PhaseProfile::Omega { .. }));
        let before = c.clone();
        super::super::PathRule::Omega.apply(&mut c, &Variable::Path(0), result);
        assert!(!c.phase.variables().contains(&Variable::Path(0)));
        // Exact equality in Q(zeta_8), where sqrt(2)=zeta_8-zeta_8^3.
        for input in 0..8 {
            let exponent = |p: &PhasePolynomial, v| {
                usize::try_from((phase(p, input, v) * integer(8)).to_integer()).unwrap()
            };
            let mut lhs = [0i32; 4];
            let mut rhs = [0i32; 4];
            let insert = |v: &mut [i32; 4], e: usize, k: i32| {
                let e = e % 8;
                v[e % 4] += if e >= 4 { -k } else { k };
            };
            insert(&mut lhs, exponent(&before.phase, false), 1);
            insert(&mut lhs, exponent(&before.phase, true), 1);
            let e = exponent(&c.phase, false);
            insert(&mut rhs, e + 1, 1);
            insert(&mut rhs, e + 3, -1);
            assert_eq!(lhs, rhs);
        }
    }
}

#[test]
fn nonclifford_and_variable_quarter_derivatives_are_not_forced_into_rules() {
    for denominator in [3, 8, 16, 8192] {
        let mut c = fixture();
        add(&mut c, y(), 1, denominator);
        assert!(analyze(&c, &Variable::Path(0)).is_none());
    }
    let mut c = fixture();
    add(&mut c, y().and(&x(0)), 1, 4);
    assert!(analyze(&c, &Variable::Path(0)).is_none());
}

#[test]
fn exact_modular_profiles_agree_with_exhaustive_small_phase_functions() {
    let mut state = 917u64;
    let mut next = || {
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        state
    };
    let mut admitted = 0;
    for _ in 0..256 {
        let mut c = fixture();
        let mut terms = vec![y(), x(0), x(1), x(2), x(3)];
        for _ in 0..6 {
            let a = terms[(next() as usize) % terms.len()].clone();
            let b = terms[(next() as usize) % terms.len()].clone();
            let selector = if next() & 1 == 0 {
                a.and(&b)
            } else {
                a.xor(&b)
            };
            add(&mut c, selector.clone(), (next() % 15) as i64 - 7, 16);
            terms.push(selector);
        }
        if let Some(result) = analyze(&c, &Variable::Path(0)) {
            admitted += 1;
            verify_profile(&c, &result, 4);
        }
    }
    assert!(admitted > 0);
}

#[test]
fn local_davio_recovers_affine_guard_without_expanded_storage() {
    let a = x(0);
    let b = x(1);
    let f = x(2).xor(&x(3));
    let g = a
        .and(&b)
        .xor(&a.and(&f))
        .xor(&a.and(&f.complement()))
        .xor(&a.complement().and(&b));
    let normalized = BooleanPolynomial::normalize_local(&[g.clone()])
        .unwrap()
        .remove(0);
    assert!(normalized.is_affine());
    for input in 0..16 {
        assert_eq!(
            boolean(&g, input, false),
            boolean(&normalized, input, false)
        );
    }
    assert_eq!(normalized, a.xor(&b));
}

#[test]
fn joint_rewrite_respects_guard_scalar_outputs_and_history() {
    let mut original = fixture();
    let b = y().xor(&x(1));
    add(&mut original, x(0).and(&b), 1, 4);
    add(&mut original, x(0).and(&b.complement()), 1, 4);
    add(&mut original, y().and(&x(2)), 1, 2);
    for field in 0..4 {
        let mut c = original.clone();
        match field {
            0 => c.guard.push(y().xor(&x(3))),
            1 => c.scalar = Scalar::select(y(), Scalar::one(), Scalar::rational(integer(2))),
            2 => {
                c.output.quantum.insert(
                    Qubit {
                        register: SymbolId(0),
                        index: 0,
                    },
                    y(),
                );
            }
            3 => c.output.history.push(HistoryEntry::Discard { value: y() }),
            _ => unreachable!(),
        }
        let before = c.clone();
        assert!(!super::super::reduce_path(&mut c, &Variable::Path(0), true));
        assert_eq!(c, before);
    }
    assert!(super::super::reduce_path(
        &mut original,
        &Variable::Path(0),
        false
    ));
    assert!(!original.path_support.contains(&0));
}

#[test]
fn zero_joint_derivative_still_rewrites_the_zero_cofactor() {
    let mut c = fixture();
    let b = y().xor(&x(1));
    add(&mut c, x(0).and(&b), 1, 4);
    add(&mut c, x(0).and(&b.complement()), 1, 4);
    let before = c.clone();
    assert!(super::super::reduce_path(&mut c, &Variable::Path(0), false));
    assert_eq!(c.scalar, Scalar::rational(integer(2)));
    assert!(!c.phase.variables().contains(&Variable::Path(0)));
    for input in 0..4 {
        assert_eq!(
            phase(&before.phase, input, false),
            phase(&before.phase, input, true)
        );
        assert_eq!(
            phase(&c.phase, input, false),
            phase(&before.phase, input, false)
        );
    }
}

#[test]
fn recovered_guard_pivot_propagates_to_all_hps_fields() {
    let mut c = fixture();
    let a = y();
    let b = x(1);
    let f = x(2).xor(&x(3));
    c.guard.push(
        a.and(&b)
            .xor(&a.and(&f))
            .xor(&a.and(&f.complement()))
            .xor(&a.complement().and(&b)),
    );
    let q = Qubit {
        register: SymbolId(0),
        index: 0,
    };
    c.output.quantum.insert(q.clone(), y());
    c.output.history.push(HistoryEntry::Discard { value: y() });
    c.scalar = Scalar::select(y(), Scalar::one(), Scalar::rational(integer(2)));
    add(&mut c, y(), 1, 8);
    assert!(super::super::simplify_component(&mut c));
    assert!(!c.path_support.contains(&0));
    assert!(c.guard.is_empty());
    assert_eq!(c.output.quantum[&q], b);
    assert_eq!(
        c.output.history,
        vec![HistoryEntry::Discard { value: b.clone() }]
    );
    assert_eq!(
        c.scalar,
        Scalar::select(b, Scalar::one(), Scalar::rational(integer(2)))
    );
    for input in 0..16 {
        assert_eq!(
            phase(&c.phase, input, false),
            if input & 2 != 0 {
                ratio(1, 8)
            } else {
                integer(0)
            }
        );
    }
}
