use super::*;
use crate::ir::{ClassicalBit, Qubit, SymbolId};
use crate::symbolic::{HybridMemory, PhasePolynomial};
use std::collections::BTreeMap;
use std::convert::Infallible;

fn q(i: usize) -> Qubit {
    Qubit {
        register: SymbolId(0),
        index: i,
    }
}
fn x(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Input(q(i)))
}
fn y(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(i))
}
fn fixture() -> Component {
    Component {
        guard: Vec::new(),
        scalar: Scalar::rational(ratio(-1, 3)),
        path_support: [0].into(),
        phase: PhasePolynomial::zero(),
        output: HybridMemory::default(),
    }
}
fn add_phase(c: &mut Component, selector: &BooleanPolynomial, n: i64, d: i64) {
    c.phase
        .add_boolean(selector, PhaseCoefficient::rational(ratio(n, d)));
}
fn run(c: &mut Component) -> bool {
    reduce_path_sums(c, false)
}
fn step(c: &mut Component, variable: &Variable) -> bool {
    reduce_path(c, variable, false)
}

// Independent exact arithmetic in Q(zeta_8), with zeta_8^4 = -1.
// It checks amplitudes, including global phase, not only their probabilities.
pub(super) type Eighth = [BigRational; 4];
pub(super) fn zero() -> Eighth {
    std::array::from_fn(|_| integer(0))
}
fn rational(value: BigRational) -> Eighth {
    [value, integer(0), integer(0), integer(0)]
}
pub(super) fn multiply(a: &Eighth, b: &Eighth) -> Eighth {
    let mut result = zero();
    for i in 0..4 {
        for j in 0..4 {
            result[(i + j) % 4] += &a[i] * &b[j] * integer(if i + j >= 4 { -1 } else { 1 });
        }
    }
    result
}
fn rational_root(r: &BigRational) -> Option<BigRational> {
    if r < &integer(0) {
        return None;
    }
    let n = r.numer().sqrt();
    let d = r.denom().sqrt();
    (&n * &n == *r.numer() && &d * &d == *r.denom()).then(|| BigRational::new(n, d))
}
fn scalar(s: &Scalar, eval: &impl Fn(&BooleanPolynomial) -> bool) -> Eighth {
    match s {
        Scalar::Rational(r) => rational(r.clone()),
        Scalar::Neg(a) => scalar(a, eval).map(|r| -r),
        Scalar::Mul(a, b) => multiply(&scalar(a, eval), &scalar(b, eval)),
        Scalar::Add(a, b) => {
            let mut result = scalar(a, eval);
            for (r, v) in result.iter_mut().zip(scalar(b, eval)) {
                *r += v;
            }
            result
        }
        Scalar::Sqrt(a) => {
            let Scalar::Rational(r) = a.as_ref() else {
                panic!("test root must be rational")
            };
            if let Some(root) = rational_root(r) {
                rational(root)
            } else {
                let root = rational_root(&(r / integer(2))).expect("test root lies in Q(sqrt(2))");
                // sqrt(2) = zeta_8 - zeta_8^3.
                [integer(0), root.clone(), integer(0), -root]
            }
        }
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
        _ => panic!("unsupported scalar in the independent test oracle"),
    }
}
pub(super) type Vector = BTreeMap<(usize, Vec<bool>), Eighth>;
pub(super) fn vector(c: &Component) -> Vector {
    let mut result = Vector::new();
    for input in 0usize..4 {
        for path in 0usize..(1 << c.path_support.len()) {
            let mut values = BTreeMap::from([
                (Variable::Input(q(0)), input & 1 != 0),
                (Variable::Input(q(1)), input & 2 != 0),
            ]);
            for (i, id) in c.path_support.iter().enumerate() {
                values.insert(Variable::Path(*id), path & (1 << i) != 0);
            }
            let eval = |p: &BooleanPolynomial| p.evaluate::<Infallible>(|v| Ok(values[v])).unwrap();
            if c.guard.iter().any(&eval) {
                continue;
            }
            let mut exponent = integer(0);
            for (selector, coefficient) in c.phase.selectors() {
                if eval(&selector) {
                    exponent += coefficient.as_rational().unwrap() * integer(8);
                }
            }
            assert!(exponent.is_integer());
            let k = usize::try_from(exponent.to_integer()).unwrap() % 8;
            let mut phase = zero();
            phase[k % 4] = integer(if k >= 4 { -1 } else { 1 });
            let amplitude = multiply(&scalar(&c.scalar, &eval), &phase);
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
            let entry = result.entry((input, signature)).or_insert_with(zero);
            for (r, a) in entry.iter_mut().zip(amplitude) {
                *r += a;
            }
        }
    }
    result.retain(|_, value| value.iter().any(|r| *r != integer(0)));
    result
}
fn assert_amplitudes(before: &Component, after: &Component, reachable: bool) {
    if reachable {
        assert_eq!(vector(before), vector(after));
    } else {
        assert!(vector(before).is_empty());
    }
}

#[test]
fn unused_path_doubles_amplitude_without_changing_relative_phase() {
    let mut c = fixture();
    c.scalar = Scalar::sqrt(Scalar::rational(ratio(1, 2)));
    add_phase(&mut c, &x(0), 1, 8);
    c.output.quantum.insert(q(0), x(0));
    let before = c.clone();
    let reachable = run(&mut c);
    assert!(reachable && c.path_support.is_empty());
    assert_amplitudes(&before, &c, reachable);
}

#[test]
fn fourier_preserves_exact_amplitudes_for_both_cofactors() {
    for f in [
        BooleanPolynomial::zero(),
        BooleanPolynomial::one(),
        x(0),
        x(0).xor(&x(1)),
        x(0).and(&x(1)),
    ] {
        let mut c = fixture();
        // Nonzero zero-cofactor x(1) must survive removal of y.
        add_phase(&mut c, &y(0).and(&f).xor(&x(1)), 1, 2);
        add_phase(&mut c, &x(0), 1, 8);
        c.output.quantum.insert(q(0), x(0));
        let before = c.clone();
        let reachable = run(&mut c);
        if reachable {
            assert!(c.path_support.is_empty());
        }
        assert_amplitudes(&before, &c, reachable);
    }
}

#[test]
fn omega_preserves_both_signs_parities_and_zero_cofactor_phase() {
    for sign in [-1, 1] {
        for f in [
            BooleanPolynomial::zero(),
            BooleanPolynomial::one(),
            x(0),
            x(0).xor(&x(1)),
            x(0).and(&x(1)),
        ] {
            let mut c = fixture();
            c.scalar = Scalar::sqrt(Scalar::rational(ratio(1, 2)));
            add_phase(&mut c, &y(0), sign, 4);
            add_phase(&mut c, &y(0).and(&f).xor(&x(1)), 1, 2);
            add_phase(&mut c, &x(0), 3, 8);
            let before = c.clone();
            let reachable = run(&mut c);
            assert!(reachable && c.path_support.is_empty());
            assert_amplitudes(&before, &c, reachable);
        }
    }
}

#[test]
fn dependencies_in_every_nonphase_field_block_coherent_summation() {
    for field in 0..6 {
        let mut c = fixture();
        match field {
            0 => c.guard.push(y(0).and(&x(0))),
            1 => c.scalar = Scalar::select(y(0), Scalar::one(), Scalar::zero()),
            2 => {
                c.output.quantum.insert(q(0), y(0));
            }
            3 => {
                c.output.classical.insert(
                    ClassicalBit {
                        register: SymbolId(1),
                        index: 0,
                    },
                    y(0),
                );
            }
            4 => c.output.history.push(HistoryEntry::Discard { value: y(0) }),
            5 => c.output.history.push(HistoryEntry::Write {
                target: ClassicalBit {
                    register: SymbolId(1),
                    index: 0,
                },
                value: y(0),
            }),
            _ => unreachable!(),
        }
        let before = c.clone();
        assert!(!step(&mut c, &Variable::Path(0)));
        assert_eq!(c, before);
    }
}

#[test]
fn unsupported_eighth_turn_dependence_is_not_discarded() {
    let mut c = fixture();
    add_phase(&mut c, &y(0), 1, 8);
    let before = c.clone();
    assert!(run(&mut c));
    assert_eq!(c, before);
    assert_eq!(vector(&before), vector(&c));
}

#[test]
fn fixed_point_revisits_paths_unblocked_by_fourier_constraints() {
    let mut c = fixture();
    c.path_support = [0, 1, 2].into();
    c.guard.push(y(2).and(&x(0)));
    add_phase(&mut c, &y(0).and(&y(2)), 1, 2);
    add_phase(&mut c, &y(1).and(&y(2)), 1, 2);
    let before = c.clone();
    let reachable = run(&mut c);
    assert!(reachable && c.path_support.is_empty());
    assert_amplitudes(&before, &c, reachable);
}

#[test]
fn consecutive_omega_rules_preserve_sqrt_factors_and_all_phase_offsets() {
    let mut c = fixture();
    c.path_support = [0, 1].into();
    add_phase(&mut c, &y(0), 1, 4);
    add_phase(&mut c, &y(1), -1, 4);
    add_phase(
        &mut c,
        &y(0).and(&x(0)).xor(&y(1).and(&x(1))).xor(&x(0)),
        1,
        2,
    );
    let before = c.clone();
    let reachable = run(&mut c);
    assert!(reachable && c.path_support.is_empty());
    assert_amplitudes(&before, &c, reachable);
}

#[test]
fn semantic_scalar_independence_removes_syntactic_binder_uses() {
    let mut c = fixture();
    c.path_support = [0, 1].into();
    let condition = y(0)
        .xor(&y(0).and(&y(1)))
        .xor(&y(0).and(&y(1).complement()));
    c.scalar = Scalar::select(condition, Scalar::rational(integer(3)), Scalar::one());
    let before = c.clone();
    assert!(!scalar_depends_on(&c.scalar, &Variable::Path(0)));
    assert!(step(&mut c, &Variable::Path(0)));
    assert!(!c.path_support.contains(&0));
    assert_eq!(vector(&before), vector(&c));
}

#[test]
fn omega_then_fourier_can_cancel_the_entire_component() {
    let mut c = fixture();
    c.path_support = [0, 1].into();
    add_phase(&mut c, &y(0), 1, 4);
    add_phase(&mut c, &y(1), -1, 4);
    add_phase(&mut c, &y(0).and(&y(1)), 1, 2);
    let before = c.clone();
    assert!(!run(&mut c));
    assert!(vector(&before).is_empty());
}

#[test]
fn hps_entrypoint_sums_paths_and_applies_guard_substitution() {
    let mut c = fixture();
    c.path_support = [0, 1].into();
    c.scalar = Scalar::rational(ratio(1, 2));
    add_phase(&mut c, &y(0).and(&x(0).xor(&y(1))), 1, 2);
    c.output.quantum.insert(q(0), y(1));
    let before = c.clone();
    let reduced = super::super::simplify(crate::symbolic::HybridPathSum {
        input: HybridMemory::default(),
        components: vec![c],
    });
    assert_eq!(reduced.components.len(), 1);
    assert!(reduced.components[0].path_support.is_empty());
    assert_eq!(reduced.components[0].output.quantum[&q(0)], x(0));
    assert_eq!(reduced.components[0].scalar, Scalar::one());
    assert_eq!(vector(&before), vector(&reduced.components[0]));
}
