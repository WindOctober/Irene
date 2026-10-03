use super::*;
use crate::ir::{ClassicalBit, Qubit, SymbolId};
use crate::symbolic::{HistoryEntry, PhaseCoefficient, PhasePolynomial};
use std::collections::BTreeMap;

fn rational(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

fn identity(n: usize) -> (Component, HybridMemory) {
    let mut input = HybridMemory::default();
    for index in 0..n {
        let q = Qubit {
            register: SymbolId(0),
            index,
        };
        input
            .quantum
            .insert(q.clone(), BooleanPolynomial::variable(Variable::Input(q)));
    }
    (
        Component {
            guard: vec![],
            scalar: Scalar::one(),
            path_support: Default::default(),
            phase: PhasePolynomial::zero(),
            output: input.clone(),
        },
        input,
    )
}

fn bit(p: &BooleanPolynomial, values: &BTreeMap<Variable, bool>) -> bool {
    p.evaluate::<std::convert::Infallible>(|v| Ok(*values.get(v).expect("unbound variable")))
        .unwrap()
}

// Independent exact enumeration for real, half-turn fixtures. No production
// path elimination or trace evaluator is used to establish the expected sum.
fn scalar(s: &Scalar, values: &BTreeMap<Variable, bool>) -> BigRational {
    match s {
        Scalar::Rational(r) => r.clone(),
        Scalar::Add(a, b) => scalar(a, values) + scalar(b, values),
        Scalar::Mul(a, b) => scalar(a, values) * scalar(b, values),
        Scalar::Neg(a) => -scalar(a, values),
        Scalar::Inverse(a) => scalar(a, values).recip(),
        Scalar::Select {
            condition,
            when_true,
            when_false,
        } => scalar(
            if bit(condition, values) {
                when_true
            } else {
                when_false
            },
            values,
        ),
        _ => panic!("fixture requires rational scalar arithmetic"),
    }
}

fn amplitude(c: &Component, values: &BTreeMap<Variable, bool>) -> BigRational {
    if c.guard.iter().any(|p| bit(p, values)) {
        return rational(0, 1);
    }
    let mut turns = rational(0, 1);
    for (p, coefficient) in c.phase.selectors() {
        if bit(&p, values) {
            turns += coefficient.as_rational().unwrap();
        }
    }
    let half_turns = turns * rational(2, 1);
    assert!(half_turns.is_integer());
    let sign = if half_turns.to_integer() % BigInt::from(2) == BigInt::from(0) {
        1
    } else {
        -1
    };
    scalar(&c.scalar, values) * rational(sign, 1)
}

fn check(c: Component, input: HybridMemory, expected: BigRational) {
    let inputs: Vec<_> = input.quantum.keys().cloned().collect();
    let variables: Vec<_> = inputs
        .iter()
        .cloned()
        .map(Variable::Input)
        .chain(c.path_support.iter().copied().map(Variable::Path))
        .collect();
    assert!(variables.len() < 16);
    let mut before = rational(0, 1);
    for bits in 0..(1_usize << variables.len()) {
        let values = variables
            .iter()
            .enumerate()
            .map(|(i, v)| (v.clone(), bits & (1 << i) != 0))
            .collect();
        if inputs
            .iter()
            .all(|q| bit(&c.output.quantum[q], &values) == values[&Variable::Input(q.clone())])
        {
            before += amplitude(&c, &values);
        }
    }
    before /= BigRational::from_integer(BigInt::from(1) << inputs.len());
    assert_eq!(before, expected);
    let out = normalized_trace_component(c, &input).unwrap();
    assert!(out.output.quantum.is_empty());
    assert!(out.output.classical.is_empty());
    assert!(out.output.history.is_empty());
    let paths: Vec<_> = out
        .path_support
        .iter()
        .copied()
        .map(Variable::Path)
        .collect();
    let mut after = rational(0, 1);
    for bits in 0..(1_usize << paths.len()) {
        let values = paths
            .iter()
            .enumerate()
            .map(|(i, v)| (v.clone(), bits & (1 << i) != 0))
            .collect();
        after += amplitude(&out, &values);
    }
    assert_eq!(after, expected);
}

#[test]
fn identity_sums_all_inputs_including_unused_ones() {
    for n in 0..=4 {
        let (c, input) = identity(n);
        check(c, input, rational(1, 1));
    }
}

#[test]
fn x_has_no_diagonal_paths_and_z_cancels_amplitudes() {
    let (mut c, input) = identity(1);
    let q = input.quantum.keys().next().unwrap().clone();
    c.output
        .quantum
        .insert(q.clone(), input.quantum[&q].complement());
    check(c, input, rational(0, 1));
    let (mut c, input) = identity(1);
    c.phase.add_boolean(
        &input.quantum[&q],
        PhaseCoefficient::rational(rational(1, 2)),
    );
    check(c, input, rational(0, 1));
}

#[test]
fn global_phase_is_preserved_and_controlled_z_has_half_trace() {
    let (mut c, input) = identity(2);
    c.phase.add_boolean(
        &BooleanPolynomial::one(),
        PhaseCoefficient::rational(rational(1, 2)),
    );
    check(c, input, rational(-1, 1));
    let (mut c, input) = identity(2);
    let values: Vec<_> = input.quantum.values().collect();
    c.phase.add_boolean(
        &values[0].and(values[1]),
        PhaseCoefficient::rational(rational(1, 2)),
    );
    check(c, input, rational(1, 2));
}

#[test]
fn fresh_input_binders_do_not_capture_existing_hadamard_paths() {
    // H;H: (1/2) sum_{y,z} (-1)^(xy+yz) |z>.
    let (mut c, input) = identity(1);
    let q = input.quantum.keys().next().unwrap().clone();
    let y = BooleanPolynomial::variable(Variable::Path(0));
    let z = BooleanPolynomial::variable(Variable::Path(7));
    c.path_support = [0, 7].into();
    c.scalar = Scalar::rational(rational(1, 2));
    c.phase.add_boolean(
        &input.quantum[&q].and(&y).xor(&y.and(&z)),
        PhaseCoefficient::rational(rational(1, 2)),
    );
    c.output.quantum.insert(q, z);
    check(c, input, rational(1, 1));
}

#[test]
fn input_dependencies_in_guards_and_scalar_conditions_are_rebound() {
    let (mut c, input) = identity(1);
    let q = input.quantum.keys().next().unwrap().clone();
    let x = input.quantum[&q].clone();
    let y = BooleanPolynomial::variable(Variable::Path(3));
    c.path_support.insert(3);
    c.guard.push(x.xor(&y));
    c.output.quantum.insert(q, y);
    c.scalar = Scalar::select(x, Scalar::rational(rational(-1, 1)), Scalar::one());
    check(c, input, rational(0, 1));
}

#[test]
fn invalid_interfaces_and_history_are_declined() {
    let (base, input) = identity(1);
    let q = input.quantum.keys().next().unwrap().clone();
    let b = ClassicalBit {
        register: SymbolId(1),
        index: 0,
    };
    for case in 0..7 {
        let mut c = base.clone();
        let mut i = input.clone();
        match case {
            0 => {
                c.output.quantum.clear();
            }
            1 => {
                i.quantum.insert(q.clone(), BooleanPolynomial::zero());
            }
            2 => {
                c.output
                    .classical
                    .insert(b.clone(), BooleanPolynomial::zero());
            }
            3 => {
                i.classical.insert(b.clone(), BooleanPolynomial::zero());
            }
            4 => {
                c.output.history.push(HistoryEntry::Discard {
                    value: BooleanPolynomial::zero(),
                });
            }
            5 => {
                i.history.push(HistoryEntry::Discard {
                    value: BooleanPolynomial::zero(),
                });
            }
            6 => {
                c.path_support.insert(usize::MAX);
            }
            _ => unreachable!(),
        }
        assert!(normalized_trace_component(c, &i).is_none(), "case {case}");
    }
}
