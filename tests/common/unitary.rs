//! Small independent matrix oracle for frontend tests, not a proof backend.
//! Compare every complex matrix entry, including relative and global phases.
#![allow(dead_code)] // Each integration test uses a different subset of helpers.

use irene::ir::{
    Block, Gate, NumericConstant, NumericExpr, NumericExprKind, Program, Qubit, StatementKind,
};
use std::f64::consts::{FRAC_1_SQRT_2, PI, TAU};

pub type Complex = (f64, f64);
pub type Matrix2 = [[Complex; 2]; 2];
const ZERO: Complex = (0.0, 0.0);
const ONE: Complex = (1.0, 0.0);

pub fn cis(x: f64) -> Complex {
    (x.cos(), x.sin())
}
pub fn mul(a: Complex, b: Complex) -> Complex {
    (a.0 * b.0 - a.1 * b.1, a.0 * b.1 + a.1 * b.0)
}
fn add(a: Complex, b: Complex) -> Complex {
    (a.0 + b.0, a.1 + b.1)
}

fn number(e: &NumericExpr) -> f64 {
    match &e.kind {
        NumericExprKind::Rational(x) => {
            x.numer().to_string().parse::<f64>().unwrap()
                / x.denom().to_string().parse::<f64>().unwrap()
        }
        NumericExprKind::Constant(c) => match c {
            NumericConstant::Pi => PI,
            NumericConstant::Tau => TAU,
            NumericConstant::Euler => std::f64::consts::E,
        },
        NumericExprKind::Neg(a) => -number(a),
        NumericExprKind::Add(a, b) => number(a) + number(b),
        NumericExprKind::Sub(a, b) => number(a) - number(b),
        NumericExprKind::Mul(a, b) => number(a) * number(b),
        NumericExprKind::Div(a, b) => number(a) / number(b),
        NumericExprKind::Input(_) => panic!("matrix oracle requires constant parameters"),
    }
}

pub fn single(gate: Gate, angle: f64) -> Matrix2 {
    let c = (angle / 2.0).cos();
    let s = (angle / 2.0).sin();
    match gate {
        Gate::X => [[ZERO, ONE], [ONE, ZERO]],
        Gate::Y => [[ZERO, (0.0, -1.0)], [(0.0, 1.0), ZERO]],
        Gate::Z => [[ONE, ZERO], [ZERO, (-1.0, 0.0)]],
        Gate::H => [
            [(FRAC_1_SQRT_2, 0.0); 2],
            [(FRAC_1_SQRT_2, 0.0), (-FRAC_1_SQRT_2, 0.0)],
        ],
        Gate::S => single(Gate::P, PI / 2.0),
        Gate::Sdg => single(Gate::P, -PI / 2.0),
        Gate::T => single(Gate::P, PI / 4.0),
        Gate::Tdg => single(Gate::P, -PI / 4.0),
        Gate::P => [[ONE, ZERO], [ZERO, cis(angle)]],
        Gate::Rx => [[(c, 0.0), (0.0, -s)], [(0.0, -s), (c, 0.0)]],
        Gate::Ry => [[(c, 0.0), (-s, 0.0)], [(s, 0.0), (c, 0.0)]],
        Gate::Rz => [[cis(-angle / 2.0), ZERO], [ZERO, cis(angle / 2.0)]],
        _ => panic!("not a single-qubit gate: {gate:?}"),
    }
}

/// The specified CU matrix, independent of any Euler-angle decomposition.
pub fn u(theta: f64, phi: f64, lambda: f64, gamma: f64) -> Matrix2 {
    let c = (theta / 2.0).cos();
    let s = (theta / 2.0).sin();
    [
        [
            mul(cis(gamma), (c, 0.0)),
            mul(cis(gamma + lambda), (-s, 0.0)),
        ],
        [
            mul(cis(gamma + phi), (s, 0.0)),
            mul(cis(gamma + phi + lambda), (c, 0.0)),
        ],
    ]
}

pub fn apply(state: &mut [Complex], controls: &[usize], target: usize, matrix: Matrix2) {
    let target = 1 << target;
    let mask = controls.iter().fold(0, |mask, q| mask | (1 << q));
    for i in 0..state.len() {
        if i & target != 0 || i & mask != mask {
            continue;
        }
        let j = i | target;
        let (x, y) = (state[i], state[j]);
        state[i] = add(mul(matrix[0][0], x), mul(matrix[0][1], y));
        state[j] = add(mul(matrix[1][0], x), mul(matrix[1][1], y));
    }
}

fn wires(p: &Program) -> Vec<Qubit> {
    p.quantum_registers
        .iter()
        .flat_map(|r| {
            (0..r.width).map(|index| Qubit {
                register: r.id,
                index,
            })
        })
        .collect()
}

fn evolve(block: &Block, wires: &[Qubit], state: &mut [Complex]) {
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::Scope(b) => evolve(b, wires, state),
            StatementKind::Apply {
                gate,
                parameters,
                qubits,
            } => {
                let q: Vec<_> = qubits
                    .iter()
                    .map(|q| wires.iter().position(|w| w == q).unwrap())
                    .collect();
                if *gate == Gate::Swap {
                    let (a, b) = (1 << q[0], 1 << q[1]);
                    for i in 0..state.len() {
                        if i & a == 0 && i & b != 0 {
                            state.swap(i, i ^ a ^ b);
                        }
                    }
                    continue;
                }
                let base = match gate {
                    Gate::Cx | Gate::Ccx => Gate::X,
                    Gate::Cy => Gate::Y,
                    Gate::Cz | Gate::Ccz => Gate::Z,
                    Gate::Cp => Gate::P,
                    Gate::Crx => Gate::Rx,
                    Gate::Cry => Gate::Ry,
                    Gate::Crz => Gate::Rz,
                    other => *other,
                };
                let angle = parameters.first().map(number).unwrap_or(0.0);
                apply(
                    state,
                    &q[..q.len() - 1],
                    *q.last().unwrap(),
                    single(base, angle),
                );
            }
            _ => panic!("matrix oracle only accepts unitary programs"),
        }
    }
}

pub fn assert_action(p: &Program, expected: impl Fn(&mut [Complex])) {
    let wires = wires(p);
    assert!(wires.len() <= 8, "dense oracle is only for small tests");
    for column in 0..1 << wires.len() {
        let mut actual = vec![ZERO; 1 << wires.len()];
        actual[column] = ONE;
        let mut reference = actual.clone();
        evolve(&p.body, &wires, &mut actual);
        expected(&mut reference);
        for (row, (a, b)) in actual.iter().zip(&reference).enumerate() {
            assert!(
                (a.0 - b.0).hypot(a.1 - b.1) < 1e-10,
                "matrix entry ({row},{column}): {a:?} != {b:?}"
            );
        }
    }
}

pub fn assert_same(left: &Program, right: &Program) {
    let right_wires = wires(right);
    assert_eq!(wires(left).len(), right_wires.len());
    assert_action(left, |state| evolve(&right.body, &right_wires, state));
}

pub fn assert_fresh_ids(p: &Program) {
    let mut ids = Vec::new();
    p.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort_unstable();
    assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
}
