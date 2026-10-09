//! Small independent state-vector oracle for phase-sensitive import regressions.
use iqir::*;

#[derive(Clone, Copy, Default, Debug)]
struct C(f64, f64);
impl std::ops::Add for C {
    type Output = Self;
    fn add(self, b: Self) -> Self {
        C(self.0 + b.0, self.1 + b.1)
    }
}
impl std::ops::Mul for C {
    type Output = Self;
    fn mul(self, b: Self) -> Self {
        C(self.0 * b.0 - self.1 * b.1, self.0 * b.1 + self.1 * b.0)
    }
}
fn cis(a: f64) -> C {
    C(a.cos(), a.sin())
}
fn numeric(e: &NumericExpr) -> f64 {
    use NumericExprKind as N;
    match &e.kind {
        N::Rational(r) => {
            r.numer().to_string().parse::<f64>().unwrap()
                / r.denom().to_string().parse::<f64>().unwrap()
        }
        N::Constant(NumericConstant::Pi) => std::f64::consts::PI,
        N::Constant(NumericConstant::Tau) => std::f64::consts::TAU,
        N::Constant(NumericConstant::Euler) => std::f64::consts::E,
        N::Neg(a) => -numeric(a),
        N::Add(a, b) => numeric(a) + numeric(b),
        N::Sub(a, b) => numeric(a) - numeric(b),
        N::Mul(a, b) => numeric(a) * numeric(b),
        N::Div(a, b) => numeric(a) / numeric(b),
        N::Input(_) => panic!(),
    }
}
fn block(b: &Block, state: &mut [C], mask: usize, inverse: bool) {
    if inverse {
        for s in b.statements.iter().rev() {
            statement(s, state, mask, true);
        }
    } else {
        for s in &b.statements {
            statement(s, state, mask, false);
        }
    }
}
fn statement(s: &Statement, state: &mut [C], mask: usize, inverse: bool) {
    let sign = if inverse { -1.0 } else { 1.0 };
    match &s.kind {
        StatementKind::Scope(b) => block(b, state, mask, inverse),
        StatementKind::Unitary {
            controls,
            power,
            body,
        } => {
            let mask = controls.iter().fold(mask, |m, q| m | (1 << q.index));
            for _ in 0..power.unsigned_abs() {
                block(body, state, mask, inverse ^ (*power < 0));
            }
        }
        StatementKind::GlobalPhase(e) => {
            for (index, a) in state.iter_mut().enumerate() {
                if index & mask == mask {
                    *a = *a * cis(sign * numeric(e));
                }
            }
        }
        StatementKind::Apply {
            gate,
            parameters,
            qubits,
        } => {
            let theta = parameters.first().map(numeric).unwrap_or(0.0) * sign;
            let m = match gate {
                Gate::X => [[C(0.0, 0.0), C(1.0, 0.0)], [C(1.0, 0.0), C(0.0, 0.0)]],
                Gate::H => {
                    let a = std::f64::consts::FRAC_1_SQRT_2;
                    [[C(a, 0.0), C(a, 0.0)], [C(a, 0.0), C(-a, 0.0)]]
                }
                Gate::S => [
                    [C(1.0, 0.0), C(0.0, 0.0)],
                    [C(0.0, 0.0), cis(sign * std::f64::consts::FRAC_PI_2)],
                ],
                Gate::P => [[C(1.0, 0.0), C(0.0, 0.0)], [C(0.0, 0.0), cis(theta)]],
                Gate::Ry => {
                    let (s, c) = (theta / 2.0).sin_cos();
                    [[C(c, 0.0), C(-s, 0.0)], [C(s, 0.0), C(c, 0.0)]]
                }
                Gate::Rx => {
                    let (s, c) = (theta / 2.0).sin_cos();
                    [[C(c, 0.0), C(0.0, -s)], [C(0.0, -s), C(c, 0.0)]]
                }
                Gate::Rz => [
                    [cis(-theta / 2.0), C(0.0, 0.0)],
                    [C(0.0, 0.0), cis(theta / 2.0)],
                ],
                _ => panic!("unsupported test gate {gate:?}"),
            };
            assert_eq!(qubits.len(), 1);
            let target = 1 << qubits[0].index;
            for index in 0..state.len() {
                if index & target == 0 && index & mask == mask {
                    let a = state[index];
                    let b = state[index | target];
                    state[index] = m[0][0] * a + m[0][1] * b;
                    state[index | target] = m[1][0] * a + m[1][1] * b;
                }
            }
        }
        _ => panic!("not a unitary test program"),
    }
}
fn matrix(source: &str) -> Vec<Vec<C>> {
    let p = frontend::parse_str(
        &format!("OPENQASM 3; include \"stdgates.inc\"; {source}"),
        "matrix.qasm",
    )
    .unwrap();
    assert_eq!(p.quantum_registers.len(), 1);
    let dimension = 1 << p.quantum_registers[0].width;
    (0..dimension)
        .map(|i| {
            let mut state = vec![C::default(); dimension];
            state[i] = C(1.0, 0.0);
            block(&p.body, &mut state, 0, false);
            state
        })
        .collect()
}
fn close(a: C, b: C) {
    assert!(
        (a.0 - b.0).abs() + (a.1 - b.1).abs() < 1e-12,
        "{a:?} != {b:?}"
    );
}
fn same(a: Vec<Vec<C>>, b: Vec<Vec<C>>) {
    for (a, b) in a.into_iter().flatten().zip(b.into_iter().flatten()) {
        close(a, b);
    }
}

#[test]
fn builtin_u_uses_qasm3_theta_phase_even_under_control() {
    let (theta, phi, lambda) = (0.7_f64, 0.2_f64, -0.4_f64);
    let (s, c) = (theta / 2.0).sin_cos();
    let phase = cis(theta / 2.0);
    let u = [
        [phase * C(c, 0.0), phase * cis(lambda) * C(-s, 0.0)],
        [
            phase * cis(phi) * C(s, 0.0),
            phase * cis(phi + lambda) * C(c, 0.0),
        ],
    ];
    let plain = matrix("qubit q; U(0.7,0.2,-0.4) q;");
    for col in 0..2 {
        for row in 0..2 {
            close(plain[col][row], u[row][col]);
        }
    }
    let controlled = matrix(
        "gate k(theta,phi,lam) a {U(theta,phi,lam) a;} qubit[2] q; ctrl @ k(0.7,0.2,-0.4) q[0],q[1];",
    );
    for col in 0..4 {
        for row in 0..4 {
            let expected = if col & 1 == 0 {
                C(f64::from(row == col), 0.0)
            } else if row & 1 == 0 {
                C::default()
            } else {
                u[row >> 1][col >> 1]
            };
            close(controlled[col][row], expected);
        }
    }
}

#[test]
fn composite_inverse_reverses_order_and_integer_power_repeats_whole_body() {
    same(
        matrix("gate compound a {h a; s a;} qubit q; compound q; inv @ compound q;"),
        matrix("qubit q;"),
    );
    same(
        matrix("gate compound a {h a; s a;} qubit q; pow(2) @ compound q;"),
        matrix("qubit q; h q; s q; h q; s q;"),
    );
    same(
        matrix(
            "gate compound a {h a; s a;} qubit[2] q; ctrl @ compound q[0],q[1]; inv @ ctrl @ compound q[0],q[1];",
        ),
        matrix("qubit[2] q;"),
    );
}

#[test]
fn nested_custom_global_phase_is_a_relative_phase_under_control() {
    same(
        matrix(
            "gate phasey(theta) a {gphase(theta); x a;} gate nested(theta) a {phasey(theta) a;} qubit[2] q; ctrl @ nested(pi) q[0],q[1]; ctrl @ nested(pi) q[0],q[1];",
        ),
        matrix("qubit[2] q;"),
    );
    let result = matrix("gate phasey a {gphase(pi/2);} qubit[2] q; ctrl @ phasey q[0],q[1];");
    for (col, column) in result.iter().enumerate() {
        for (row, entry) in column.iter().enumerate() {
            close(
                *entry,
                if row != col {
                    C::default()
                } else if col & 1 == 0 {
                    C(1.0, 0.0)
                } else {
                    C(0.0, 1.0)
                },
            );
        }
    }
}
