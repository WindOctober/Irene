//! Independent dense-matrix checks of the lowered IR (all basis columns).
use irene::frontend::openqasm2;
use irene::ir::{
    Block, Gate, NumericConstant, NumericExpr, NumericExprKind, Program, StatementKind,
};
use std::f64::consts::PI;
type C = (f64, f64);
fn add(a: C, b: C) -> C {
    (a.0 + b.0, a.1 + b.1)
}
fn mul(a: C, b: C) -> C {
    (a.0 * b.0 - a.1 * b.1, a.0 * b.1 + a.1 * b.0)
}
fn cis(x: f64) -> C {
    (x.cos(), x.sin())
}
fn number(e: &NumericExpr) -> f64 {
    match &e.kind {
        NumericExprKind::Rational(x) => {
            x.numer().to_string().parse::<f64>().unwrap()
                / x.denom().to_string().parse::<f64>().unwrap()
        }
        NumericExprKind::Constant(NumericConstant::Pi) => PI,
        NumericExprKind::Neg(a) => -number(a),
        NumericExprKind::Add(a, b) => number(a) + number(b),
        NumericExprKind::Sub(a, b) => number(a) - number(b),
        NumericExprKind::Mul(a, b) => number(a) * number(b),
        NumericExprKind::Div(a, b) => number(a) / number(b),
        _ => panic!("nonconstant test parameter"),
    }
}
fn evolve(b: &Block, s: &mut [C]) {
    for statement in &b.statements {
        match &statement.kind {
            StatementKind::Scope(b) => evolve(b, s),
            StatementKind::Apply {
                gate,
                parameters,
                qubits,
            } => {
                if *gate == Gate::Ccz {
                    let mask = qubits.iter().fold(0, |mask, q| mask | (1 << q.index));
                    for (index, amplitude) in s.iter_mut().enumerate() {
                        if index & mask == mask {
                            *amplitude = (-amplitude.0, -amplitude.1);
                        }
                    }
                    continue;
                }
                let a = parameters.first().map(number).unwrap_or(0.0);
                let (base, controlled) = match gate {
                    Gate::Cx => (Gate::X, true),
                    Gate::Cp => (Gate::P, true),
                    Gate::Cry => (Gate::Ry, true),
                    Gate::Crz => (Gate::Rz, true),
                    g => (*g, false),
                };
                let matrix = match base {
                    Gate::X => [[(0., 0.), (1., 0.)], [(1., 0.), (0., 0.)]],
                    Gate::H => {
                        let h = 1. / 2f64.sqrt();
                        [[(h, 0.), (h, 0.)], [(h, 0.), (-h, 0.)]]
                    }
                    Gate::P => [[(1., 0.), (0., 0.)], [(0., 0.), cis(a)]],
                    Gate::Ry => {
                        let c = (a / 2.).cos();
                        let t = (a / 2.).sin();
                        [[(c, 0.), (-t, 0.)], [(t, 0.), (c, 0.)]]
                    }
                    Gate::Rz => [[cis(-a / 2.), (0., 0.)], [(0., 0.), cis(a / 2.)]],
                    _ => panic!("unsupported test IR gate {base:?}"),
                };
                let target = 1 << qubits.last().unwrap().index;
                for i in 0..s.len() {
                    if i & target != 0 || (controlled && i & (1 << qubits[0].index) == 0) {
                        continue;
                    }
                    let j = i | target;
                    let x = s[i];
                    let y = s[j];
                    s[i] = add(mul(matrix[0][0], x), mul(matrix[0][1], y));
                    s[j] = add(mul(matrix[1][0], x), mul(matrix[1][1], y));
                }
            }
            _ => panic!("nonunitary test circuit"),
        }
    }
}
fn check(p: &Program, n: usize, expected: impl Fn(usize) -> Vec<C>) {
    let mut phase = None;
    for col in 0..1 << n {
        let mut actual = vec![(0., 0.); 1 << n];
        actual[col] = (1., 0.);
        evolve(&p.body, &mut actual);
        for (a, e) in actual.into_iter().zip(expected(col)) {
            if phase.is_none() && e.0 * e.0 + e.1 * e.1 > 0.1 {
                let d = e.0 * e.0 + e.1 * e.1;
                let z = mul(a, (e.0, -e.1));
                phase = Some((z.0 / d, z.1 / d));
            }
            let e = mul(phase.unwrap_or((1., 0.)), e);
            assert!(
                (a.0 - e.0).abs() < 1e-9 && (a.1 - e.1).abs() < 1e-9,
                "column {col}: {a:?} != {e:?}"
            );
        }
    }
    let z = phase.unwrap();
    assert!((z.0 * z.0 + z.1 * z.1 - 1.).abs() < 1e-9);
    let mut ids = Vec::new();
    p.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort_unstable();
    assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
}
fn q2(n: usize, call: &str) -> Program {
    openqasm2::parse_str(
        &format!("OPENQASM 2.0; include \"qelib1.inc\"; qreg q[{n}]; {call}"),
        "test",
    )
    .unwrap()
}
#[test]
fn controlled_u_preserves_all_four_parameters() {
    for (theta, phi, lambda, gamma) in [(0.7_f64, -0.4, 0.2, 0.9), (0., 0., 0., 0.6)] {
        let call = format!("cu({theta},{phi},{lambda},{gamma}) q[0],q[1];");
        let p = q2(2, &call);
        {
            check(&p, 2, |i| {
                let mut v = vec![(0., 0.); 4];
                if i & 1 == 0 {
                    v[i] = (1., 0.);
                } else {
                    let c = (theta / 2.).cos();
                    let s = (theta / 2.).sin();
                    if i & 2 == 0 {
                        v[1] = mul(cis(gamma), (c, 0.));
                        v[3] = mul(cis(gamma + phi), (s, 0.));
                    } else {
                        v[1] = mul(cis(gamma + lambda), (-s, 0.));
                        v[3] = mul(cis(gamma + phi + lambda), (c, 0.));
                    }
                }
                v
            });
        }
    }
}
#[test]
fn rotations_and_relative_phase_toffoli() {
    let a: f64 = 0.73;
    for name in ["rxx", "rzz"] {
        check(&q2(2, &format!("{name}({a}) q[0],q[1];")), 2, |i| {
            let mut v = vec![(0., 0.); 4];
            if name == "rxx" {
                v[i] = ((a / 2.).cos(), 0.);
                v[i ^ 3] = (0., -(a / 2.).sin());
            } else {
                v[i] = cis(if i == 0 || i == 3 { -a / 2. } else { a / 2. });
            }
            v
        });
    }
    check(&q2(3, "rccx q[0],q[1],q[2];"), 3, |i| {
        let mut v = vec![(0., 0.); 8];
        let (j, z) = match i {
            3 => (7, (0., 1.)),
            7 => (3, (0., -1.)),
            5 => (5, (-1., 0.)),
            _ => (i, (1., 0.)),
        };
        v[j] = z;
        v
    });
    check(&q2(4, "rc3x q[0],q[1],q[2],q[3];"), 4, |i| {
        let mut v = vec![(0., 0.); 16];
        let (j, z) = match i {
            3 => (3, (0., 1.)),
            11 => (11, (0., -1.)),
            7 => (15, (-1., 0.)),
            15 => (7, (1., 0.)),
            _ => (i, (1., 0.)),
        };
        v[j] = z;
        v
    });
}
#[test]
fn multi_controlled_x_and_sqrt_x() {
    for (name, controls, sqrt) in [
        ("csx", 1, true),
        ("c3sqrtx", 3, true),
        ("c3x", 3, false),
        ("c4x", 4, false),
    ] {
        let operands = (0..=controls)
            .map(|i| format!("q[{i}]"))
            .collect::<Vec<_>>()
            .join(",");
        check(
            &q2(controls + 1, &format!("{name} {operands};")),
            controls + 1,
            |i| {
                let mut v = vec![(0., 0.); 1 << (controls + 1)];
                let mask = (1 << controls) - 1;
                if i & mask != mask {
                    v[i] = (1., 0.);
                } else if sqrt {
                    v[i] = (0.5, 0.5);
                    v[i ^ (1 << controls)] = (0.5, -0.5);
                } else {
                    v[i ^ (1 << controls)] = (1., 0.);
                }
                v
            },
        );
    }
}
#[test]
fn explicit_override_does_not_change_earlier_gate_definitions() {
    let p = q2(
        2,
        "gate saved(t) a,b { rzz(t) a,b; } gate rzz(t) a,b { x b; } saved(0.73) q[0],q[1];",
    );
    check(&p, 2, |i| {
        let mut v = vec![(0., 0.); 4];
        v[i] = cis(if i == 0 || i == 3 { 0. } else { 0.73 });
        v
    });
}

#[test]
fn source_definitions_override_extensions_but_not_standard_gates() {
    check(
        &q2(2, "gate rzz(t) a,b { x b; } rzz(0.2) q[0],q[1];"),
        2,
        |i| {
            let mut v = vec![(0., 0.); 4];
            v[i ^ 2] = (1., 0.);
            v
        },
    );
    for body in [
        "gate rzz(t) a,b {} gate rzz(t) a,b {}",
        "gate h a { x a; }",
        "gate saved a,b { csx a,b; } gate csx a,b { csx a,b; }",
    ] {
        let source = format!("OPENQASM 2.0; include \"qelib1.inc\"; {body}");
        assert!(openqasm2::parse_str(&source, "invalid").is_err(), "{body}");
    }
}

#[test]
fn embedded_gates_keep_their_original_dependencies() {
    check(
        &q2(5, "gate c3x a,b,c,d {} c4x q[0],q[1],q[2],q[3],q[4];"),
        5,
        |i| {
            let mut v = vec![(0., 0.); 32];
            v[if i & 15 == 15 { i ^ 16 } else { i }] = (1., 0.);
            v
        },
    );
    // Pin native bindings too: otherwise the new ccz indirectly calls itself.
    check(
        &q2(
            3,
            "gate saved a,b,c { ccz a,b,c; } gate ccz a,b,c { saved a,b,c; } ccz q[0],q[1],q[2];",
        ),
        3,
        |i| {
            let mut v = vec![(0., 0.); 8];
            v[i] = (if i == 7 { -1. } else { 1. }, 0.);
            v
        },
    );
}

#[test]
fn extension_arity_and_broadcast_are_validated() {
    for body in [
        "cu(1,2,3) q[0],q[1];",
        "cu(1,2,3,4) q[0],q[0];",
        "csx(1) q[0],q[1];",
        "rzz(1) q[0];",
        "rxx(1) q[0],q[2];",
        "c3x q[0],q[1];",
    ] {
        let source = format!("OPENQASM 2.0; include \"qelib1.inc\"; qreg q[2]; {body}");
        assert!(openqasm2::parse_str(&source, "invalid").is_err(), "{body}");
    }
    assert!(
        openqasm2::parse_str("OPENQASM 2.0; qreg q[2]; csx q[0],q[1];", "missing-include").is_err()
    );
    let broadcast = openqasm2::parse_str(
        "OPENQASM 2.0; include \"qelib1.inc\"; qreg a[2]; qreg b[2]; cu(0.1,0.2,0.3,0.4) a,b;",
        "broadcast",
    )
    .unwrap();
    assert_eq!(
        broadcast.operation_count(),
        2 * q2(2, "cu(0.1,0.2,0.3,0.4) q[0],q[1];").operation_count()
    );
    assert!(
        openqasm2::parse_str(
            "OPENQASM 2.0; include \"qelib1.inc\"; qreg a[2]; qreg b[3]; cu(0.1,0.2,0.3,0.4) a,b;",
            "width-mismatch"
        )
        .is_err()
    );
}
