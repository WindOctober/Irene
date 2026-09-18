mod common;

use common::unitary::{assert_fresh_ids, assert_same};
use irene::frontend::openqasm3;
use irene::ir::{
    Block, ClassicalBit, ClassicalExpr, ClassicalExprKind, Program, Qubit, Statement, StatementKind,
};
use irene::symbolic::{
    BooleanPolynomial, ExecutionConfig, OutputSelection, SymbolicError, Variable, execute,
};
use std::collections::BTreeMap;

fn parse(body: &str) -> Program {
    let p = openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
        "runtime-angle.qasm",
    )
    .unwrap();
    assert_fresh_ids(&p);
    p
}

fn word(body: &str, name: &str) -> u64 {
    let p = parse(body);
    let r = p
        .classical_registers
        .iter()
        .find(|r| r.name == name)
        .unwrap();
    let cells: Vec<_> = (0..r.width)
        .map(|index| ClassicalBit {
            register: r.id,
            index,
        })
        .collect();
    let hps = execute(
        &p,
        &ExecutionConfig::zero(),
        &OutputSelection::new([], cells.clone()),
    )
    .unwrap();
    assert!(!hps.components.is_empty());
    let mut results = Vec::new();
    for c in &hps.components {
        results.push(
            cells
                .iter()
                .enumerate()
                .map(|(i, b)| {
                    let v = &c.output.classical[b];
                    assert!(v.is_one() || v.is_zero());
                    u64::from(v.is_one()) << i
                })
                .sum::<u64>(),
        );
    }
    assert!(results.iter().all(|v| *v == results[0]));
    results[0]
}

// Interpret classical IR independently, then use the matrix oracle for every
// quantum input column. This retains global and controlled relative phases.
fn specialize_classical(mut p: Program) -> Program {
    fn value(e: &ClassicalExpr, m: &BTreeMap<ClassicalBit, bool>) -> bool {
        match &e.kind {
            ClassicalExprKind::Bool(v) => *v,
            ClassicalExprKind::Bit(b) => m[b],
            ClassicalExprKind::Not(a) => !value(a, m),
            ClassicalExprKind::And(a, b) => value(a, m) & value(b, m),
            ClassicalExprKind::Or(a, b) => value(a, m) | value(b, m),
            ClassicalExprKind::Xor(a, b) => value(a, m) ^ value(b, m),
            ClassicalExprKind::Eq(a, b) => value(a, m) == value(b, m),
        }
    }
    fn run(b: &Block, m: &mut BTreeMap<ClassicalBit, bool>, gates: &mut Vec<Statement>) {
        for s in &b.statements {
            match &s.kind {
                StatementKind::Assign { target, value: e } => {
                    let v = value(e, m);
                    m.insert(target.clone(), v);
                }
                StatementKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => run(
                    if value(condition, m) {
                        then_branch
                    } else {
                        else_branch
                    },
                    m,
                    gates,
                ),
                StatementKind::Scope(b) => run(b, m, gates),
                StatementKind::Apply { .. } => gates.push(s.clone()),
                _ => panic!("oracle requires a unitary quantum body"),
            }
        }
        for r in &b.classical_registers {
            for index in 0..r.width {
                m.remove(&ClassicalBit {
                    register: r.id,
                    index,
                });
            }
        }
    }
    let mut gates = Vec::new();
    run(&p.body, &mut BTreeMap::new(), &mut gates);
    p.body.statements = gates;
    p.body.classical_registers.clear();
    p.classical_registers.clear();
    p
}

#[test]
fn initialization_quantizes_radians_and_reduces_modulo_one_turn() {
    for (expr, expected) in [
        ("0", 0),
        ("pi/2", 2),
        ("pi", 4),
        ("3*pi/2", 6),
        ("-pi/2", 6),
        ("2*pi", 0),
        ("5*pi/2", 2),
        ("0.39", 0),
        ("0.40", 1),
        ("-0.40", 7),
        ("(1/2)*pi", 0),
        ("(1.0/2)*pi", 2),
    ] {
        assert_eq!(
            word(&format!("angle[3] a={expr};"), "a"),
            expected,
            "{expr}"
        );
    }
    assert_eq!(word("angle a=pi;", "a"), 1 << 31);
    assert_eq!(word("angle[61] a=pi;", "a"), (1_u64 << 60) - 45);
    assert_eq!(word("const int n=3; angle[n] a=angle[n](\"101\");", "a"), 5);
}

#[test]
fn angle_arithmetic_matches_all_small_modular_words() {
    for n in 1..=3 {
        let mask = (1_u64 << n) - 1;
        for a in 0..=mask {
            let setup = format!("angle[{n}] a=angle[{n}](\"{a:0n$b}\");");
            assert_eq!(
                word(&format!("{setup} a=-a;"), "a"),
                a.wrapping_neg() & mask
            );
            assert_eq!(word(&format!("{setup} a=~a;"), "a"), !a & mask);
            for shift in 0..=n + 1 {
                assert_eq!(
                    word(&format!("{setup} a<<={shift};"), "a"),
                    (a << shift) & mask
                );
                assert_eq!(word(&format!("{setup} a>>={shift};"), "a"), a >> shift);
            }
            for b in 0..=mask {
                let setup = format!("{setup} angle[{n}] b=angle[{n}](\"{b:0n$b}\");");
                for (op, expected) in [
                    ("+", a.wrapping_add(b)),
                    ("-", a.wrapping_sub(b)),
                    ("^", a ^ b),
                    ("&", a & b),
                    ("|", a | b),
                ] {
                    for update in [format!("a {op}= b;"), format!("a=a {op} b;")] {
                        assert_eq!(word(&format!("{setup} {update}"), "a"), expected & mask);
                    }
                }
            }
        }
    }
    assert_eq!(
        word(
            "bit[3] b=\"011\"; b=bit[3](angle[3](b)+angle[3](\"001\"));",
            "b"
        ),
        4
    );
    assert_eq!(
        word("bit[3] b=\"011\"; b ^= bit[3](angle[3](b)<<1);", "b"),
        5
    );
}

#[test]
fn all_fixed_angle_rotations_preserve_full_unitaries() {
    for gate in [
        "p",
        "rx",
        "ry",
        "rz",
        "cp",
        "crx",
        "cry",
        "crz",
        "ctrl @ rz",
    ] {
        let qs = if gate.starts_with('c') {
            "q[0],q[1]"
        } else {
            "q[1]"
        };
        for k in 0..8 {
            for (modifier, multiplier) in [("", 1), ("inv @ ", -1), ("pow(3) @ ", 3)] {
                let p = specialize_classical(parse(&format!(
                    "qubit[2] q; angle[3] a=angle[3](\"{k:03b}\"); {modifier}{gate}(a) {qs};"
                )));
                let reference = parse(&format!(
                    "qubit[2] q; {gate}({}*pi/4) {qs};",
                    k * multiplier
                ));
                assert_same(&p, &reference);
            }
        }
    }
    for (body, reference) in [
        (
            "angle[3] a=angle[3](\"111\"); a+=angle[3](\"001\"); crz(a) q[0],q[1];",
            "",
        ),
        (
            "angle[3] a=angle[3](\"111\"); crz(-a) q[0],q[1];",
            "crz(pi/4) q[0],q[1];",
        ),
        (
            "angle[3] a=angle[3](\"101\"); rz(a) q;",
            "rz(5*pi/4) q[0]; rz(5*pi/4) q[1];",
        ),
    ] {
        assert_same(
            &specialize_classical(parse(&format!("qubit[2] q; {body}"))),
            &parse(&format!("qubit[2] q; {reference}")),
        );
    }
}

#[test]
fn angle_bits_remain_measurement_dependent() {
    let p = parse("qubit q; angle[3] a=0; measure q -> a[0]; a<<=1; bit[3] b=bit[3](a);");
    let r = p
        .classical_registers
        .iter()
        .find(|r| r.name == "b")
        .unwrap();
    let cells: Vec<_> = (0..3)
        .map(|index| ClassicalBit {
            register: r.id,
            index,
        })
        .collect();
    let hps = execute(
        &p,
        &ExecutionConfig::all_symbolic(),
        &OutputSelection::new([], cells.clone()),
    )
    .unwrap();
    assert!(!hps.components.is_empty());
    for c in &hps.components {
        assert!(c.output.classical[&cells[0]].is_zero());
        assert!(c.output.classical[&cells[2]].is_zero());
        assert_eq!(
            c.output.classical[&cells[1]],
            BooleanPolynomial::variable(Variable::Input(Qubit {
                register: p.quantum_registers[0].id,
                index: 0
            }))
        );
    }
}

#[test]
fn unused_and_shifted_out_bits_still_require_initialization() {
    for body in [
        "angle[3] a; rz(a) q;",
        "angle[3] a; a<<=3;",
        "angle[3] a; a[0]=true; a>>=1;",
        "angle[3] a; pow(0) @ rz(a) q;",
    ] {
        let p = parse(&format!("qubit q; {body}"));
        let a = &p.classical_registers[0];
        let cells = (0..a.width).map(|index| ClassicalBit {
            register: a.id,
            index,
        });
        assert!(
            matches!(
                execute(
                    &p,
                    &ExecutionConfig::zero(),
                    &OutputSelection::new(
                        [Qubit {
                            register: p.quantum_registers[0].id,
                            index: 0
                        }],
                        cells
                    )
                ),
                Err(SymbolicError::UninitializedClassical(_))
            ),
            "{body}"
        );
    }
}

#[test]
fn unsupported_widths_values_and_operations_are_rejected() {
    for body in [
        "uint n=4; angle[n] a;",
        "angle[0] a;",
        "angle[62] a;",
        "angle[3] a=angle[2](\"00\");",
        "angle[3] a=\"000\";",
        "angle[3] a=0; a<<=-1;",
        "angle[3] a=0; a[3]=true;",
        "angle[3] a=0; a+=1;",
        "angle[3] a=0; a=a*2;",
        "angle[3] a=0; a=a/2;",
        "angle[3] a=1.0/0.0;",
        "angle[3] a=1e309;",
        "angle[3] a=1e308;",
        "input float f; angle[3] a=f;",
        "uint[3] v=0; angle[3] a=angle[3](v);",
        "qubit q; angle[3] a=0; h(a) q;",
    ] {
        assert!(
            openqasm3::parse_str(
                &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
                "invalid-angle.qasm"
            )
            .is_err(),
            "{body}"
        );
    }
}
