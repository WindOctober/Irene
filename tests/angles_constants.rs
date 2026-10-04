mod common;
use irene::equivalence::{Endpoint, EquivalenceConfig, InputPair, OutputPair, Verdict, analyze};
use irene::frontend::openqasm3;
use irene::ir::{ClassicalBit, NumericExprKind, Program, Qubit, StatementKind};
use irene::symbolic::{ExecutionConfig, OutputSelection, SymbolicError, execute};
use num_rational::BigRational;

fn parse(body: &str) -> Program {
    let p = openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
        "angles.qasm",
    )
    .unwrap();
    let mut ids = vec![];
    p.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort_unstable();
    assert_eq!(
        ids,
        (0..p.ast_id_bound()).collect::<Vec<_>>(),
        "IDs: {body}"
    );
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
    let result = execute(
        &p,
        &ExecutionConfig::zero(),
        &OutputSelection::new([], cells.clone()),
    )
    .unwrap();
    assert_eq!(result.components.len(), 1);
    cells
        .iter()
        .enumerate()
        .map(|(i, c)| {
            let b = &result.components[0].output.classical[c];
            assert!(b.is_zero() || b.is_one());
            u64::from(b.is_one()) << i
        })
        .sum()
}

fn compare(left: &str, right: &str, verdict: Verdict) {
    compare_n(left, right, verdict, 2);
}

fn compare_n(left: &str, right: &str, verdict: Verdict, width: usize) {
    let l = parse(&format!("qubit[{width}] q; {left}"));
    let r = parse(&format!("qubit[{width}] q; {right}"));
    let endpoint = |p: &Program, index| {
        Endpoint::Quantum(Qubit {
            register: p.quantum_registers[0].id,
            index,
        })
    };
    let cfg = EquivalenceConfig {
        input_pairs: (0..width)
            .map(|i| InputPair {
                left: endpoint(&l, i),
                right: endpoint(&r, i),
            })
            .collect(),
        output_pairs: (0..width)
            .map(|i| OutputPair {
                left: endpoint(&l, i),
                right: endpoint(&r, i),
            })
            .collect(),
        ..EquivalenceConfig::default()
    };
    assert_eq!(analyze(&l, &r, &cfg).unwrap().verdict, verdict, "{left}");
}

#[test]
fn fixed_angles_have_exact_bit_order_rounding_and_modular_arithmetic() {
    assert_eq!(
        word(
            "bit[3] b=\"011\"; b=bit[3](angle[3](b)+angle[3](\"001\"));",
            "b"
        ),
        4
    );
    assert_eq!(
        word("bit[3] b=\"011\"; b ^= bit[3](angle[3](b) << 1);", "b"),
        5
    );
    // At sufficiently fine resolution IEEE pi is distinguishable from the
    // mathematical pi. Do not restore the ideal value when folding a float.
    assert_eq!(word("angle[61] a=pi;", "a"), (1_u64 << 60) - 45);
    for (expr, expected) in [
        ("0", 0),
        ("pi/2", 2),
        ("pi", 4),
        ("3*pi/2", 6),
        ("-pi/2", 6),
        ("2*pi", 0),
    ] {
        assert_eq!(
            word(&format!("angle[3] a={expr};"), "a"),
            expected,
            "{expr}"
        );
    }
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
                    word(&format!("{setup} a <<= {shift};"), "a"),
                    (a << shift) & mask
                );
                assert_eq!(word(&format!("{setup} a >>= {shift};"), "a"), a >> shift);
            }
            for b in 0..=mask {
                let setup = format!("{setup} angle[{n}] b=angle[{n}](\"{b:0n$b}\");");
                for (op, expected) in [
                    ("+=", a.wrapping_add(b)),
                    ("-=", a.wrapping_sub(b)),
                    ("^=", a ^ b),
                    ("&=", a & b),
                    ("|=", a | b),
                ] {
                    assert_eq!(
                        word(&format!("{setup} a {op} b;"), "a"),
                        expected & mask,
                        "n={n},a={a},b={b},{op}"
                    );
                }
            }
        }
    }
}

#[test]
fn const_floats_keep_ieee_precision_in_initializers_and_use_sites() {
    for (source, expected) in [
        (
            "const float[32] theta=3*pi/8; p(theta) q;",
            f64::from((3.0 * std::f64::consts::PI / 8.0) as f32),
        ),
        (
            "const float[32] a=16777216; const float[32] b=1; const float[32] c=(a+b)-a; p(c) q;",
            0.0,
        ),
        ("const float[32] a=16777216; p((a+1)-a) q;", 0.0),
        (
            "const float[64] a=16777216; const float[64] c=(a+1)-a; p(c) q;",
            1.0,
        ),
        ("const int n=1; const float[32] a=(n/2)*pi; p(a) q;", 0.0),
        ("const int n=1; p(n/2) q;", 0.0),
    ] {
        let p = parse(&format!("qubit q; {source}"));
        let StatementKind::Apply { parameters, .. } = &p.body.statements[0].kind else {
            panic!("gate expected")
        };
        assert_eq!(
            parameters[0].kind,
            NumericExprKind::Rational(BigRational::from_float(expected).unwrap()),
            "{source}"
        );
    }
    assert_eq!(
        word(
            "const int n=4; const angle[n] a=pi/2; angle[n] out=a;",
            "out"
        ),
        4
    );
    assert_eq!(
        word("const bit[3] b=\"101\" ^ \"011\"; bit[3] out=b;", "out"),
        6
    );
    assert_eq!(
        word("const bool flag=true && !false; bit out=flag;", "out"),
        1
    );
    assert_eq!(
        word(
            "const int n=3; const angle[n] a=pi; bit[n] out=bit[n](a);",
            "out"
        ),
        4
    );
    assert_eq!(
        word("const angle[3] a=pi; const bit b=a[2]; bit out=b;", "out"),
        1
    );
    compare(
        "const angle[3] a=pi/2; def f(qubit wire) { p(a) wire; } if(true) { const angle[3] a=pi; p(a) q[1]; } f(q[1]);",
        "z q[1]; s q[1];",
        Verdict::Equivalent,
    );
}

#[test]
fn runtime_measurement_angles_match_exact_feedback_channels() {
    for gate in ["p", "rx", "ry", "rz", "cp", "crx", "cry", "crz"] {
        let qs = if gate.starts_with('c') {
            "q[0],q[1]"
        } else {
            "q[1]"
        };
        for modifier in ["", "inv @ "] {
            let sign = if modifier.is_empty() { "" } else { "-" };
            compare(
                &format!("angle[3] a=0; measure q[0] -> a[0]; {modifier}{gate}(a) {qs};"),
                &format!("bit c; measure q[0] -> c; if(c) {gate}({sign}pi/4) {qs};"),
                Verdict::Equivalent,
            );
        }
    }
    compare(
        "angle[3] a=0; measure q[0] -> a[0]; a <<= 1; p(a) q[1];",
        "bit c; measure q[0] -> c; if(c) s q[1];",
        Verdict::Equivalent,
    );
    compare(
        "const angle[3] a=pi/2; p(a) q[1];",
        "",
        Verdict::NotEquivalent,
    );
    compare(
        "angle[3] a=0; bit c; measure q[0] -> c; a[0]=c; a[1]=c; a += angle[3](\"001\"); p(a) q[1];",
        "bit c; measure q[0] -> c; if(c) z q[1]; else t q[1];",
        Verdict::Equivalent,
    );
    // Rz is 4pi-periodic as a unitary. Under coherent quantum control a
    // mistaken +/-2pi phase quotient changes the observable channel.
    compare(
        "angle[3] a=angle[3](\"111\"); a += angle[3](\"001\"); crz(a) q[0],q[1];",
        "",
        Verdict::Equivalent,
    );
    compare(
        "angle[3] a=angle[3](\"111\"); crz(-a) q[0],q[1];",
        "crz(pi/4) q[0],q[1];",
        Verdict::Equivalent,
    );
}

#[test]
fn unsupported_or_ill_typed_values_are_not_silently_approximated() {
    for body in [
        "const float[32] f;",
        "const float[16] f=1;",
        "const float f=1.0/0.0;",
        "const float[32] f=1e100;",
        "bit b=true; const bool c=b;",
        "bit b=true; const bool c=false && b;",
        "const bool b=true; b=false;",
        "const float[64] a=1; a=2;",
        "const angle[3] a=0; a[0]=true;",
        "bit b=true; const float f=b;",
        "uint n=4; angle[n] a;",
        "angle[0] a;",
        "angle[62] a;",
        "angle[3] a=angle[2](\"00\");",
        "angle[3] a=\"000\";",
        "angle[3] a=0; a <<= -1;",
        "angle[3] a=0; a[3]=true;",
        "angle[3] a=0; a += 1;",
        "qubit q; def f(qubit wire) { p(late) wire; } const float late=1; f(q);",
    ] {
        assert!(
            openqasm3::parse_str(
                &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
                "invalid.qasm"
            )
            .is_err(),
            "{body}"
        );
    }
    for body in [
        "angle[3] a; p(a) q;",
        "angle[3] a; a <<= 3; p(a) q;",
        "angle[3] a; a[0]=true; a <<= 2; p(a) q;",
    ] {
        let p = parse(&format!("qubit q; {body}"));
        let q = Qubit {
            register: p.quantum_registers[0].id,
            index: 0,
        };
        assert!(
            matches!(
                execute(&p, &ExecutionConfig::zero(), &OutputSelection::new([q], [])),
                Err(SymbolicError::UninitializedClassical(_))
            ),
            "{body}"
        );
    }
}

#[test]
fn ipe_const_and_angle_declarations_no_longer_block_the_frontend() {
    // The frozen left program now lowers, but reads c before initialization.
    let left = openqasm3::parse_str(
        include_str!("../benchmarks/openqasm3-programs/programs/ipe-gate-fusion/left.qasm"),
        "ipe-left.qasm",
    )
    .unwrap();
    fn rational(e: &irene::ir::NumericExpr) -> BigRational {
        match &e.kind {
            NumericExprKind::Rational(v) => v.clone(),
            NumericExprKind::Mul(a, b) => rational(a) * rational(b),
            _ => panic!("IPE powers must retain the rounded theta as an exact rational"),
        }
    }
    fn collect(b: &irene::ir::Block, angles: &mut Vec<BigRational>) {
        for s in &b.statements {
            match &s.kind {
                StatementKind::Apply {
                    gate: irene::ir::Gate::Cp,
                    parameters,
                    ..
                } => angles.push(rational(&parameters[0])),
                StatementKind::Scope(b) => collect(b, angles),
                StatementKind::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    collect(then_branch, angles);
                    collect(else_branch, angles);
                }
                _ => {}
            }
        }
    }
    let mut angles = vec![];
    collect(&left.body, &mut angles);
    let theta =
        BigRational::from_float(f64::from((3.0 * std::f64::consts::PI / 8.0) as f32)).unwrap();
    assert_eq!(
        angles,
        (0..10)
            .map(|i| &theta * BigRational::from_integer((1_u64 << i).into()))
            .collect::<Vec<_>>()
    );
    assert!(matches!(
        execute(
            &left,
            &ExecutionConfig::zero(),
            &OutputSelection::new([], [])
        ),
        Err(SymbolicError::UninitializedClassical(_))
    ));
    // The right program advances beyond pow to a separate U/numeric-angle gap.
    let error = openqasm3::parse_str(
        include_str!("../benchmarks/openqasm3-programs/programs/ipe-gate-fusion/right.qasm"),
        "ipe-right.qasm",
    )
    .unwrap_err();
    assert!(
        matches!(&error, openqasm3::FrontendError::WrongIdentifierKind { name, .. } if name == "c"),
        "{error}"
    );
}

#[test]
fn common_integer_gate_powers_match_explicit_repetition() {
    for (gate, inverse) in [
        ("h q[0];", "h q[0];"),
        ("x q[0];", "x q[0];"),
        ("y q[0];", "y q[0];"),
        ("z q[0];", "z q[0];"),
        ("s q[0];", "sdg q[0];"),
        ("t q[0];", "tdg q[0];"),
        ("sdg q[0];", "s q[0];"),
        ("tdg q[0];", "t q[0];"),
        ("cx q[0],q[1];", "cx q[0],q[1];"),
        ("cz q[0],q[1];", "cz q[0],q[1];"),
        ("swap q[0],q[1];", "swap q[0],q[1];"),
        ("phase(pi/8) q[0];", "phase(-pi/8) q[0];"),
        ("rx(pi/2) q[0];", "rx(-pi/2) q[0];"),
        ("ry(pi/2) q[0];", "ry(-pi/2) q[0];"),
        ("rz(pi/2) q[0];", "rz(-pi/2) q[0];"),
    ] {
        for k in [-2_i32, -1, 0, 2, 3, 8] {
            // Eight explicit Rx/Ry summations exceed the current comparison
            // route's capacity (Unknown). At k=8 these quarter-turn powers
            // are exactly the identity, including global phase: test against
            // that independent closed form instead of weakening the verdict.
            let reference = if k == 8 && gate.starts_with('r') {
                String::new()
            } else {
                (if k < 0 { inverse } else { gate }).repeat(k.unsigned_abs() as usize)
            };
            compare(
                &format!("pow({k}) @ {gate}"),
                &reference,
                Verdict::Equivalent,
            );
        }
    }
}

#[test]
fn nontrivial_cu_modifiers_are_rejected_or_preserve_operator_powers() {
    use common::unitary::{apply, assert_action, u};
    use std::f64::consts::PI;
    for (modifier, power) in [
        ("inv @", -1_i32),
        ("pow(-1) @", -1),
        ("pow(2) @", 2),
        ("pow(-2) @", -2),
        ("pow(3) @", 3),
        ("inv @ pow(2) @", -2),
        ("pow(2) @ inv @", -2),
        ("pow(k) @", 2),
    ] {
        for operands in ["controls[0],targets[0]", "controls,targets"] {
            let source = format!(
                "OPENQASM 3.0; include \"stdgates.inc\"; const int k=2; \
                 qubit[2] controls; qubit[2] targets; {modifier} cu(pi/2,pi/4,pi/8,pi/16) {operands};"
            );
            if let Ok(p) = openqasm3::parse_str(&source, "modified-cu.qasm") {
                let matrix = u(PI / 2.0, PI / 4.0, PI / 8.0, PI / 16.0);
                let matrix = if power < 0 {
                    std::array::from_fn(|i| {
                        std::array::from_fn(|j| (matrix[j][i].0, -matrix[j][i].1))
                    })
                } else {
                    matrix
                };
                assert_action(&p, |state| {
                    let width = if operands == "controls,targets" { 2 } else { 1 };
                    for i in 0..width {
                        for _ in 0..power.unsigned_abs() {
                            apply(state, &[i], i + 2, matrix);
                        }
                    }
                });
            }
        }
    }
}

#[test]
fn cu_identity_powers_and_explicit_inverse_keep_the_complete_operator() {
    let cu = "cu(pi/2,pi/4,pi/8,pi/16) q[0],q[1];";
    for modifier in ["pow(1) @", "inv @ pow(-1) @"] {
        compare(&format!("{modifier} {cu}"), cu, Verdict::Equivalent);
    }
    compare(&format!("pow(0) @ {cu}"), "", Verdict::Equivalent);
    let inverse = "crz(-pi/4) q[0],q[1]; cry(-pi/2) q[0],q[1]; \
                   crz(-pi/8) q[0],q[1]; p(-pi/4) q[0];";
    compare(&format!("{cu} {inverse}"), "", Verdict::Equivalent);
    let wrong_inverse = "p(-pi/4) q[0]; crz(-pi/8) q[0],q[1]; \
                         cry(-pi/2) q[0],q[1]; crz(-pi/4) q[0],q[1];";
    compare(inverse, wrong_inverse, Verdict::NotEquivalent);
    let wrong_square = "p(pi/2) q[0]; crz(pi/4) q[0],q[1]; \
                        cry(pi) q[0],q[1]; crz(pi/2) q[0],q[1];";
    compare(&format!("{cu} {cu}"), wrong_square, Verdict::NotEquivalent);
}

#[test]
fn controlled_powers_preserve_relative_phase_and_modifier_composition() {
    for (gate, reference) in [
        ("phase(pi/8)", "cp(3*pi/8)"),
        ("rx(pi/8)", "crx(3*pi/8)"),
        ("ry(pi/8)", "cry(3*pi/8)"),
        ("rz(pi/8)", "crz(3*pi/8)"),
        ("s", "cp(3*pi/2)"),
        ("t", "cp(3*pi/4)"),
        ("h", "ch"),
    ] {
        compare(
            &format!("ctrl @ pow(3) @ {gate} q[0],q[1];"),
            &format!("{reference} q[0],q[1];"),
            Verdict::Equivalent,
        );
        compare(
            &format!("pow(3) @ ctrl @ {gate} q[0],q[1];"),
            &format!("{reference} q[0],q[1];"),
            Verdict::Equivalent,
        );
    }
    compare("pow(2) @ ctrl @ h q[0],q[1];", "", Verdict::Equivalent);
    compare(
        "pow(2) @ ctrl @ rz(pi) q[0],q[1];",
        "z q[0];",
        Verdict::Equivalent,
    );
    compare(
        "pow(2) @ ctrl @ rz(pi) q[0],q[1];",
        "",
        Verdict::NotEquivalent,
    );
    compare(
        "inv @ pow(-2) @ ctrl @ pow(3) @ phase(pi/8) q[0],q[1];",
        "cp(3*pi/4) q[0],q[1];",
        Verdict::Equivalent,
    );
    compare(
        "h q[0]; bit b=measure q[0]; angle[3] a=0; a[1]=b; pow(-3) @ ctrl @ rz(a) q[0],q[1];",
        "h q[0]; bit b=measure q[0]; angle[3] a=0; a[1]=b; inv @ crz(a) q[0],q[1]; inv @ crz(a) q[0],q[1]; inv @ crz(a) q[0],q[1];",
        Verdict::Equivalent,
    );
}

#[test]
fn pow_constant_propagation_respects_flow_widths_and_scope() {
    compare(
        "uint[3] k=1; for uint i in [0:3] { pow(k) @ phase(pi/8) q[0]; k <<= 1; }",
        "phase(7*pi/8) q[0];",
        Verdict::Equivalent,
    );
    compare(
        "h q[0]; bit b=measure q[0]; uint[3] k=1; if(b) { k=2; } else { k=2; } pow(k) @ x q[1];",
        "h q[0]; bit b=measure q[0];",
        Verdict::Equivalent,
    );
    compare(
        "uint[3] k=1; if(true) { uint[3] k=2; pow(k) @ x q[0]; } pow(k) @ x q[1];",
        "x q[1];",
        Verdict::Equivalent,
    );
    compare(
        "uint[3] k=1; if(true) { k=2; } pow(k) @ x q[0];",
        "",
        Verdict::Equivalent,
    );
    compare(
        "uint[3] k=1; pow(k<<1) @ x q[0]; pow(k) @ x q[1];",
        "x q[1];",
        Verdict::Equivalent,
    );
    compare(
        "h q[0]; bit b=measure q[0]; uint[3] k=1; if(b) { k=2; } else { pow(k) @ x q[1]; }",
        "h q[0]; bit b=measure q[0]; if(!b) x q[1];",
        Verdict::Equivalent,
    );
    for body in [
        "uint[3] k; pow(k) @ x q;",
        "bit b=measure q; uint[3] k=1; if(b) { k=2; } pow(k) @ x q;",
        "uint[3] k=1; measure q -> k[0]; pow(k) @ x q;",
        "uint[3] k=1; bit b=measure q; if(b) { k=2; } else { pow(k-1) @ x q; }", // unsupported runtime arithmetic, not a guessed value
        "pow(0.5) @ x q;",
        "pow(2.0) @ x q;",
        "pow(0) @ bogus q;",
        "pow(0) @ x q,q;",
        "uint[3] k=2; bit[k] b; pow(k) @ x q;",
    ] {
        assert!(
            openqasm3::parse_str(
                &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit q; {body}"),
                "pow-invalid.qasm"
            )
            .is_err(),
            "{body}"
        );
    }
}

#[test]
fn multi_qubit_involution_powers_and_controls_are_exact() {
    for gate in ["ccx", "ccz", "cswap", "ctrl @ swap"] {
        for k in [0, 1, 2, 3, 1000001] {
            let source = format!("pow({k}) @ {gate} q[0],q[1],q[2];");
            let reference = if k % 2 == 0 {
                String::new()
            } else {
                format!("{gate} q[0],q[1],q[2];")
            };
            compare_n(&source, &reference, Verdict::Equivalent, 3);
        }
    }
    compare_n(
        "reset q[0]; x q[0]; ctrl @ pow(3) @ swap q[0],q[1],q[2];",
        "reset q[0]; x q[0]; swap q[1],q[2];",
        Verdict::Equivalent,
        3,
    );
    compare(
        "reset q[0]; x q[0]; ctrl @ pow(3) @ h q[0],q[1];",
        "reset q[0]; x q[0]; h q[1];",
        Verdict::Equivalent,
    );
    compare(
        "reset q[0]; ctrl @ pow(3) @ h q[0],q[1];",
        "reset q[0];",
        Verdict::Equivalent,
    );
}

#[test]
fn zero_power_does_not_hide_parameter_errors_or_angle_reads() {
    for body in [
        "angle[3] a; pow(0) @ rz(a) q;",
        "input float a; pow(0) @ rz(1/a) q;",
    ] {
        let p = parse(&format!("qubit q; {body}"));
        assert!(execute(&p, &ExecutionConfig::zero(), &OutputSelection::new([], [])).is_err());
    }
    for parameter in 0..4 {
        let mut args = ["pi/2", "pi/4", "pi/8", "pi/16"];
        args[parameter] = "1/a";
        let p = parse(&format!(
            "input float a; qubit[2] q; pow(0) @ cu({}) q[0],q[1];",
            args.join(",")
        ));
        assert!(execute(&p, &ExecutionConfig::zero(), &OutputSelection::new([], [])).is_err());
    }
}

#[test]
fn constant_width_uint_storage_and_updates_are_exact() {
    assert_eq!(
        word(
            "const int n=10; uint[n] power=1; for uint i in [0:n-1] { power <<= 1; }",
            "power"
        ),
        0
    );
    assert_eq!(
        word("const uint n=3; uint[n+1] a=3; a=a<<1; a >>= 1;", "a"),
        3
    );
    assert_eq!(word("uint a=4294967295;", "a"), u64::from(u32::MAX));
    assert_eq!(
        word(
            "const int n=64; uint[n] a=18446744073709551615; a>>=63;",
            "a"
        ),
        1
    );
    assert_eq!(
        word(
            "const int n=4; uint[n] a=9; uint[n] b=6; a ^= b; a &= b; a |= b; a=~a;",
            "a"
        ),
        9
    );
    assert_eq!(
        word(
            "const int n=4; uint[n] a=3; a[3]=true; bit[n] b=bit[n](a); uint[n] c=uint[n](b);",
            "c"
        ),
        11
    );
    assert_eq!(
        word("const int n=4; uint[n] a=3; bool b=(a<4)&&(a!=2);", "b"),
        1
    );
    // Assignment from an immutable expression may be narrowed if representable.
    assert_eq!(
        word("const int n=4; const uint[8] v=3; uint[n] a=v+1;", "a"),
        4
    );
}

#[test]
fn uint_shifts_match_all_small_words_and_preserve_ast_ids() {
    for width in 1..=4 {
        let mask = (1_u64 << width) - 1;
        for value in 0..=mask {
            for shift in 0..=width + 1 {
                assert_eq!(
                    word(
                        &format!("const int n={width}; uint[n] a={value}; a <<= {shift};",),
                        "a"
                    ),
                    (value << shift) & mask
                );
                assert_eq!(
                    word(
                        &format!("const int n={width}; uint[n] a={value}; a >>= {shift};",),
                        "a"
                    ),
                    value >> shift
                );
            }
        }
    }
}

#[test]
fn uint_can_carry_measurement_dependent_values_without_constant_folding_them() {
    compare(
        "h q[0]; bit b=measure q[0]; const int n=3; uint[n] a=0; if(b) { a=1; } a <<= 2; if(a==4) x q[1];",
        "h q[0]; bit b=measure q[0]; if(b) x q[1];",
        Verdict::Equivalent,
    );
    compare(
        "h q[0]; bit b=measure q[0]; const int n=3; uint[n] a=0; if(b) { a=1; } a <<= 2; if(a==2) x q[1];",
        "h q[0]; bit b=measure q[0]; if(b) x q[1];",
        Verdict::NotEquivalent,
    );
}

#[test]
fn uint_rejects_dynamic_widths_and_unsupported_or_lossy_operations() {
    for body in [
        "uint n=4; uint[n] a=1;",
        "input uint n; uint[n] a=1;",
        "const int n=0; uint[n] a;",
        "const int n=-1; uint[n] a;",
        "const int n=65; uint[n] a;",
        "for uint n in [1:2] { uint[n] a=1; }",
        "const int n=4; { const int n=0; uint[n] a; }",
        "const int n=4; uint[n] a=16;",
        "const int n=4; uint[n] a=-1;",
        "uint[4] a=1; uint[3] b=a;",
        "uint[4] a=1; a <<= -1;",
        "uint[4] a=1; uint[4] s=1; a <<= s;",
        "uint[4] a=1; a += 1;",
        "uint[4] a=1; a=a*2;",
        "uint[4] a=1; angle[4] b=a;",
        "uint[4] a=1; bit[4] b=a;",
        "const int n=4; n=3; uint[n] a;",
        "uint a=1; a <<= 1;", // Target-default types retain bit-operation restrictions.
    ] {
        assert!(
            openqasm3::parse_str(&format!("OPENQASM 3.0; {body}"), "invalid-uint.qasm").is_err(),
            "{body}"
        );
    }
}

#[test]
fn uint_shift_does_not_hide_uninitialized_reads() {
    for body in ["uint[4] a; a <<= 4;", "uint[4] a; a[0]=true; a >>= 1;"] {
        let p = parse(body);
        let a = &p.classical_registers[0];
        let output = OutputSelection::new(
            [],
            (0..a.width).map(|index| ClassicalBit {
                register: a.id,
                index,
            }),
        );
        assert!(
            matches!(
                execute(&p, &ExecutionConfig::zero(), &output),
                Err(SymbolicError::UninitializedClassical(_))
            ),
            "{body}"
        );
    }
}
