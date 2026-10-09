use iqir::*;
use std::collections::{BTreeMap, BTreeSet};

fn parse(body: &str) -> Program {
    let p = frontend::parse_str(
        &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
        "while.qasm",
    )
    .unwrap();
    let mut ids = Vec::new();
    p.visit_ast_ids(|id| ids.push(id.index()));
    let unique: BTreeSet<_> = ids.iter().copied().collect();
    assert_eq!(ids.len(), unique.len(), "shared AST identity");
    assert_eq!(
        unique.into_iter().collect::<Vec<_>>(),
        (0..p.ast_id_bound()).collect::<Vec<_>>()
    );
    p
}

#[test]
fn preserves_nested_and_single_statement_loops() {
    let p = parse(
        "qubit q; bit flag; while(flag) { bit local; while(local) reset q; flag=measure q; } while(false) reset q;",
    );
    let StatementKind::While { condition, body } = &p.body.statements[0].kind else {
        panic!()
    };
    assert!(matches!(condition.kind, ClassicalExprKind::Bit(_)));
    assert_eq!(body.classical_registers.len(), 1);
    assert!(
        body.statements
            .iter()
            .any(|s| matches!(s.kind, StatementKind::While { .. }))
    );
    assert!(
        body.statements
            .iter()
            .any(|s| matches!(s.kind, StatementKind::Measure { .. }))
    );
    let StatementKind::While { body, .. } = &p.body.statements[1].kind else {
        panic!()
    };
    assert!(matches!(body.statements[0].kind, StatementKind::Reset(_)));
}

#[test]
fn locals_do_not_escape_or_capture_the_guard() {
    let p = parse("bit flag; while(flag) {bit flag; flag=false;}");
    let StatementKind::While { condition, body } = &p.body.statements[0].kind else {
        panic!()
    };
    let ClassicalExprKind::Bit(guard) = &condition.kind else {
        panic!()
    };
    assert_eq!(guard.register, p.classical_registers[0].id);
    assert_ne!(guard.register, body.classical_registers[0].id);
    for body in [
        "while(false) {bit x;} if(x) {}",
        "while(false) {bit x; bit x;}",
    ] {
        assert!(frontend::parse_str(&format!("OPENQASM 3; {body}"), "scope.qasm").is_err());
    }
}

#[test]
fn loop_entry_and_exit_facts_do_not_specialize_gate_powers() {
    for body in [
        "bit[1] b=\"1\"; qubit q; while(b[0]) {pow(uint[1](b)) @ x q; b[0]=measure q;}",
        "bit[1] b=\"1\"; qubit q; while(b[0]) {b[0]=measure q;} pow(uint[1](b)) @ x q;",
    ] {
        let error = frontend::parse_str(
            &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
            "power.qasm",
        )
        .unwrap_err();
        assert!(error.to_string().contains("power"), "{error}");
    }
    parse("bit[1] b; qubit q; while(true) {b=\"1\"; pow(uint[1](b)) @ x q; b[0]=measure q;}");
}

fn evaluate(e: &ClassicalExpr, bits: &BTreeMap<ClassicalBit, bool>) -> bool {
    use ClassicalExprKind as E;
    // This suite also runs against the subsequent typed-scalar IR additions.
    #[allow(unreachable_patterns)]
    match &e.kind {
        E::Bool(v) => *v,
        E::Bit(b) => bits[b],
        E::Not(a) => !evaluate(a, bits),
        E::Eq(a, b) => evaluate(a, bits) == evaluate(b, bits),
        E::And(a, b) => evaluate(a, bits) && evaluate(b, bits),
        E::Or(a, b) => evaluate(a, bits) || evaluate(b, bits),
        E::Xor(a, b) => evaluate(a, bits) ^ evaluate(b, bits),
        _ => panic!("expected only Boolean expressions"),
    }
}

#[test]
fn register_comparisons_use_all_bits_in_both_operand_orders() {
    for op in ["==", "!=", "<", "<=", ">", ">="] {
        for reverse in [false, true] {
            let guard = if reverse {
                format!("5 {op} c")
            } else {
                format!("c {op} 5")
            };
            for control in ["while", "if"] {
                let p = parse(&format!("bit[3] c; {control}({guard}) {{}}"));
                let condition = match &p.body.statements[0].kind {
                    StatementKind::While { condition, .. }
                    | StatementKind::If { condition, .. } => condition,
                    _ => panic!(),
                };
                for value in 0..8 {
                    let bits = (0..3)
                        .map(|index| {
                            (
                                ClassicalBit {
                                    register: p.classical_registers[0].id,
                                    index,
                                },
                                value & (1 << index) != 0,
                            )
                        })
                        .collect();
                    let (a, b) = if reverse { (5, value) } else { (value, 5) };
                    let expected = match op {
                        "==" => a == b,
                        "!=" => a != b,
                        "<" => a < b,
                        "<=" => a <= b,
                        ">" => a > b,
                        ">=" => a >= b,
                        _ => unreachable!(),
                    };
                    assert_eq!(
                        evaluate(condition, &bits),
                        expected,
                        "{control}({guard}), c={value}"
                    );
                }
            }
        }
    }
}

#[test]
fn invalid_literals_and_unsupported_loop_control_are_rejected() {
    for body in [
        "bit[3] c; while(c==8) {}",
        "bit[3] c; while(c == -1) {}",
        "while(true) {break;}",
        "while(true) {continue;}",
    ] {
        assert!(
            frontend::parse_str(&format!("OPENQASM 3; {body}"), "invalid.qasm").is_err(),
            "{body}"
        );
    }
    let nested = |n| format!("{}{}", "while(false) {".repeat(n), "}".repeat(n));
    parse(&nested(64));
    assert!(frontend::parse_str(&format!("OPENQASM 3; {}", nested(65)), "depth.qasm").is_err());
}
