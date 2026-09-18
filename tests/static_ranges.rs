mod common;

use common::unitary::{assert_fresh_ids, assert_same};
use irene::frontend::openqasm3::parse_str;
use irene::ir::{Block, Program, StatementKind};
use std::collections::BTreeSet;

fn parse(body: &str) -> Program {
    parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
        "static-ranges.qasm",
    )
    .unwrap()
}

#[test]
fn loops_preserve_order_signed_steps_and_nondivisible_endpoints() {
    for (source, reference) in [
        (
            "qubit[3] q; for int i in [0:1] cx q[i],q[i+1];",
            "qubit[3] q; cx q[0],q[1]; cx q[1],q[2];",
        ),
        (
            "qubit[3] q; for int i in [1:-1:0] cx q[i],q[i+1];",
            "qubit[3] q; cx q[1],q[2]; cx q[0],q[1];",
        ),
        (
            "qubit[4] q; for int i in [-2:0] x q[i+2]; for uint i in [0:2:3] h q[i];",
            "qubit[4] q; x q[0]; x q[1]; x q[2]; h q[0]; h q[2];",
        ),
        (
            "qubit[4] q; for int i in [3:-2:0] h q[i]; for int j in [1:1] z q[j];",
            "qubit[4] q; h q[3]; h q[1]; z q[1];",
        ),
        (
            "qubit q; for int i in [0:1] { h q; rz(i*pi/4) q; }",
            "qubit q; h q; rz(0) q; h q; rz(pi/4) q;",
        ),
    ] {
        let p = parse(source);
        assert_same(&p, &parse(reference));
        assert_fresh_ids(&p);
    }
}

#[test]
fn slices_preserve_broadcast_pairing_and_scalar_reuse() {
    for (source, reference) in [
        (
            "qubit[5] q; h q[0:2:4];",
            "qubit[5] q; h q[0]; h q[2]; h q[4];",
        ),
        (
            "qubit[4] q; cx q[0:1],q[3:-1:2];",
            "qubit[4] q; cx q[0],q[3]; cx q[1],q[2];",
        ),
        (
            "qubit[4] q; cx q[0],q[3:-1:1];",
            "qubit[4] q; cx q[0],q[3]; cx q[0],q[2]; cx q[0],q[1];",
        ),
        (
            "qubit[4] q; def f(qubit[2] a) { h a[0]; cx a[0],a[1]; } f(q[3:-2:0]);",
            "qubit[4] q; h q[3]; cx q[3],q[1];",
        ),
    ] {
        let p = parse(source);
        assert_same(&p, &parse(reference));
        assert_fresh_ids(&p);
    }
}

#[test]
fn nested_loops_restore_shadowed_bindings_and_subroutines_use_lexical_scope() {
    let p = parse(
        "const int i=2; qubit[3] q;
         def f(qubit[3] a) { x a[i]; }
         for int i in [0:1] {
             h q[i]; for int i in [1:1] z q[i]; x q[i]; f(q);
         }
         h q[i];",
    );
    assert_same(
        &p,
        &parse(
            "qubit[3] q; h q[0]; z q[1]; x q[0]; x q[2]; h q[1]; z q[1]; x q[1]; x q[2]; h q[2];",
        ),
    );
    assert_fresh_ids(&p);
}

#[test]
fn iteration_local_registers_do_not_alias() {
    let p = parse("qubit[3] q; for int i in [0:2] { bit c; c=measure q[i]; }");
    fn collect(
        block: &Block,
        declarations: &mut Vec<irene::ir::SymbolId>,
        targets: &mut Vec<irene::ir::SymbolId>,
    ) {
        declarations.extend(block.classical_registers.iter().map(|r| r.id));
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::Scope(b) => collect(b, declarations, targets),
                StatementKind::Measure { target, .. } => targets.push(target.register),
                _ => {}
            }
        }
    }
    let (mut declarations, mut targets) = (Vec::new(), Vec::new());
    collect(&p.body, &mut declarations, &mut targets);
    assert_eq!(declarations.len(), 3);
    assert_eq!(declarations.iter().collect::<BTreeSet<_>>().len(), 3);
    assert_eq!(targets, declarations);
    assert_fresh_ids(&p);
}

#[test]
fn invalid_dynamic_or_unsupported_ranges_are_rejected_completely() {
    for source in [
        "qubit q; for int i in [0:0:1] x q;",
        "qubit q; for int i in [2:1] x q;",
        "qubit q; for int i in [0:-1:2] x q;",
        "qubit q; for uint[2] i in [0:4] x q;",
        "qubit q; for uint i in [-1:0] x q;",
        "qubit q; for float i in [0:1] x q;",
        "qubit q; input int n; for int i in [0:n] x q;",
        "qubit q; for int i in [0:1] { i=1; x q; }",
        "qubit q; for int i in [0:1] { break; }",
        "qubit q; for int i in [0:1] { continue; }",
        "qubit q; for int i in [0:1] { const int n=i; }",
        "qubit q; for int i in [1:2] { bit[i] c; }",
        "qubit q; for int i in [0:1] { const int i=1; }",
        "qubit[2] q; for int i in [0:1] x q[i]; x q[i];",
        "qubit[2] q; def f(qubit[2] a) { x a[i]; } for int i in [0:1] f(q);",
        "qubit[2] q; x q[:1];",
        "qubit[2] q; x q[0:];",
        "qubit[2] q; x q[0:1:];",
        "qubit[2] q; x q[0:2];",
        "qubit[2] q; x q[1:-1:-1];",
        "qubit[4] q; cx q[0:1],q[1:3];",
        "qubit[4] q; cx q[0:1],q[0:1];",
        "qubit[4] q; cx q[0],q[0:2];",
    ] {
        assert!(
            parse_str(
                &format!("OPENQASM 3.0; include \"stdgates.inc\"; {source}"),
                "rejected-range.qasm"
            )
            .is_err(),
            "{source}"
        );
    }
}

#[test]
fn expansion_limits_are_shared_across_loops() {
    for source in [
        "qubit q; for int i in [0:4096] x q;",
        "qubit q; for int i in [0:64] { for int j in [0:64] x q; }",
        "qubit q; for int i in [0:64] x q; for int j in [0:4090] x q;",
        "qubit q; for uint[64] i in [0:18446744073709551615] x q;",
        "qubit[2] q; x q[0:18446744073709551615];",
    ] {
        assert!(
            parse_str(
                &format!("OPENQASM 3.0; include \"stdgates.inc\"; {source}"),
                "oversized-range.qasm"
            )
            .is_err(),
            "{source}"
        );
    }
}
