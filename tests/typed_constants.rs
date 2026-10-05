use irene::frontend::openqasm3;
use irene::ir::{ClassicalBit, Program};
use irene::symbolic::{ExecutionConfig, OutputSelection, execute};

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

#[test]
fn constant_bits_and_angles_preserve_types_and_bit_order() {
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
}

#[test]
fn constants_reject_runtime_values_invalid_types_and_mutation() {
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
        "const bit[3] b=\"101\"; const bit c=b[3];",
        "const bool b=true; const bit c=b[0];",
        "const bit[3] b=\"10\";",
        "const angle[3] a=angle[2](\"00\");",
        "qubit q; def f(qubit wire) { p(late) wire; } const float late=1; f(q);",
    ] {
        assert!(
            openqasm3::parse_str(
                &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
                "invalid.qasm",
            )
            .is_err(),
            "{body}",
        );
    }
}

#[test]
fn constant_shadowing_preserves_outer_binding() {
    assert_eq!(
        word(
            "const bit[3] b=\"101\"; bit[3] out=b; if (true) { const bit[3] b=\"010\"; out=b; } out ^= b;",
            "out",
        ),
        7
    );
}

#[test]
fn subroutine_uses_constant_visible_at_definition() {
    // a = pi/2 makes p(a) turn |+> into |+i>; the final inverse S and H
    // therefore restore |0>. The caller's local a = pi must not be captured.
    assert_eq!(
        word(
            "const angle[3] a=pi/2; def f(qubit wire) { p(a) wire; } qubit q; bit out; h q; if (true) { const angle[3] a=pi; f(q); } inv @ s q; h q; out=measure q;",
            "out",
        ),
        0
    );
}
