//! Tests the IR transformation independently of any equivalence backend.
mod common;

use irene::{
    frontend::{openqasm2, openqasm3},
    ir::{
        Program, StatementKind,
        unitary::{UnitaryMiterError, miter, validate},
    },
};

fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
        "miter.qasm",
    )
    .unwrap()
}

fn assert_identity_pair(left: &Program, right: &Program) {
    for (a, b) in [(left, right), (right, left)] {
        validate(a).unwrap();
        validate(b).unwrap();
        let (circuit, identity) = miter(a, b).unwrap();
        // Compare all matrix entries without quotienting out global phase.
        common::unitary::assert_action(&circuit, |_| {});
        common::unitary::assert_action(&identity, |_| {});
    }
}

#[test]
fn every_supported_gate_has_an_exact_ir_adjoint() {
    for gate in [
        "h q[0]",
        "x q[0]",
        "y q[0]",
        "z q[0]",
        "s q[0]",
        "sdg q[0]",
        "t q[0]",
        "tdg q[0]",
        "cx q[0],q[1]",
        "cy q[0],q[1]",
        "cz q[0],q[1]",
        "swap q[0],q[1]",
        "ccx q[0],q[1],q[2]",
        "ccz q[0],q[1],q[2]",
    ] {
        let p = parse(&format!("qubit[3] q; {gate};"));
        assert_identity_pair(&p, &p);
    }
    for angle in ["0", "pi/7", "-pi/3", "2*pi", "3*pi", "0.17"] {
        for (gate, args) in [
            ("p", "q[0]"),
            ("rx", "q[0]"),
            ("ry", "q[0]"),
            ("rz", "q[0]"),
            ("cp", "q[0],q[1]"),
            ("crx", "q[0],q[1]"),
            ("cry", "q[0],q[1]"),
            ("crz", "q[0],q[1]"),
        ] {
            let p = parse(&format!("qubit[2] q; {gate}({angle}) {args};"));
            assert_identity_pair(&p, &p);
        }
    }
}

#[test]
fn distinct_programs_compose_in_the_correct_order_without_mutation() {
    let left = parse("qubit[2] a; h a[0]; cx a[0],a[1]; t a[1];");
    let right = parse("qubit[2] b; ry(pi/3) b[1]; crz(pi/5) b[1],b[0]; s b[0];");
    let original = (left.clone(), right.clone());
    let (circuit, identity) = miter(&left, &right).unwrap();
    let expected = parse(
        "qubit[2] q; h q[0]; cx q[0],q[1]; t q[1];
        sdg q[0]; crz(-pi/5) q[1],q[0]; ry(-pi/3) q[1];",
    );
    common::unitary::assert_same(&circuit, &expected);
    common::unitary::assert_action(&identity, |_| {});
    assert_eq!((left, right), original);
    for p in [&circuit, &identity] {
        let mut ids = std::collections::BTreeSet::new();
        p.visit_ast_ids(|id| assert!(ids.insert(id)));
    }
}

#[test]
fn nested_scopes_and_positional_interfaces_are_preserved() {
    let left = openqasm2::parse_str(
        "OPENQASM 2.0; include \"qelib1.inc\";
         gate inner a { t a; } gate outer a,b { cx a,b; inner b; }
         qreg a[2]; creg c[1]; h a[0]; outer a[0],a[1]; s a[0];",
        "nested.qasm",
    )
    .unwrap();
    let right = parse(
        "bit unused=0; qubit first; qubit second;
        h first; cx first,second; t second; s first;",
    );
    assert_identity_pair(&left, &right);
}

#[test]
fn toffoli_and_its_decomposition_compose_to_identity() {
    let direct = parse("qubit[3] q; ccx q[0],q[1],q[2];");
    let decomposed = parse(
        "qubit[3] q;
        h q[2]; cx q[1],q[2]; tdg q[2]; cx q[0],q[2]; t q[2];
        cx q[1],q[2]; tdg q[2]; cx q[0],q[2]; t q[1]; t q[2];
        h q[2]; cx q[0],q[1]; t q[0]; tdg q[1]; cx q[0],q[1];",
    );
    assert_identity_pair(&direct, &decomposed);
}

#[test]
fn nonunitary_programs_are_rejected_on_both_sides() {
    let identity = parse("qubit q;");
    for body in [
        "qubit q; reset q;",
        "qubit q; bit c; c=measure q;",
        "qubit q; bit c; bit d; c=d;",
        "qubit q; bit c=0; if(c) x q;",
    ] {
        let p = parse(body);
        assert!(matches!(validate(&p), Err(UnitaryMiterError::NonUnitary)));
        for (a, b) in [(&p, &identity), (&identity, &p)] {
            assert!(matches!(miter(a, b), Err(UnitaryMiterError::NonUnitary)));
        }
    }
    let p = parse("input angle theta; qubit q; rz(theta) q;");
    assert!(matches!(validate(&p), Err(UnitaryMiterError::NumericInput)));
    for (a, b) in [(&p, &identity), (&identity, &p)] {
        assert!(matches!(miter(a, b), Err(UnitaryMiterError::NumericInput)));
    }
    assert!(matches!(
        miter(&identity, &parse("qubit[2] q;")),
        Err(UnitaryMiterError::InterfaceWidth)
    ));
}

#[test]
fn malformed_gate_shapes_and_wire_references_are_rejected() {
    let valid = parse("qubit[2] q; crz(pi/4) q[0],q[1];");
    for mutation in 0..5 {
        let mut p = valid.clone();
        let StatementKind::Apply {
            parameters, qubits, ..
        } = &mut p.body.statements[0].kind
        else {
            panic!()
        };
        match mutation {
            0 => parameters.clear(),
            1 => qubits.clear(),
            2 => qubits[1] = qubits[0].clone(),
            3 => qubits[1].index = 99,
            4 => qubits[1].register.0 = 99,
            _ => unreachable!(),
        }
        assert!(matches!(
            validate(&p),
            Err(UnitaryMiterError::InvalidOperands)
        ));
        for (a, b) in [(&p, &valid), (&valid, &p)] {
            assert!(matches!(
                miter(a, b),
                Err(UnitaryMiterError::InvalidOperands)
            ));
        }
    }
    let mut duplicate = valid.clone();
    duplicate
        .quantum_registers
        .push(valid.quantum_registers[0].clone());
    assert!(matches!(
        validate(&duplicate),
        Err(UnitaryMiterError::InvalidOperands)
    ));
}

#[test]
fn relative_and_global_phases_are_not_removed_by_construction() {
    let empty = parse("qubit q;");
    let z = parse("qubit q; z q;");
    let (circuit, _) = miter(&z, &empty).unwrap();
    common::unitary::assert_same(&circuit, &z);
    let xz = parse("qubit q; x q; z q;");
    let zx = parse("qubit q; z q; x q;");
    let (minus_identity, _) = miter(&xz, &zx).unwrap();
    common::unitary::assert_action(&minus_identity, |state| {
        for z in state {
            *z = (-z.0, -z.1);
        }
    });
}
