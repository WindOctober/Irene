mod common;
use irene::{
    equivalence::{EquivalenceConfig, Verdict, analyze},
    frontend::openqasm3,
    ir::{
        unitary::{UnitaryMiterError, miter},
        *,
    },
};

fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
        "miter.qasm",
    )
    .unwrap()
}

fn verdict(a: &Program, b: &Program) -> Verdict {
    let (circuit, identity) = miter(a, b).unwrap();
    let interface = EquivalenceConfig::positional(&circuit, &identity).unwrap();
    analyze(&circuit, &identity, &interface).unwrap().verdict
}

#[test]
fn reverses_order_and_adjoins_gates_with_fresh_ast_ids() {
    let source = parse("qubit[2] a; h a[0]; cx a[0],a[1]; t a[1]; rz(pi/8) a[0];");
    let empty = parse("qubit[2] b;");
    let (inverse, identity) = miter(&empty, &source).unwrap();
    let expected = parse("qubit[2] a; rz(-pi/8) a[0]; tdg a[1]; cx a[0],a[1]; h a[0];");
    common::unitary::assert_same(&inverse, &expected);
    common::unitary::assert_action(&identity, |_| {});
    for program in [&inverse, &identity] {
        // The two generated programs can share an ID allocator; IDs need not start at zero.
        let mut ids = std::collections::BTreeSet::new();
        program.visit_ast_ids(|id| assert!(ids.insert(id)));
    }
    assert_eq!(
        source,
        parse("qubit[2] a; h a[0]; cx a[0],a[1]; t a[1]; rz(pi/8) a[0];")
    );
}

#[test]
fn inverse_of_every_supported_gate_restores_arbitrary_quantum_input() {
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
        "p(pi/4) q[0]",
        "rx(pi/4) q[0]",
        "ry(pi/4) q[0]",
        "rz(pi/4) q[0]",
        "cp(pi/4) q[0],q[1]",
        "crx(pi/4) q[0],q[1]",
        "cry(pi/4) q[0],q[1]",
        "crz(pi/4) q[0],q[1]",
    ] {
        let source = parse(&format!("qubit[3] q; {gate};"));
        assert_eq!(verdict(&source, &source), Verdict::Equivalent, "{gate}");
    }
}

#[test]
fn positional_wires_ignore_register_names_and_local_symbol_ids() {
    let a = parse("qubit[2] a; cx a[0],a[1]; t a[1];");
    let b = parse("bit unused; qubit first; qubit second; cx first,second; t second;");
    assert_eq!(verdict(&a, &b), Verdict::Equivalent);
    assert_eq!(verdict(&b, &a), Verdict::Equivalent);
}

#[test]
fn preserves_coherence_and_ignores_only_global_phase() {
    let identity = parse("qubit q;");
    // Z is invisible on basis states, but not an identity channel.
    assert_eq!(
        verdict(&parse("qubit q; z q;"), &identity),
        Verdict::NotEquivalent
    );
    assert_eq!(
        verdict(&parse("qubit q; t q;"), &parse("qubit q; tdg q;")),
        Verdict::NotEquivalent
    );
    assert_eq!(
        verdict(&parse("qubit q; x q; z q;"), &parse("qubit q; z q; x q;")),
        Verdict::Equivalent
    );
}

#[test]
fn noncommuting_sequences_and_nested_scopes_are_inverted_in_reverse_order() {
    let a = irene::frontend::openqasm2::parse_str(
        "OPENQASM 2.0; include \"qelib1.inc\";
         gate inner a { t a; } gate outer a,b { cx a,b; inner b; }
         qreg q[2]; h q[0]; outer q[0],q[1]; s q[0];",
        "scopes.qasm",
    )
    .unwrap();
    let b = parse("qubit[2] q; h q[0]; cx q[0],q[1]; t q[1]; s q[0];");
    assert_eq!(verdict(&a, &b), Verdict::Equivalent);
}

#[test]
fn rejects_nonunitary_operations_on_either_side_even_if_unobserved() {
    let identity = parse("qubit q;");
    for text in [
        "qubit q; reset q;",
        "qubit q; bit c; c=measure q;",
        "qubit q; bit c; bit d; c=d;",
        "qubit q; bit c=0; if(c) x q;",
    ] {
        let program = parse(text);
        assert!(matches!(
            miter(&program, &identity),
            Err(UnitaryMiterError::NonUnitary)
        ));
        assert!(matches!(
            miter(&identity, &program),
            Err(UnitaryMiterError::NonUnitary)
        ));
    }
    assert!(matches!(
        miter(&identity, &parse("qubit[2] q;")),
        Err(UnitaryMiterError::InterfaceWidth)
    ));
    assert!(matches!(
        miter(
            &identity,
            &parse("input angle[8] theta; qubit q; rz(theta) q;")
        ),
        Err(UnitaryMiterError::NumericInput)
    ));
}

#[test]
fn qasm2_classical_initialization_is_irrelevant_to_full_quantum_interface() {
    let with_storage = irene::frontend::openqasm2::parse_str(
        "OPENQASM 2.0; include \"qelib1.inc\"; qreg q[1]; creg c[1]; h q[0];",
        "creg.qasm",
    )
    .unwrap();
    let without_storage = parse("qubit q; h q;");
    assert_eq!(
        verdict(&with_storage, &without_storage),
        Verdict::Equivalent
    );
    assert_eq!(
        verdict(&without_storage, &with_storage),
        Verdict::Equivalent
    );
}

#[test]
fn toffoli_decomposition_composes_to_identity_in_both_directions() {
    let direct = parse("qubit[3] q; ccx q[0],q[1],q[2];");
    let decomposed = parse(
        "qubit[3] q;
        h q[2]; cx q[1],q[2]; tdg q[2]; cx q[0],q[2]; t q[2];
        cx q[1],q[2]; tdg q[2]; cx q[0],q[2]; t q[1]; t q[2];
        h q[2]; cx q[0],q[1]; t q[0]; tdg q[1]; cx q[0],q[1];",
    );
    assert_eq!(verdict(&direct, &decomposed), Verdict::Equivalent);
    assert_eq!(verdict(&decomposed, &direct), Verdict::Equivalent);
}
