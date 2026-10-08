use iqir::annotation::{
    AnnotationPayload, BinaryOp, QubitState, SpecExpr, SpecType, check_expression, parse_expression,
};
use iqir::{StatementKind, SymbolId, frontend};

#[test]
fn reset_postcondition_keeps_the_program_qubit_identity() {
    let source = "OPENQASM 3; qubit q;\n@saria.ensures q == |0>\nreset q;";
    let program = frontend::parse_str(source, "reset-state.qasm").unwrap();
    let reset = &program.body.statements[0];
    let StatementKind::Reset(qubit) = &reset.kind else {
        panic!()
    };
    let annotation = &program.annotations[&reset.ast_id()][0];
    let AnnotationPayload::Expression(SpecExpr::Binary { op, left, right }) = &annotation.payload
    else {
        panic!()
    };
    assert_eq!(*op, BinaryOp::Eq);
    assert_eq!(
        left.as_ref(),
        &SpecExpr::Symbol {
            id: qubit.register,
            name: "q".into()
        }
    );
    assert_eq!(right.as_ref(), &SpecExpr::Ket(vec![QubitState::Zero]));
    assert_eq!(
        &source[annotation.span.start..annotation.span.end],
        "@saria.ensures q == |0>"
    );
}

#[test]
fn state_predicates_admit_conditional_targets_without_proving_purity_or_truth() {
    // q may be entangled here. Import checks the predicate's types, not its truth.
    for predicate in [
        "q == |0>",
        "|0> == q",
        "q != |1>",
        "|1> != q",
        "q == (m == 0 ? |0> : |1>)",
        "q == (flag ? (m == 0 ? |0> : |1>) : |+>)",
        r"q == (\cos(theta)*|0> + \i*\sin(theta)*|1>)",
        "q == 2*|0>", // Normalization is also a proof obligation, not a type check.
    ] {
        let source = format!(
            r#"OPENQASM 3;
include "stdgates.inc";
qubit q;
qubit other;
bit m;
bool flag = false;
float theta = 0.5;
h q;
cx q, other;
@saria.ensures {predicate}
barrier q;
"#
        );
        let program = frontend::parse_str(&source, "state-target.qasm")
            .unwrap_or_else(|e| panic!("{predicate}: {e}"));
        assert_eq!(program.annotations.len(), 1);
    }
    let measured = frontend::parse_str(
        "OPENQASM 3; qubit q; bit m;\n@saria.ensures q == (m == 0 ? |0> : |1>)\nm = measure q;",
        "measured-state.qasm",
    )
    .unwrap();
    let AnnotationPayload::Expression(SpecExpr::Binary { right, .. }) =
        &measured.annotations.values().next().unwrap()[0].payload
    else {
        panic!()
    };
    let SpecExpr::Conditional { condition, .. } = right.as_ref() else {
        panic!()
    };
    let SpecExpr::Binary { left, .. } = condition.as_ref() else {
        panic!()
    };
    assert!(matches!(left.as_ref(), SpecExpr::Symbol { name, .. } if name == "m"));
}

#[test]
fn register_predicates_and_indices_preserve_quantum_types() {
    for (source, expected) in [
        ("q", SpecType::Qubit),
        ("r", SpecType::QubitRegister(2)),
        ("r[0]", SpecType::Qubit),
        ("r[n]", SpecType::Qubit),
        ("r == |00>", SpecType::Bool),
        ("|00> != r", SpecType::Bool),
        ("r[n] == (b ? |0> : |1>)", SpecType::Bool),
        (r"\forall i in 0..2; r[i] == |0>", SpecType::Bool),
    ] {
        let resolve = |name: &str| {
            let (id, ty) = match name {
                "q" => (0, SpecType::Qubit),
                "r" => (1, SpecType::QubitRegister(2)),
                "n" => (2, SpecType::Int),
                "b" => (3, SpecType::Bool),
                _ => return Err(format!("unknown {name}")),
            };
            Ok((
                SpecExpr::Symbol {
                    id: SymbolId(id),
                    name: name.into(),
                },
                ty,
            ))
        };
        let mut expression = parse_expression(source).unwrap();
        assert_eq!(
            check_expression(&mut expression, &[], resolve).unwrap(),
            expected,
            "{source}"
        );
        let resolved = expression.clone();
        assert_eq!(
            check_expression(&mut expression, &[], resolve).unwrap(),
            expected
        );
        assert_eq!(expression, resolved);
    }
    let source = r"OPENQASM 3;
qubit[2] r;
qubit[1] one;
int i = 0;
@saria.requires r == |00> && one == |0> && one[0] == |0>
reset r;
@saria.invariant r[i] == |0> && (\forall j in 0..2; r[j] == |0>)
while (i < 2) { i += 1; }
";
    assert_eq!(
        frontend::parse_str(source, "register-state.qasm")
            .unwrap()
            .annotations
            .len(),
        2
    );
}

#[test]
fn state_predicates_reject_wrong_bindings_dimensions_and_operand_types() {
    for predicate in [
        "missing == |0>",
        "n == |0>",
        "m == |0>",
        "h == |0>",
        "q == |00>",
        "r == |0>",
        "r[0] == |00>",
        "q == (true ? |0> : |00>)",
        "q[0] == |0>",
        "r[true] == |0>",
        "r[0.5] == |0>",
        "r[0][0] == |0>",
        "q == <0|",
        r"q == \X",
        "q == 0",
        "q < |0>",
        "q + |0> == |0>",
        "q",
        r"\forall q in 0..1; q == |0>",
    ] {
        let source = format!(
            "OPENQASM 3; include \"stdgates.inc\"; qubit q; qubit[2] r; int n = 0; bit m;\n@saria.ensures {predicate}\nreset q;"
        );
        assert!(
            frontend::parse_str(&source, "bad-state.qasm").is_err(),
            "accepted {predicate}"
        );
    }
    let capture = "OPENQASM 3; qubit q;\npragma saria.def bad() -> bool = q == |0>\nreset q;";
    assert!(
        frontend::parse_str(capture, "capture.qasm")
            .unwrap_err()
            .to_string()
            .contains("cannot capture")
    );
}

#[test]
fn quantum_binding_recognition_obeys_lexical_shadowing() {
    let source = "OPENQASM 3; qubit q; qubit other;\n\
        if (true) { int q = 0;\n@saria.requires q == 0\nreset other; }\n\
        @saria.ensures q == |0>\nreset q;";
    let program = frontend::parse_str(source, "shadow.qasm").unwrap();
    let mut ids = Vec::new();
    for annotations in program.annotations.values() {
        let AnnotationPayload::Expression(SpecExpr::Binary { left, .. }) = &annotations[0].payload
        else {
            panic!()
        };
        let SpecExpr::Symbol { id, name } = left.as_ref() else {
            panic!()
        };
        assert_eq!(name, "q");
        ids.push(*id);
    }
    assert_eq!(ids.len(), 2);
    assert_ne!(ids[0], ids[1]);
    assert!(ids.contains(&program.quantum_registers[0].id));
    let invalid = source.replace("@saria.requires q == 0", "@saria.requires q == |0>");
    assert!(frontend::parse_str(&invalid, "shadowed-classical.qasm").is_err());
}

#[test]
fn static_loop_specializes_quantum_indices_without_losing_register_identity() {
    let source =
        "OPENQASM 3; qubit[2] r;\nfor int i in [0:1] {\n@saria.ensures r[i] == |0>\nreset r[i]; }";
    let program = frontend::parse_str(source, "loop-state.qasm").unwrap();
    assert_eq!(program.annotations.len(), 2);
    for (i, annotations) in program.annotations.values().enumerate() {
        let AnnotationPayload::Expression(SpecExpr::Binary { left, .. }) = &annotations[0].payload
        else {
            panic!()
        };
        let SpecExpr::Index { value, index } = left.as_ref() else {
            panic!()
        };
        assert_eq!(
            value.as_ref(),
            &SpecExpr::Symbol {
                id: program.quantum_registers[0].id,
                name: "r".into()
            }
        );
        assert_eq!(index.as_ref(), &parse_expression(&i.to_string()).unwrap());
    }
}
