use iqir::annotation::{
    AnnotationPayload, BinaryOp, MathFunction, SpecExpr, UnaryOp, parse_expression,
};
use iqir::{Block, StatementKind, frontend};

fn number(n: i64) -> SpecExpr {
    SpecExpr::Number(num_rational::BigRational::from_integer(n.into()))
}

fn unary(op: UnaryOp, operand: SpecExpr) -> SpecExpr {
    SpecExpr::Unary {
        op,
        operand: Box::new(operand),
    }
}

#[test]
fn boolean_constant_is_not_left_as_a_dangling_symbol() {
    let p = frontend::parse_str(
        "OPENQASM 3; qubit q; const bool ready = true;\n@saria.requires ready\nreset q;",
        "bool.qasm",
    )
    .unwrap();
    assert_eq!(
        p.annotations.values().next().unwrap()[0].payload,
        AnnotationPayload::Expression(SpecExpr::Bool(true))
    );
}

#[test]
fn binds_multiple_annotations_to_while_and_keeps_source_offsets() {
    let source = "OPENQASM 3;\nuint[8] n = 0;\nbool stop = false;\n\
        @saria.requires n == 0 && !stop\n\
        @saria.invariant n! >= 1\n\
        @saria.terminates almost_sure\n\
        @saria.ensures stop\n\
        while (!stop) { stop = true; }";
    let p = frontend::parse_str(source, "spec.qasm").unwrap();
    let s = p.body.statements.last().unwrap();
    assert!(matches!(s.kind, StatementKind::While { .. }));
    let a = &p.annotations[&s.ast_id()];
    assert_eq!(a.len(), 4);
    assert_eq!(a[0].span.source, "spec.qasm");
    assert_eq!(
        &source[a[0].span.start..a[0].span.end],
        "@saria.requires n == 0 && !stop"
    );
    let AnnotationPayload::Expression(SpecExpr::Binary { left, .. }) = &a[1].payload else {
        panic!()
    };
    let SpecExpr::Unary {
        op: UnaryOp::Factorial,
        operand,
    } = left.as_ref()
    else {
        panic!()
    };
    let SpecExpr::Symbol { id, name } = operand.as_ref() else {
        panic!("mutable n was folded")
    };
    assert_eq!(name, "n");
    assert_eq!(
        *id,
        p.classical_registers
            .iter()
            .find(|r| r.name == "n")
            .unwrap()
            .id
    );
    let mut ids = Vec::new();
    p.visit_ast_ids(|id| ids.push(id));
    assert!(p.annotations.keys().all(|id| ids.contains(id)));
}

#[test]
fn broadcast_annotation_is_on_the_whole_sequence() {
    let p = frontend::parse_str(
        "OPENQASM 3; include \"stdgates.inc\"; qubit[2] q;\n\
        @saria.ensures cosh(0) == 1\nh q;",
        "broadcast.qasm",
    )
    .unwrap();
    let s = &p.body.statements[0];
    let StatementKind::Scope(b) = &s.kind else {
        panic!()
    };
    assert_eq!(b.statements.len(), 2);
    assert_eq!(p.annotations.len(), 1);
    assert!(p.annotations.contains_key(&s.ast_id()));
}

fn annotated_symbols(b: &Block, p: &iqir::Program, out: &mut Vec<iqir::SymbolId>) {
    for s in &b.statements {
        if let Some(a) = p.annotations.get(&s.ast_id()) {
            let AnnotationPayload::Expression(SpecExpr::Binary { left, .. }) = &a[0].payload else {
                panic!()
            };
            let SpecExpr::Symbol { id, .. } = left.as_ref() else {
                panic!()
            };
            out.push(*id);
        }
        match &s.kind {
            StatementKind::Scope(b) | StatementKind::While { body: b, .. } => {
                annotated_symbols(b, p, out)
            }
            StatementKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                annotated_symbols(then_branch, p, out);
                annotated_symbols(else_branch, p, out);
            }
            _ => {}
        }
    }
}

#[test]
fn nested_scopes_bind_shadowed_names_separately() {
    let p = frontend::parse_str(
        "OPENQASM 3; uint[8] n = 0; bool stop = false;\n\
        @saria.invariant n <= 5\nwhile (!stop) {\n\
        uint[8] n = 2;\n@saria.ensures n == 3\nn += 1; stop = true; }",
        "scope.qasm",
    )
    .unwrap();
    let mut ids = Vec::new();
    annotated_symbols(&p.body, &p, &mut ids);
    assert_eq!(ids.len(), 2);
    assert_ne!(ids[0], ids[1]);
}

#[test]
fn static_expansion_specializes_annotation_index_and_keeps_each_instance() {
    let p = frontend::parse_str(
        "OPENQASM 3; include \"stdgates.inc\"; qubit q;\n\
        for int i in [0:2] {\n@saria.requires i! >= 1\nh q; }",
        "for.qasm",
    )
    .unwrap();
    assert_eq!(p.annotations.len(), 3);
    let mut indices = Vec::new();
    for annotations in p.annotations.values() {
        let AnnotationPayload::Expression(SpecExpr::Binary { left, .. }) = &annotations[0].payload
        else {
            panic!()
        };
        let SpecExpr::Unary { operand, .. } = left.as_ref() else {
            panic!()
        };
        indices.push(operand.as_ref().clone());
    }
    assert_eq!(indices, vec![number(0), number(1), number(2)]);
}

#[test]
fn fails_closed_on_dangling_unknown_misplaced_and_unbound_annotations() {
    for tail in [
        "@saria.ensures true",
        "while (false) {\n@saria.ensures true\n}",
        "@saria.typo true\nreset q;",
        "@saria.invariant true\nreset q;",
        "@saria.terminates almost_sure\nreset q;",
        "@saria.ensures missing! > 0\nreset q;",
        "@saria.ensures mystery(1) > 0\nreset q;",
        "@saria.ensures true\nuint[8] n = 0;",
        "@saria.invariant true\nfor int i in [0:1] { reset q; }",
        "gate unused a {\n@saria.ensures true\nx a; }",
        "def unused(qubit a) {\n@saria.ensures true\nreset a; }",
    ] {
        let source = format!("OPENQASM 3; include \"stdgates.inc\"; qubit q;\n{tail}");
        assert!(
            frontend::parse_str(&source, "bad.qasm").is_err(),
            "accepted {tail}"
        );
    }
}

#[test]
fn quantum_expression_structure_is_reserved_but_not_admitted_by_classical_checking() {
    let expr = parse_expression(
        "trace_distance(avg_density(q[0]), normalize(diag(cosh(1), cosh(0.5)))) <= 1e-6",
    )
    .unwrap();
    let SpecExpr::Binary { left, .. } = expr else {
        panic!()
    };
    assert!(matches!(
        left.as_ref(),
        SpecExpr::Call {
            function: MathFunction::TraceDistance,
            ..
        }
    ));
    let error = frontend::parse_str("OPENQASM 3; qubit[2] q; bool stop = false;\n\
        @saria.ensures trace_distance(avg_density(q[0]), normalize(diag(cosh(1), cosh(0.5)))) <= 1e-6\n\
        while (!stop) { stop = true; }", "density.qasm").unwrap_err();
    assert!(error.to_string().contains("reserved"));
}

#[test]
fn builtin_constant_names_respect_program_shadowing_and_constants_fold_exactly() {
    let p = frontend::parse_str(
        "OPENQASM 3; qubit q; const int n = 5; const float f = 0.5;\n\
         @saria.requires n! > f && pi > 3\nreset q;\n\
         if (true) { bit pi;\n@saria.ensures pi == 0\nreset q; }",
        "constants.qasm",
    )
    .unwrap();
    let a = &p.annotations[&p.body.statements[0].ast_id()][0];
    let AnnotationPayload::Expression(SpecExpr::Binary {
        op: BinaryOp::And,
        left,
        right,
    }) = &a.payload
    else {
        panic!()
    };
    let SpecExpr::Binary {
        left: factorial,
        right: f,
        ..
    } = left.as_ref()
    else {
        panic!()
    };
    assert_eq!(factorial.as_ref(), &unary(UnaryOp::Factorial, number(5)));
    assert_eq!(f.as_ref(), &parse_expression("0.5").unwrap());
    let SpecExpr::Binary { left: pi, .. } = right.as_ref() else {
        panic!()
    };
    assert_eq!(pi.as_ref(), &SpecExpr::Constant(iqir::NumericConstant::Pi));
    let StatementKind::If { then_branch, .. } = &p.body.statements[1].kind else {
        panic!()
    };
    let a = &p.annotations[&then_branch.statements[0].ast_id()][0];
    let AnnotationPayload::Expression(SpecExpr::Binary { left, .. }) = &a.payload else {
        panic!()
    };
    let SpecExpr::Symbol { id, name } = left.as_ref() else {
        panic!("shadowed pi became a constant")
    };
    assert_eq!(name, "pi");
    assert_eq!(*id, then_branch.classical_registers[0].id);
}

#[test]
fn annotations_on_if_and_custom_gate_calls_do_not_attach_to_children() {
    let p = frontend::parse_str(
        "OPENQASM 3; include \"stdgates.inc\"; qubit q;\n\
         gate g a { h a; x a; }\n\
         @saria.ensures true\ng q;\n\
         @saria.requires true\nif (true) {\n@saria.ensures true\nx q; }",
        "group.qasm",
    )
    .unwrap();
    assert_eq!(p.annotations.len(), 3);
    let gate = &p.body.statements[0];
    assert!(p.annotations.contains_key(&gate.ast_id()));
    let StatementKind::Scope(b) = &gate.kind else {
        panic!()
    };
    assert!(
        b.statements
            .iter()
            .all(|s| !p.annotations.contains_key(&s.ast_id()))
    );
    let branch = &p.body.statements[1];
    assert!(p.annotations.contains_key(&branch.ast_id()));
    let StatementKind::If { then_branch, .. } = &branch.kind else {
        panic!()
    };
    assert!(
        p.annotations
            .contains_key(&then_branch.statements[0].ast_id())
    );
}
