use iqir::{StatementKind, annotation::*, frontend};

fn parse(body: &str) -> Result<iqir::Program, String> {
    frontend::parse_str(&format!("OPENQASM 3;\n{body}"), "loop-probability.qasm")
        .map_err(|e| e.to_string())
}

fn probability_symbol(annotation: &Annotation) -> iqir::SymbolId {
    let AnnotationPayload::ExitProbability { bound, .. } = &annotation.payload else {
        panic!("expected probability clause")
    };
    let SpecExpr::Symbol { id, .. } = bound.uncast() else {
        panic!("expected variable bound")
    };
    *id
}

#[test]
fn syntax_preserves_relations_expressions_and_spans() {
    let span = SourceSpan {
        source: "test".into(),
        start: 10,
        end: 50,
    };
    for (op, expected) in [
        ("==", ProbabilityRelation::Equal),
        (">=", ProbabilityRelation::AtLeast),
        ("<=", ProbabilityRelation::AtMost),
    ] {
        let a = parse_annotation(
            &format!("@saria.exit_probability {op} rate(n)"),
            span.clone(),
        )
        .unwrap();
        assert_eq!(a.kind, AnnotationKind::ExitProbability);
        assert_eq!(a.span, span);
        assert!(
            matches!(a.payload, AnnotationPayload::ExitProbability { relation, .. } if relation == expected)
        );
    }
    for text in [
        "@saria.loop_counter n",
        "@saria.exit_probability 0.5",
        "@saria.exit_probability > 0.5",
        "@saria.exit_probability != 0.5",
        "@saria.exit_probability >=",
        "@saria.exit_probability == 0.5;",
    ] {
        assert!(parse_annotation(text, span.clone()).is_err(), "{text}");
    }
}

#[test]
fn helper_arguments_resolve_program_variables_without_designation() {
    let p = parse(
        "pragma saria.def rate(k: uint[8]) -> float = k == 0 ? 0.5 : 0.75
uint[8] n=0; bool stop=false;
@saria.exit_probability == rate(n)
@saria.exit_probability >= 0.5
@saria.invariant n <= 5
@saria.terminates almost_sure
while (!stop) { n=0; stop=true; }",
    )
    .unwrap();
    let s = p
        .body
        .statements
        .iter()
        .find(|s| matches!(s.kind, StatementKind::While { .. }))
        .unwrap();
    let a = &p.annotations[&s.ast_id()];
    let id = p
        .classical_registers
        .iter()
        .find(|r| r.name == "n")
        .unwrap()
        .id;
    let AnnotationPayload::ExitProbability {
        relation: ProbabilityRelation::Equal,
        bound: SpecExpr::HelperCall { arguments, .. },
    } = &a[0].payload
    else {
        panic!()
    };
    assert!(matches!(arguments[0].uncast(), SpecExpr::Symbol { id: found, .. } if *found == id));
    assert_eq!(a.len(), 4);
    assert_eq!(
        a[3].payload,
        AnnotationPayload::Termination(TerminationKind::AlmostSure)
    );
}

#[test]
fn probability_variables_use_existing_ghost_scope_and_annotation_order() {
    let p = parse(
        "bool done=false;
@saria.ghost rate: float = 0.25
@saria.exit_probability >= rate
while (!done) {
  @saria.set rate = 0.5
  done=true;
}",
    )
    .unwrap();
    let a = p
        .annotations
        .values()
        .find(|a| a.iter().any(|a| a.kind == AnnotationKind::ExitProbability))
        .unwrap();
    let AnnotationPayload::GhostDeclare {
        id: Some(ghost),
        scoped: true,
        ..
    } = a[0].payload
    else {
        panic!()
    };
    assert_eq!(probability_symbol(&a[1]), ghost);
    for source in [
        "bool done=false;
@saria.exit_probability >= rate
@saria.ghost rate: float = 0.25
while (!done) {done=true;}",
        "bool done=false;
@saria.ghost rate: float = 0.25
@saria.exit_probability >= rate
while (!done) {done=true;}
@saria.exit_probability >= rate
while (false) {}",
    ] {
        let error = parse(source).unwrap_err();
        assert!(error.contains("rate"), "{error}");
    }
}

#[test]
fn exit_probability_needs_only_its_while_statement() {
    parse("@saria.exit_probability == 0.5\nwhile(false) {}").unwrap();
    parse(
        "@saria.exit_probability >= 0.25
while(false) {
  @saria.exit_probability == 0.5
  while(false) {}
}",
    )
    .unwrap();
    for statement in ["n=1;", "if(true) {n=1;}", "for int k in [0:2] {n=1;}"] {
        let error = parse(&format!(
            "int n=0;\n@saria.exit_probability >= 0.5\n{statement}"
        ))
        .unwrap_err();
        assert!(error.contains("while statement"), "{error}");
    }
}

#[test]
fn probability_bounds_are_typed_without_proving_them() {
    for bound in [
        "0",
        "1.0",
        "n == 0 ? 0.5 : p",
        "p",
        "fixed",
        "\\real(1)/2",
        "\\sin(1.0)",
        "2.0",
        "-0.5",
    ] {
        // Range and probability correctness are backend obligations, not parsing.
        parse(&format!(
            "int n=0; float p=0.75; const float fixed=0.5;\n@saria.exit_probability >= {bound}\nwhile(false) {{}}"
        ))
        .unwrap();
    }
    for bound in ["true", "n == 0", "|0>", "\\i", "a", "unknown", "missing(n)"] {
        assert!(
            parse(&format!(
                "int n=0; angle[8] a;\n@saria.exit_probability == {bound}\nwhile(false) {{}}"
            ))
            .is_err(),
            "{bound}"
        );
    }
}

#[test]
fn nested_probability_bounds_follow_shadowing() {
    let p = parse(
        "float rate=0.5;
@saria.exit_probability >= rate
while(false) {
  @saria.ghost rate: float = 0.75
  @saria.exit_probability == rate
  while(false) {}
}",
    )
    .unwrap();
    let ids: Vec<_> = p
        .annotations
        .values()
        .flatten()
        .filter(|a| a.kind == AnnotationKind::ExitProbability)
        .map(probability_symbol)
        .collect();
    assert_eq!(ids.len(), 2);
    assert_ne!(ids[0], ids[1]);
}
