use iqir::{StatementKind, annotation::*, frontend};

fn parse(body: &str) -> Result<iqir::Program, String> {
    frontend::parse_str(&format!("OPENQASM 3;\n{body}"), "loop-probability.qasm")
        .map_err(|e| e.to_string())
}

#[test]
fn syntax_preserves_relations_expressions_and_spans() {
    let span = SourceSpan {
        source: "test".into(),
        start: 10,
        end: 50,
    };
    let counter = parse_annotation("@saria.loop_counter count", span.clone()).unwrap();
    assert_eq!(counter.kind, AnnotationKind::LoopCounter);
    assert_eq!(counter.span, span);
    assert!(
        matches!(counter.payload, AnnotationPayload::LoopCounter { id: None, ref name } if name == "count")
    );
    for (op, expected) in [
        ("==", ProbabilityRelation::Equal),
        (">=", ProbabilityRelation::AtLeast),
        ("<=", ProbabilityRelation::AtMost),
    ] {
        let a = parse_annotation(
            &format!("@saria.exit_probability {op} rate(count)"),
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
        "@saria.loop_counter",
        "@saria.loop_counter n + 1",
        "@saria.loop_counter 1",
        "@saria.loop_counter n[0]",
        "@saria.loop_counter_extra n",
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
fn program_counter_and_helper_arguments_resolve_to_the_same_symbol() {
    let p = parse(
        "pragma saria.def rate(k: uint[8]) -> float = k == 0 ? 0.5 : 0.75
uint[8] n=0; bool stop=false;
@saria.loop_counter n
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
    let AnnotationPayload::LoopCounter { id: Some(id), .. } = a[0].payload else {
        panic!()
    };
    assert!(p.classical_registers.iter().any(|r| r.id == id));
    let AnnotationPayload::ExitProbability {
        relation: ProbabilityRelation::Equal,
        bound: SpecExpr::HelperCall { arguments, .. },
    } = &a[1].payload
    else {
        panic!()
    };
    assert!(matches!(arguments[0].uncast(), SpecExpr::Symbol { id: found, .. } if *found == id));
    assert_eq!(
        a[4].payload,
        AnnotationPayload::Termination(TerminationKind::AlmostSure)
    );
}

#[test]
fn ghost_counter_uses_existing_scope_and_annotation_order() {
    let p = parse(
        "bool done=false;
@saria.ghost tick: int[32] = 0
@saria.exit_probability >= tick == 0 ? 0.25 : 0.5
@saria.loop_counter tick
while (!done) {
  @saria.set tick = tick + 1
  done=true;
}",
    )
    .unwrap();
    let a = p
        .annotations
        .values()
        .find(|a| a.iter().any(|a| a.kind == AnnotationKind::LoopCounter))
        .unwrap();
    let AnnotationPayload::GhostDeclare {
        id: Some(ghost),
        scoped: true,
        ..
    } = a[0].payload
    else {
        panic!()
    };
    assert!(
        matches!(a[2].payload, AnnotationPayload::LoopCounter { id: Some(id), .. } if id == ghost)
    );
    assert!(
        parse(
            "bool done=false;
@saria.loop_counter tick
@saria.ghost tick: int = 0
while (!done) {done=true;}"
        )
        .is_err()
    );
    assert!(
        parse(
            "bool done=false;
@saria.ghost tick: int = 0
@saria.loop_counter tick
while (!done) {done=true;}
@saria.loop_counter tick
while (false) {}"
        )
        .is_err()
    );
}

#[test]
fn counters_are_integer_variables_not_values_or_other_storage() {
    for declaration in ["int n=0;", "uint[8] n=0;", "@saria.ghost n: int\n"] {
        parse(&format!(
            "{declaration}\n@saria.loop_counter n\nwhile(false) {{}}"
        ))
        .unwrap();
    }
    for declaration in [
        "float n=0.0;",
        "bool n=false;",
        "bit n;",
        "bit[8] n;",
        "angle[8] n;",
        "qubit n;",
        "const int n=0;",
        "const uint[8] n=0;",
        "",
        "@saria.ghost n: float = 0.0\n",
    ] {
        let e = parse(&format!(
            "{declaration}\n@saria.loop_counter n\nwhile(false) {{}}"
        ))
        .unwrap_err();
        assert!(
            e.contains("loop_counter") || e.contains("loop counter"),
            "{e}"
        );
    }
}

#[test]
fn exit_probability_requires_its_own_single_while_counter() {
    for annotations in [
        "@saria.exit_probability == 0.5",
        "@saria.loop_counter n\n@saria.loop_counter n",
        "@saria.loop_counter n\n@saria.loop_counter m",
    ] {
        assert!(
            parse(&format!(
                "int n=0; int m=0;\n{annotations}\nwhile(false) {{}}"
            ))
            .is_err()
        );
    }
    for statement in ["n=1;", "if(true) {n=1;}", "for int k in [0:2] {n=1;}"] {
        assert!(
            parse(&format!(
                "int n=0;\n@saria.loop_counter n\n@saria.exit_probability >= 0.5\n{statement}"
            ))
            .is_err()
        );
    }
    assert!(
        parse(
            "int n=0;
@saria.loop_counter n
while(false) {
  @saria.exit_probability == 0.5
  while(false) {}
}"
        )
        .is_err()
    );
}

#[test]
fn probability_bounds_are_typed_without_proving_them() {
    for bound in [
        "0",
        "1.0",
        "n == 0 ? 0.5 : 0.75",
        "\\sin(1.0)",
        "2.0",
        "-0.5",
    ] {
        // Range and probability correctness are backend obligations, not parsing.
        parse(&format!(
            "int n=0;\n@saria.loop_counter n\n@saria.exit_probability >= {bound}\nwhile(false) {{}}"
        ))
        .unwrap();
    }
    for bound in ["true", "n == 0", "|0>", "\\i", "a", "unknown", "missing(n)"] {
        assert!(parse(&format!("int n=0; angle[8] a;\n@saria.loop_counter n\n@saria.exit_probability == {bound}\nwhile(false) {{}}")).is_err(), "{bound}");
    }
}

#[test]
fn nested_counters_and_bounds_follow_shadowing() {
    let p = parse(
        "int n=0;
@saria.loop_counter n
@saria.exit_probability >= n == 0 ? 0.5 : 1.0
while(false) {
  @saria.ghost n: int = 1
  @saria.loop_counter n
  @saria.exit_probability == n == 1 ? 0.75 : 1.0
  while(false) {}
}",
    )
    .unwrap();
    let ids: Vec<_> = p
        .annotations
        .values()
        .filter_map(|a| {
            a.iter().find_map(|a| {
                if let AnnotationPayload::LoopCounter { id, .. } = a.payload {
                    id
                } else {
                    None
                }
            })
        })
        .collect();
    assert_eq!(ids.len(), 2);
    assert_ne!(ids[0], ids[1]);
}
