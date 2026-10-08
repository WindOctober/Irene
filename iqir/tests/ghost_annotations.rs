use iqir::{StatementKind, annotation::*, frontend};

fn parse(body: &str) -> Result<iqir::Program, String> {
    frontend::parse_str(
        &format!("OPENQASM 3; include \"stdgates.inc\"; qubit q;\n{body}"),
        "ghost.qasm",
    )
    .map_err(|e| e.to_string())
}

#[test]
fn ghosts_are_resolved_and_loop_declarations_are_scoped() {
    let p = parse(
        "bool done=false;
@saria.ghost steps: int = 0
@saria.invariant steps >= 0
while (!done) {
  @saria.set steps = steps + 1
  done=true;
}",
    )
    .unwrap();
    let s = p
        .body
        .statements
        .iter()
        .find(|s| matches!(s.kind, StatementKind::While { .. }))
        .unwrap();
    let a = &p.annotations[&s.ast_id()];
    let AnnotationPayload::GhostDeclare {
        id: Some(id),
        scoped,
        ..
    } = a[0].payload
    else {
        panic!()
    };
    assert!(scoped);
    let AnnotationPayload::Expression(SpecExpr::Binary { ref left, .. }) = a[1].payload else {
        panic!()
    };
    assert!(matches!(left.uncast(), SpecExpr::Symbol { id: found, .. } if *found == id));
    assert!(
        parse(
            "bool done=false;
@saria.ghost steps: int = 0
while (!done) { done=true; }
@saria.ensures steps == 0
reset q;"
        )
        .is_err()
    );
}

#[test]
fn block_scope_shadowing_and_later_assignment() {
    parse(
        "@saria.ghost count: int
reset q;
@saria.set count = 3
reset q;
if (true) {
  @saria.ghost count: float = 1/2
  @saria.ensures count == 1/2
  reset q;
}
@saria.ensures count == 3
reset q;",
    )
    .unwrap();
    assert!(
        parse(
            "if (true) {
  @saria.ghost inner: int = 0
  reset q;
}
@saria.set inner = 1
reset q;"
        )
        .is_err()
    );
    assert!(
        parse(
            "bool done=false;
while (!done) {
  @saria.ghost inner: int = 0
  done=true;
}
@saria.ensures inner == 0
reset q;"
        )
        .is_err()
    );
}

#[test]
fn ghost_names_cannot_drive_executable_operations() {
    for use_site in [
        "if (flag) { x q; }",
        "while (flag) { reset q; }",
        "flag = false;",
        "int n=flag;",
    ] {
        assert!(
            parse(&format!(
                "@saria.ghost flag: bool = true\nreset q;\n{use_site}"
            ))
            .is_err(),
            "{use_site}"
        );
    }
    assert!(parse("@saria.ghost theta: float = 0\nreset q;\nrx(theta) q;").is_err());
}

#[test]
fn ghost_widths_and_program_reference_types_are_preserved() {
    let p = parse(
        "int[8] n=2; float[32] f=0.5;
@saria.ghost i: int[8] = n
@saria.ghost r: float[32] = f
@saria.ghost u: uint[16] = 3
@saria.ghost a: angle[12]
reset q;",
    )
    .unwrap();
    let annotations = p.annotations.values().next().unwrap();
    for (annotation, expected) in annotations.iter().zip([
        SpecType::Int(Some(8)),
        SpecType::Float(Some(32)),
        SpecType::Uint(Some(16)),
        SpecType::Angle(Some(12)),
    ]) {
        let AnnotationPayload::GhostDeclare { ty, .. } = annotation.payload else {
            panic!()
        };
        assert_eq!(ty, expected);
    }
    for annotation in &annotations[..2] {
        let AnnotationPayload::GhostDeclare {
            ty,
            initializer: Some(SpecExpr::Cast { ty: source, .. }),
            ..
        } = &annotation.payload
        else {
            panic!()
        };
        assert_eq!(ty, source);
    }
    for ty in ["int[0]", "int[65]", "float[16]", "bool[8]", "bit[2]"] {
        assert!(
            parse(&format!("@saria.ghost g: {ty}\nreset q;")).is_err(),
            "{ty}"
        );
    }
}

#[test]
fn integer_division_and_floating_literals_keep_distinct_types() {
    let check = |source: &str| {
        let mut e = parse_expression(source).unwrap();
        check_expression(&mut e, &[], |_| Err("unexpected name".into())).unwrap()
    };
    assert_eq!(check("1/2"), SpecType::Int(Some(32)));
    assert_eq!(check("1.0/2.0"), SpecType::Float(Some(64)));
    assert_ne!(
        parse_expression("1").unwrap(),
        parse_expression("1.0").unwrap()
    );
    let p = parse(
        "pragma saria.def half(x: int[8]) -> float[32] = x/2
@saria.ghost f: float[32] = half(7)
reset q;",
    )
    .unwrap();
    assert_eq!(p.spec_functions[0].parameters[0].ty, SpecType::Int(Some(8)));
    assert_eq!(p.spec_functions[0].result, SpecType::Float(Some(32)));
}

#[test]
fn ghost_types_names_and_attachment_are_checked() {
    for body in [
        "@saria.ghost x: bool = 1\nreset q;",
        "@saria.ghost x: int = 1/2\nreset q;",
        "@saria.ghost x: int = 0\n@saria.ghost x: int = 1\nreset q;",
        "@saria.set missing = 1\nreset q;",
        "int n=0;\n@saria.set n = 1\nreset q;",
        "@saria.ghost x: int = 0",
        "@saria.ghostx: int = 0\nreset q;",
        "@saria.ghost x: bool = true\nreset q;\n@saria.set x = 2\nreset q;",
        "@saria.ghost true: bool = false\nreset q;",
        "@saria.ghost state: bool = q == |0>\nreset q;",
        "@saria.ghost prob: float = \\probability(true)\nreset q;",
        "pragma saria.def p() -> float = \\probability(true)\n@saria.ghost prob: float = p()\nreset q;",
    ] {
        assert!(parse(body).is_err(), "{body}");
    }
}
