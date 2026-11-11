use iqir::{GateDefinition, StatementKind, annotation::SpecType, frontend::openqasm3};

fn source(body: &str) -> String {
    format!("OPENQASM 3; include \"stdgates.inc\";\n{body}")
}

#[test]
fn def_and_gate_summaries_use_one_linear_call_ir() {
    let p = openqasm3::parse_structured(&source(r"
pragma saria.def flip(b: bool) -> ket[1] = b ? |0> : |1>
@saria.summary flip
def leaf(qubit q) { for int j in [0:2] { x q; } }
@saria.summary flip
def parent(qubit q) { leaf(q); }
qubit[2] data; parent(data[0]); parent(data[1]);
"), "def-summary.qasm").unwrap();
    let cs = calls(&p.body); assert_eq!(cs.len(), 2);
    assert!(std::sync::Arc::ptr_eq(cs[0], cs[1]));
    assert_eq!(cs[0].name, "parent");
    assert!(cs[0].summary.is_some());
    for effect in ["reset q;", "bit m = measure q;", "while (true) {}"] {
        let text = source(&format!("pragma saria.def same(b: bool) -> ket[1] = b ? |1> : |0>\n@saria.summary same\ndef f(qubit q) {{{effect}}}\nqubit q; f(q);"));
        assert!(openqasm3::parse_structured(&text, "effect.qasm").is_err(), "{effect}");
    }
}

#[test]
fn def_numeric_summary_specializes_actuals_before_real_embedding() {
    let p = openqasm3::parse_structured(&source(r"
pragma saria.def phase(theta: real,b: bool) -> ket[1] = b ? (\cos(theta)+\i*\sin(theta))*|1> : |0>
@saria.summary phase
def rotate(float[32] theta, qubit q) { p(theta) q; }
float[32] angle_value=0.1; qubit q;
rotate(angle_value,q); rotate(0.2,q);
"), "typed-def.qasm").unwrap();
    let cs = calls(&p.body); assert_eq!(cs.len(), 2);
    assert!(!std::sync::Arc::ptr_eq(cs[0], cs[1]));
    assert_ne!(cs[0].body, cs[1].body);
    assert_eq!(cs[0].parameters.len(), 1);
}

fn calls(block: &iqir::Block) -> Vec<&std::sync::Arc<GateDefinition>> {
    block.statements.iter().flat_map(|s| match &s.kind {
        StatementKind::GateCall { definition, .. } => vec![definition],
        StatementKind::Scope(body) | StatementKind::Unitary { body, .. } => calls(body),
        _ => vec![],
    }).collect()
}

fn called_definition(program: &iqir::Program) -> &GateDefinition {
    calls(&program.body)[0]
}

#[test]
fn rocq_hint_is_metadata_not_a_summary_wrapper() {
    for helper in ["mapping", "mapping(0)"] {
        let parameters = if helper == "mapping" { "" } else { "offset: real, " };
        let text = source(&format!(r"
pragma saria.def mapping({parameters}b: bool) -> ket[1] = b ? |1> : |0>
@saria.summary {helper}
gate unchanged wire {{ x wire; x wire; }}
qubit data; unchanged data;
"));
        let plain = openqasm3::parse_structured(&text, "plain.qasm").unwrap();
        let hinted = openqasm3::parse_structured(
            &text.replace("@saria.summary ", "@saria.summary [rocq] "),
            "hinted.qasm",
        ).unwrap();
        let plain_summary = called_definition(&plain).summary.as_ref().unwrap();
        let hinted_summary = called_definition(&hinted).summary.as_ref().unwrap();
        assert!(!plain_summary.prefer_rocq);
        assert!(hinted_summary.prefer_rocq);
        assert_eq!(plain_summary.function, hinted_summary.function);
        assert_eq!(plain.spec_functions[plain_summary.function.0].body,
            hinted.spec_functions[hinted_summary.function.0].body);
        for invalid in ["[] mapping", "[unknown] mapping", "[rocq][rocq] mapping", "[rocq]", "prefer_rocq(mapping)"] {
            assert!(openqasm3::parse_structured(
                &text.replace(&format!("@saria.summary {helper}"), &format!("@saria.summary {invalid}")),
                "invalid.qasm",
            ).is_err(), "{invalid}");
        }
    }
    let assertion = openqasm3::parse_structured(
        &source("qubit q;\n@saria.assert [rocq] true\nx q;"), "assert.qasm",
    ).unwrap();
    assert!(assertion.annotations.values().flatten().any(|a|
        a.kind == iqir::annotation::AnnotationKind::Assert
            && a.summary_hint == Some(iqir::annotation::SummaryHint::Rocq)));
    assert!(openqasm3::parse_structured(
        &source("qubit q;\n@saria.assert [unknown] true\nx q;"), "invalid.qasm",
    ).is_err());
}

#[test]
fn named_assertion_hint_preserves_expression_and_validates_labels() {
    use iqir::annotation::{parse_annotation, SourceSpan};
    let parse = |text: &str| parse_annotation(text, SourceSpan { source: "test".into(), start: 0, end: text.len() });
    let plain = parse("@saria.assert [rocq] true").unwrap();
    let named = parse("@saria.assert [rocq:observations_1] true").unwrap();
    assert_eq!(named.payload, plain.payload);
    assert_eq!(named.summary_hint, plain.summary_hint);
    assert_eq!(named.proof_group.as_deref(), Some("observations_1"));
    assert_eq!(plain.proof_group, None);
    for invalid in ["[rocq:]", "[rocq:1]", "[rocq:a:b]", "[rocq:a-b]", "[smt:a]"] {
        assert!(parse(&format!("@saria.assert {invalid} true")).is_err(), "{invalid}");
    }
    assert!(parse("@saria.summary [rocq:family] mapping").is_err());
    let program = openqasm3::parse_structured(
        &source("qubit q;\n@saria.assert [rocq:observations_1] true\nx q;"), "named.qasm",
    ).unwrap();
    assert!(program.annotations.values().flatten().any(|a| a.proof_group.as_deref() == Some("observations_1")));
}

#[test]
fn checked_linear_summary_stays_on_shared_gate_definition() {
    let text = source(r"
pragma saria.def phase(angle_value: real) -> complex = \cos(angle_value) + \i * \sin(angle_value)
pragma saria.def mapping(angle_value: real, input_bit: bool) -> ket[1] = input_bit ? phase(angle_value) * |1> : |0>
@saria.summary mapping
gate diagonal(angle_value) wire { p(angle_value) wire; }
qubit data;
diagonal(0.1) data;
diagonal(0.2) data;
");
    let p = openqasm3::parse_structured(&text, "summary.qasm").unwrap();
    let d = called_definition(&p);
    let summary = d.summary.as_ref().unwrap();
    assert_eq!(p.spec_functions[summary.function.0].name, "mapping");
    assert_eq!(p.spec_functions[summary.function.0].result, SpecType::Ket(1));
    assert_eq!(d.body.statements.len(), 1);
    assert!(matches!(d.body.statements[0].kind, StatementKind::Apply { gate: iqir::Gate::P, .. }));
    let calls = calls(&p.body);
    assert!(std::sync::Arc::ptr_eq(calls[0], calls[1]));
    assert!(p.annotations.is_empty());
    assert!(openqasm3::parse_str(&text, "legacy.qasm").is_err());
}

#[test]
fn nested_gate_and_ket_helpers_remain_structured() {
    let text = source(r"
pragma saria.def basis(input_bit: bool) -> ket[1] = input_bit ? |1> : |0>
pragma saria.def mapping(input_bit: bool) -> ket[1] = \sum(z in 0..2, (z == 0 ? \real(1) : \real(0)) * basis(!input_bit))
@saria.summary mapping
gate leaf wire { x wire; }
@saria.summary mapping
gate outer wire { leaf wire; }
qubit data;
outer data;
");
    let p = openqasm3::parse_structured(&text, "nested.qasm").unwrap();
    let outer = called_definition(&p);
    let leaf = calls(&outer.body)[0];
    assert_eq!(outer.summary.as_ref().unwrap().function, leaf.summary.as_ref().unwrap().function);
    let mut ids = iqir::AstIdGenerator::default();
    let instantiated = outer.instantiate(&[], &p.quantum_registers.iter().map(|q| iqir::Qubit { register: q.id, index: 0 }).collect::<Vec<_>>(), &mut ids).unwrap();
    let rebound = calls(&instantiated)[0];
    assert!(std::sync::Arc::ptr_eq(leaf, rebound));
}

#[test]
fn fixed_summary_prefix_desugars_to_the_same_checked_helper_ir() {
    let p = openqasm3::parse_structured(&source(r"
pragma saria.def mapping(offset: real, angle_value: real, bit_value: bool) -> ket[1] = bit_value ? (\cos(offset+angle_value)+\i*\sin(offset+angle_value))*|1> : |0>
@saria.summary mapping(0)
gate diagonal(angle_value) wire { p(angle_value) wire; }
qubit data; diagonal(0.25) data;
"), "bound.qasm").unwrap();
    let helper = &p.spec_functions[called_definition(&p).summary.as_ref().unwrap().function.0];
    assert_eq!(helper.parameters.iter().map(|p| p.ty).collect::<Vec<_>>(),
        [SpecType::Real, SpecType::Bool]);
    assert_eq!(helper.result, SpecType::Ket(1));
    assert!(matches!(helper.body, iqir::annotation::SpecExpr::HelperCall { .. }));

    for fixed in ["captured", "1 / 0", "\\sqrt(-1)", "0.1", "\\real(1e999)", "\\real(-(-0.1))", "2147483648", "-(-(-2147483648))", "false", "0, 1"] {
        let text = source(&format!(r"
const int captured = 0;
pragma saria.def mapping(offset: real, b: bool) -> ket[1] = b ? |1> : |0>
@saria.summary mapping({fixed})
gate identity wire {{ x wire; x wire; }}
qubit data; identity data;
"));
        assert!(openqasm3::parse_structured(&text, "invalid-bound.qasm").is_err(), "{fixed}");
    }
}

#[test]
fn summary_rejects_bad_signature_capture_placement_and_unavailable_helpers() {
    for body in [
        "@saria.summary missing\ngate leaf wire { x wire; }",
        "pragma saria.def mapping(input_bit: bool) -> ket[1] = input_bit ? |1> : |0>\n@saria.summary mapping(true)\ngate leaf wire { x wire; }",
        "pragma saria.def mapping(input_bit: bool) -> ket[1] = input_bit ? |1> : |0>\n@saria.summary mapping\n@saria.summary mapping\ngate leaf wire { x wire; }",
        "pragma saria.def mapping(input_bit: bool) -> ket[1] = input_bit ? |1> : |0>\nqubit data;\n@saria.summary mapping\nx data;",
        "pragma saria.def mapping(input_bit: bool) -> ket[2] = |00>\n@saria.summary mapping\ngate leaf wire { x wire; }",
        "pragma saria.def mapping(input_bit: int) -> ket[1] = |0>\n@saria.summary mapping\ngate leaf wire { x wire; }",
        "pragma saria.def mapping(angle_value: float, input_bit: bool) -> ket[1] = |0>\n@saria.summary mapping\ngate leaf(angle_value) wire { p(angle_value) wire; }",
        "pragma saria.def mapping(input_bit: bool) -> ket[1] = |0>\n@saria.summary mapping\ngate leaf(angle_value) wire { p(angle_value) wire; }",
        "bit captured;\npragma saria.def mapping(input_bit: bool) -> ket[1] = captured ? |1> : |0>",
        "pragma saria.def mapping(input_bit: bool) -> ket[1] = mapping(input_bit)",
        "pragma saria.def mapping(input_bit: bool) -> ket[1] = |00>",
        "pragma saria.def mapping(input_bit: bool) -> ket[0] = |0>",
        "pragma saria.def mapping(input_bit: bool) -> ket[65] = |0>",
        "pragma saria.def mapping(input_bit: bool) -> ket[1] = |0>\n@saria.summary mapping\ngate leaf wire {\n@saria.assert wire == |0>\nx wire; }",
    ] {
        assert!(openqasm3::parse_structured(&source(body), "invalid.qasm").is_err(), "{body}");
    }
}
