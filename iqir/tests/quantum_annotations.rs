use iqir::annotation::*;
use iqir::frontend;

fn checked(text: &str) -> Result<(SpecExpr, SpecType), String> {
    let mut expression = parse_expression(text).map_err(|e| e.to_string())?;
    let ty = check_expression(&mut expression, &[], |name| Err(format!("unknown {name}")))
        .map_err(|e| e.to_string())?;
    Ok((expression, ty))
}

#[test]
fn state_and_pauli_literals_are_structured_not_names() {
    use QubitState::*;
    for (source, factors) in [
        ("|0>", vec![Zero]),
        ("|1>", vec![One]),
        ("|+>", vec![Plus]),
        ("|->", vec![Minus]),
        ("|−⟩", vec![Minus]),
        ("|+i>", vec![PlusI]),
        ("|-i>", vec![MinusI]),
        ("|−i⟩", vec![MinusI]),
        ("|01+->", vec![Zero, One, Plus, Minus]),
        ("|+i -i⟩", vec![PlusI, MinusI]),
    ] {
        let (expression, ty) = checked(source).unwrap();
        assert_eq!(ty, SpecType::Ket(factors.len()));
        assert_eq!(expression, SpecExpr::Ket(factors));
    }
    assert_eq!(
        checked("<+i|").unwrap(),
        (SpecExpr::Bra(vec![PlusI]), SpecType::Bra(1))
    );
    assert_eq!(
        parse_expression("⟨01−|").unwrap(),
        parse_expression("<01-|").unwrap()
    );
    for (source, pauli) in [
        (r"\I", Pauli::I),
        (r"\X", Pauli::X),
        (r"\Y", Pauli::Y),
        (r"\Z", Pauli::Z),
    ] {
        assert_eq!(
            checked(source).unwrap(),
            (SpecExpr::Pauli(pauli), SpecType::Operator(1))
        );
    }
    assert_eq!(
        checked(r"\i").unwrap(),
        (SpecExpr::ImaginaryUnit, SpecType::Complex)
    );
    for plain_name in ["X", "Y", "Z", "I", "i"] {
        assert_eq!(
            parse_expression(plain_name).unwrap(),
            SpecExpr::Name(plain_name.into())
        );
    }
}

#[test]
fn linear_algebra_preserves_dimensions_and_complex_sorts() {
    use SpecType::*;
    for (source, ty) in [
        ("(|0> + |1>) / \\sqrt(2)", Ket(1)),
        ("(|00> + |11>) / \\sqrt(2)", Ket(2)),
        (r"(|0> + \i * |1>) / \sqrt(2)", Ket(1)),
        ("-|+>", Ket(1)),
        (r"|0> \otimes |1>", Ket(2)),
        ("|0⟩ ⊗ |1⟩", Ket(2)),
        (r"\X * |0>", Ket(1)),
        (r"(\X \otimes \Z) * |01>", Ket(2)),
        (r"\X * \Y", Operator(1)),
        (r"\X + \i * \Y", Operator(1)),
        ("|+> * <+|", Operator(1)),
        ("<0| * |1>", Complex),
        (r"<+| * \X * |+>", Complex),
        (r"<0| * \X", Bra(1)),
        (r"<0| \otimes <1|", Bra(2)),
        ("\\adjoint(|+>)", Bra(1)),
        ("\\adjoint(<+|)", Ket(1)),
        (r"\adjoint(\Y)", Operator(1)),
        (r"\adjoint(1 + \i)", Complex),
        (r"\conj(1 + \i)", Complex),
        (r"\abs(1 + \i)", Float(None)),
        ("\\re(<0| * |1>)", Float(None)),
        ("\\im(<0| * |1>)", Float(None)),
        (r"(1 + \i) / (1 - \i)", Complex),
        (r"\i^2", Complex),
        ("true ? |0> : |1>", Ket(1)),
        (r"true ? 1 : \i", Complex),
        (r"\sum(j in 0..5, (1/(j+1))*|0>)", Ket(1)),
        (r"\sum(j in 0..5, (1/(j+1))*\X)", Operator(1)),
        (r"\product(j in 0..5, j + \i)", Complex),
        (
            r"\forall n in 0..5; (\cos(n)*|0> + \sin(n)*|1>) == |+>",
            Bool,
        ),
        (r"\Y * |0> == \i * |1>", Bool),
        (r"(\X \otimes \Z) == (\X \otimes \Z)", Bool),
        ("\\abs(<+| * |0>)^2 <= 1", Bool),
    ] {
        assert_eq!(
            checked(source)
                .unwrap_or_else(|e| panic!("{source}: {e}"))
                .1,
            ty,
            "{source}"
        );
    }
}

#[test]
fn quantum_notation_does_not_change_boolean_or_arithmetic_precedence() {
    for (source, explicit) in [
        (r"\X * \Y \otimes \Z", r"(\X * \Y) \otimes \Z"),
        (
            r"\X \otimes \Y + \Z \otimes \I",
            r"(\X \otimes \Y) + (\Z \otimes \I)",
        ),
        (r"2*|0> \otimes |1>", r"(2*|0>) \otimes |1>"),
        ("|0> == |1> || true", "(|0> == |1>) || true"),
        ("true || |0> == |1>", "true || (|0> == |1>)"),
        ("|0> == |1> && 0 < 1", "(|0> == |1>) && (0 < 1)"),
    ] {
        assert_eq!(
            parse_expression(source).unwrap(),
            parse_expression(explicit).unwrap()
        );
    }
    // Pauli identities and state equalities are not evaluated by the parser.
    assert!(matches!(
        checked(r"\X * |0> == |1>").unwrap().0,
        SpecExpr::Binary {
            op: BinaryOp::Eq,
            ..
        }
    ));
    assert_ne!(
        parse_expression("|01>").unwrap(),
        parse_expression(r"|0> \otimes |1>").unwrap()
    );
}

#[test]
fn compact_dirac_products_desugar_to_typed_multiplication() {
    for (compact, explicit, ty) in [
        ("<0|1>", "<0| * |1>", SpecType::Complex),
        ("<0|0>", "<0| * |0>", SpecType::Complex),
        ("⟨+i|−i⟩", "<+i| * |-i>", SpecType::Complex),
        ("<01+-|10-+>", "<01+-| * |10-+>", SpecType::Complex),
        ("< +i -i | 0 1 >", "<+i -i| * |01>", SpecType::Complex),
        ("|0><0|", "|0> * <0|", SpecType::Operator(1)),
        ("|+i⟩⟨−i|", "|+i> * <-i|", SpecType::Operator(1)),
        ("|01><10|", "|01> * <10|", SpecType::Operator(2)),
        ("| 0 1 > < 1 0 |", "|01> * <10|", SpecType::Operator(2)),
    ] {
        assert_eq!(
            parse_expression(compact).unwrap(),
            parse_expression(explicit).unwrap(),
            "{compact}"
        );
        let (expression, actual) = checked(compact).unwrap();
        assert_eq!(actual, ty, "{compact}");
        assert_eq!((expression.clone(), actual), checked(explicit).unwrap());
        // Even <0|0> remains a symbolic product, not the computed number 1.
        assert!(matches!(
            expression,
            SpecExpr::Binary {
                op: BinaryOp::Mul,
                ..
            }
        ));
    }
}

#[test]
fn compact_dirac_pairs_are_primaries_without_changing_other_precedence() {
    for (compact, explicit) in [
        ("2 * |0><0|", "2 * (|0> * <0|)"),
        ("|0><0| * |1>", "(|0> * <0|) * |1>"),
        ("<0|1> + <1|0>", "(<0| * |1>) + (<1| * |0>)"),
        ("<0|1>^2", "(<0| * |1>)^2"),
        ("-|0><0|", "-(|0> * <0|)"),
        ("<0|1> / <1|0>", "(<0| * |1>) / (<1| * |0>)"),
        (r"\adjoint(|0><1|)", r"\adjoint((|0> * <1|))"),
        (r"|0><0| \otimes |1><1|", r"(|0> * <0|) \otimes (|1> * <1|)"),
        ("<0|1> == 0 || true", "((<0| * |1>) == 0) || true"),
        ("true || <0|1> == 0", "true || ((<0| * |1>) == 0)"),
        ("|0><0| == |1><1|", "(|0> * <0|) == (|1> * <1|)"),
        ("0 < 1 && <0|1> == 0", "(0 < 1) && ((<0| * |1>) == 0)"),
        ("1 > 0 && <0|1> == 0", "(1 > 0) && ((<0| * |1>) == 0)"),
        ("true ? <0|1> : <1|0>", "true ? (<0| * |1>) : (<1| * |0>)"),
    ] {
        assert_eq!(
            parse_expression(compact).unwrap(),
            parse_expression(explicit).unwrap(),
            "{compact}"
        );
        assert_eq!(checked(compact).unwrap(), checked(explicit).unwrap());
    }
}

#[test]
fn compact_dirac_products_keep_literal_dimension_and_syntax_limits() {
    for bad in [
        "<|0>",
        "<0|>",
        "<0|1",
        "<2|0>",
        "<0|2>",
        "<psi|phi>",
        "|0><|",
        "|0><2|",
        "|0><psi|",
        "<0||1>",
        "<0|1><1|0>",
        "|0><0||1><1|",
        "2|0>",
        r"\X|0>",
        "|0>|1>",
        r"<0|\X|1>",
    ] {
        assert!(parse_expression(bad).is_err(), "accepted {bad}");
    }
    for bad in ["<0|00>", "⟨00|0⟩", "|0><00|", "|00⟩⟨0|"] {
        let mut expression = parse_expression(bad).unwrap();
        let error = check_expression(&mut expression, &[], |_| unreachable!()).unwrap_err();
        assert!(
            error.to_string().contains("invalid linear product"),
            "{bad}: {error}"
        );
    }
    let max = "0".repeat(64);
    assert_eq!(
        checked(&format!("<{max}|{max}>")).unwrap().1,
        SpecType::Complex
    );
    assert_eq!(
        checked(&format!("|{max}><{max}|")).unwrap().1,
        SpecType::Operator(64)
    );
    let excessive = "0".repeat(65);
    for bad in [
        format!("<{excessive}|0>"),
        format!("<0|{excessive}>"),
        format!("|{excessive}><0|"),
        format!("|0><{excessive}|"),
    ] {
        let error = parse_expression(&bad).unwrap_err();
        assert!(
            error.message.contains("quantum dimension budget"),
            "{bad}: {error}"
        );
    }
}

#[test]
fn compact_dirac_products_import_in_annotations_and_helpers() {
    let source = r"OPENQASM 3;
qubit q;
pragma saria.def overlap(x: float) -> float = x * \re(⟨0|1⟩)
@saria.requires overlap(1) == 0 && <0|1> == 0 || false
@saria.ensures |0⟩⟨0| * |0> == |0>
reset q;
";
    let explicit = source
        .replace("⟨0|1⟩", "(<0| * |1>)")
        .replace("<0|1>", "(<0| * |1>)")
        .replace("|0⟩⟨0|", "(|0> * <0|)");
    let program = frontend::parse_str(source, "compact.qasm").unwrap();
    let expanded = frontend::parse_str(&explicit, "explicit.qasm").unwrap();
    assert_eq!(program.spec_functions.len(), 1);
    assert_eq!(
        program.spec_functions[0].body,
        expanded.spec_functions[0].body
    );
    assert_eq!(program.annotations.len(), 1);
    let annotations = program.annotations.values().next().unwrap();
    let expanded_annotations = expanded.annotations.values().next().unwrap();
    assert_eq!(annotations.len(), 2);
    for ((annotation, expanded), expected_text) in
        annotations.iter().zip(expanded_annotations).zip([
            "@saria.requires overlap(1) == 0 && <0|1> == 0 || false",
            "@saria.ensures |0⟩⟨0| * |0> == |0>",
        ])
    {
        assert_eq!(annotation.payload, expanded.payload);
        assert_eq!(
            &source[annotation.span.start..annotation.span.end],
            expected_text
        );
    }
}

#[test]
fn invalid_quantum_dimensions_and_operations_are_rejected() {
    for source in [
        "|>", "<|", "|2>", "|psi>", "|i>", "|0", "<0>", r"\XX", r"\Xfoo", r"\ifoo", r"\otimes",
        "2|0>", "|0>|1>",
    ] {
        assert!(parse_expression(source).is_err(), "accepted {source}");
    }
    for source in [
        "|0> + |00>",
        "|0> == |00>",
        "|0> == <0|",
        r"\X * |00>",
        "|0> * |1>",
        "<0| * <1|",
        "|0> * <00|",
        r"\X + |0>",
        "|0> + 1",
        "|0> > |1>",
        "|0> && true",
        r"\i < 1",
        r"\i!",
        r"\i % 2",
        r"\i^0.5",
        r"|0> \otimes \X",
        r"2 \otimes |0>",
        "|0> / |1>",
        "1 / |0>",
        "|0>^2",
        "\\sin(|0>)",
        r"\sin(\i)",
        "\\abs(|0>)",
        "\\conj(|0>)",
        "\\re(|0>)",
        "\\adjoint(true)",
        "\\adjoint()",
        "true ? |0> : |00>",
        r"\forall i in 0..1; |0>",
        r"\sup(i in 0..1, |0>)",
        r"\sum(i in 0..1, true)",
        r"\product(i in 0..1, \X)",
    ] {
        assert!(checked(source).is_err(), "accepted {source}");
    }
    let max = format!("|{}>", "0".repeat(64));
    assert_eq!(checked(&max).unwrap().1, SpecType::Ket(64));
    assert!(parse_expression(&format!("|{}>", "0".repeat(65))).is_err());
    assert!(checked(&format!(r"{max} \otimes |0>")).is_err());
    for mut expression in [
        SpecExpr::Ket(vec![]),
        SpecExpr::Bra(vec![QubitState::Zero; 65]),
    ] {
        assert!(check_expression(&mut expression, &[], |_| unreachable!()).is_err());
    }
}

#[test]
fn quantum_annotations_import_with_classical_parameters_and_no_state_assumptions() {
    let source = r"OPENQASM 3;
qubit[2] q;
int n = 2;
float theta = 0.5;
int X = 3;
pragma saria.def amp(t: float) -> float = \cos(t)
pragma saria.def overlap(t: float) -> float = \abs(<0| * (\cos(t)*|0> + \sin(t)*|1>))^2
@saria.requires X == 3 && \X * |0> == |1>
@saria.ensures (amp(theta)*|0> + \sin(theta)*|1>) == |+>
reset q;
@saria.invariant \forall k in 0..n; \Y * |0> == \i * |1>
while (n > 0) { n -= 1; }
@saria.requires |−⟩ == (|0⟩ - |1⟩)/\sqrt(2) && overlap(theta) <= 1
reset q;
";
    let program = frontend::parse_str(source, "quantum-spec.qasm").unwrap();
    assert_eq!(program.spec_functions.len(), 2);
    assert_eq!(program.annotations.len(), 3);
    for annotations in program.annotations.values() {
        for annotation in annotations {
            let text = &source[annotation.span.start..annotation.span.end];
            let AnnotationPayload::Expression(unresolved) =
                parse_annotation(text, annotation.span.clone())
                    .unwrap()
                    .payload
            else {
                panic!()
            };
            // Exact UTF-8 spans include the quantum notation, not executable code.
            assert!(matches!(
                unresolved,
                SpecExpr::Binary { .. } | SpecExpr::Binder { .. }
            ));
        }
    }
    frontend::parse_str(
        "OPENQASM 3; qubit q;\n@saria.ensures q == |0>\nreset q;",
        "state-predicate.qasm",
    )
    .unwrap();
}

#[test]
fn helper_instantiation_traverses_amplitudes_and_keeps_quantum_leaves() {
    let mut functions = Vec::new();
    let source =
        r"pragma saria.def amplitude(n: int) -> float = \re(<0| * \sum(j in 0..n, (1/(j+1))*|0>))";
    let id = define_function(
        &mut functions,
        parse_function(
            source,
            SourceSpan {
                source: "amplitudes.qasm".into(),
                start: 0,
                end: source.len(),
            },
        )
        .unwrap(),
    )
    .unwrap();
    let argument = parse_expression("5").unwrap();
    let instantiated =
        instantiate_function(&functions, id, std::slice::from_ref(&argument)).unwrap();
    let SpecExpr::Call {
        function: MathFunction::RealPart,
        arguments,
    } = instantiated.uncast()
    else {
        panic!()
    };
    let SpecExpr::Binary {
        op: BinaryOp::Mul,
        left,
        right,
    } = &arguments[0]
    else {
        panic!()
    };
    assert_eq!(**left, SpecExpr::Bra(vec![QubitState::Zero]));
    let SpecExpr::Binder {
        id: Some(local),
        upper,
        body,
        ..
    } = right.as_ref()
    else {
        panic!()
    };
    assert_ne!(*local, 0, "substitution must freshen the helper's binder");
    assert_eq!(upper.uncast(), &argument);
    let SpecExpr::Binary {
        op: BinaryOp::Mul,
        left,
        right,
    } = body.as_ref()
    else {
        panic!()
    };
    assert_eq!(**right, SpecExpr::Ket(vec![QubitState::Zero]));
    let SpecExpr::Binary {
        op: BinaryOp::Div,
        right,
        ..
    } = left.as_ref()
    else {
        panic!()
    };
    let SpecExpr::Binary {
        op: BinaryOp::Add,
        left,
        ..
    } = right.as_ref()
    else {
        panic!()
    };
    assert_eq!(**left, SpecExpr::BoundVariable(*local));
}
