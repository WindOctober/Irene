use iqir::{annotation::*, frontend};

fn checked(text: &str) -> SpecExpr {
    let span = SourceSpan {
        source: "approx".into(),
        start: 0,
        end: 0,
    };
    let mut functions = vec![];
    define_function(
        &mut functions,
        parse_approx_config("pragma saria.approx 1e-15", span).unwrap(),
    )
    .unwrap();
    let mut e = parse_expression(text).unwrap();
    assert_eq!(
        check_expression(&mut e, &functions, |_| Err("unbound".into())).unwrap(),
        SpecType::Bool
    );
    e
}

#[test]
fn approx_is_an_exact_bound_on_original_typed_operands() {
    let e = checked(r"0.1 + 0.2 \approx 0.3");
    let SpecExpr::Binary {
        op: BinaryOp::Le,
        left,
        right,
    } = e
    else {
        panic!("{e:?}")
    };
    let SpecExpr::Number(n) = right.uncast() else {
        panic!("{right:?}")
    };
    assert_eq!(n.to_string(), "1/1000000000000000");
    let SpecExpr::Call {
        function: MathFunction::Abs,
        arguments,
    } = *left
    else {
        panic!()
    };
    let SpecExpr::Binary {
        op: BinaryOp::Sub,
        left,
        ..
    } = &arguments[0]
    else {
        panic!()
    };
    let SpecExpr::Cast {
        ty: SpecType::Real,
        operand,
    } = left.as_ref()
    else {
        panic!("{left:?}")
    };
    assert!(matches!(
        operand.as_ref(),
        SpecExpr::Cast {
            ty: SpecType::Float(_),
            ..
        }
    ));
    checked(r"\i + 1 \approx \i + 1");
    let matrix = checked(r"|0><0| \approx |1><1|");
    let SpecExpr::Binary { left, .. } = matrix else {
        panic!()
    };
    assert!(matches!(
        *left,
        SpecExpr::Call {
            function: MathFunction::TraceDistance,
            ..
        }
    ));
    checked(r"\forall i in 0..3; \real(i) \approx \real(i)");
    checked(r"false || 1 \approx 2 && true");
}

#[test]
fn config_is_required_source_ordered_nonnegative_and_unique() {
    for body in [
        "@saria.assert 1 \\approx 1\n",
        "@saria.assert 1 \\approx 1\npragma saria.approx 1e-15\n",
        "pragma saria.approx -1e-15\n",
        "pragma saria.approx NaN\n",
        "pragma saria.approx1\n",
        "if (true) {\npragma saria.approx 1e-15\n}\n",
        "pragma saria.approx 1/10\n",
        "pragma saria.approx 1e-1025\n",
        "pragma saria.approx 0\npragma saria.approx 1\n",
        "pragma saria.approx 1\n@saria.assert true \\approx false\n",
        "pragma saria.approx 1\n@saria.assert |0> \\approx |1>\n",
        "pragma saria.approx 1\n@saria.assert |0><0| \\approx |00><00|\n",
        "pragma saria.approx 1\n@saria.assert 1 \\approx 2 == 3\n",
    ] {
        assert!(
            frontend::parse_str(&format!("OPENQASM 3; qubit q;\n{body}"), "bad-approx").is_err(),
            "{body}"
        );
    }
    frontend::parse_str(
        r"OPENQASM 3; qubit q;
pragma saria.approx 0
pragma saria.def close(x: real) -> bool = x \approx x
@saria.assert close(\real(1)) && (\avg_density(q) \approx |0><0|)
",
        "approx",
    )
    .unwrap();
}
