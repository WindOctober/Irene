use iqir::annotation::{
    AnnotationKind, AnnotationPayload, BinaryOp, MathFunction, SourceSpan, SpecExpr,
    TerminationKind, UnaryOp, parse_annotation, parse_expression,
};

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
fn factorial_power_negation_and_exact_numbers() {
    assert_eq!(
        parse_expression("5!").unwrap(),
        unary(UnaryOp::Factorial, number(5))
    );
    assert_eq!(
        parse_expression("n!").unwrap(),
        unary(UnaryOp::Factorial, SpecExpr::Name("n".into()))
    );
    assert_eq!(
        parse_expression("0.5").unwrap(),
        parse_expression("5e-1").unwrap()
    );
    assert_eq!(
        parse_expression("-2^2").unwrap(),
        unary(
            UnaryOp::Neg,
            SpecExpr::Binary {
                op: BinaryOp::Pow,
                left: Box::new(number(2)),
                right: Box::new(number(2)),
            }
        )
    );
    assert_eq!(
        parse_expression("2^3^4").unwrap(),
        SpecExpr::Binary {
            op: BinaryOp::Pow,
            left: Box::new(number(2)),
            right: Box::new(SpecExpr::Binary {
                op: BinaryOp::Pow,
                left: Box::new(number(3)),
                right: Box::new(number(4)),
            }),
        }
    );
    assert!(matches!(
        parse_expression("n! != 0 && !stop").unwrap(),
        SpecExpr::Binary {
            op: BinaryOp::And,
            ..
        }
    ));
    assert!(matches!(
        parse_expression("[[1, 0], [0, 1]]").unwrap(),
        SpecExpr::List(_)
    ));
    assert!(matches!(
        parse_expression("\\cosh(1 / (2 * n)!)").unwrap(),
        SpecExpr::Call {
            function: MathFunction::Cosh,
            ..
        }
    ));
}

#[test]
fn rejects_malformed_unknown_and_over_budget_expressions() {
    for source in [
        "",
        "n! garbage",
        "\\cosh()",
        "\\trace_distance(1)",
        "1e",
        "1.2.3",
        "1e1000000000",
        "q[]",
        "(n",
        "0 <= n <= 5",
        "[1,]",
        "1;",
        "1 // comment",
    ] {
        assert!(parse_expression(source).is_err(), "accepted {source}");
    }
    assert!(parse_expression(&format!("{}1{}", "(".repeat(70), ")".repeat(70))).is_err());
    assert!(parse_expression(&format!("1{}", "!".repeat(1100))).is_err());
}

#[test]
fn annotation_kind_and_payload_are_typed() {
    let span = SourceSpan {
        source: "test.qasm".into(),
        start: 10,
        end: 46,
    };
    let a = parse_annotation("@saria.terminates almost_sure", span.clone()).unwrap();
    assert_eq!(a.kind, AnnotationKind::Terminates);
    assert_eq!(
        a.payload,
        AnnotationPayload::Termination(TerminationKind::AlmostSure)
    );
    assert_eq!(a.span, span);
    for text in [
        "@saria.invaraint true",
        "@other.foo true",
        "@saria.terminates n!",
        "@saria.requires",
    ] {
        assert!(parse_annotation(text, span.clone()).is_err());
    }
}

#[test]
fn factorial_comparison_and_binders_keep_structure() {
    assert_eq!(
        parse_expression("n! >= x").unwrap(),
        SpecExpr::Binary {
            op: BinaryOp::Ge,
            left: Box::new(unary(UnaryOp::Factorial, SpecExpr::Name("n".into()))),
            right: Box::new(SpecExpr::Name("x".into())),
        }
    );
    for (text, expected, inclusive) in [
        (
            "\\sum(j in 0..n, 1/(2*j)!)",
            iqir::annotation::BinderKind::Sum,
            false,
        ),
        (
            "\\product(j in 1..=n, j)",
            iqir::annotation::BinderKind::Product,
            true,
        ),
        (
            "\\forall j in 0..n; j >= 0",
            iqir::annotation::BinderKind::Forall,
            false,
        ),
        (
            "\\exists j in 0..\\inf; j > n",
            iqir::annotation::BinderKind::Exists,
            false,
        ),
        (
            "\\sup(x: float in 0..=1, x)",
            iqir::annotation::BinderKind::Sup,
            true,
        ),
        (
            "\\infimum(x: float in 0..1, x)",
            iqir::annotation::BinderKind::Inf,
            false,
        ),
    ] {
        let SpecExpr::Binder {
            kind,
            inclusive: found,
            id,
            ..
        } = parse_expression(text).unwrap()
        else {
            panic!("{text}");
        };
        assert_eq!(kind, expected);
        assert_eq!(found, inclusive);
        assert_eq!(
            id, None,
            "syntax parsing must not invent resolved variable IDs"
        );
    }
}

#[test]
fn helper_signature_is_parsed_without_resolving_or_executing_it() {
    use iqir::annotation::{SpecType, parse_function};
    let text = "pragma saria.def remaining(n: int) -> float = \\cosh(1) - \\sum(j in 0..n, a(j))";
    let span = SourceSpan {
        source: "helpers.qasm".into(),
        start: 0,
        end: text.len(),
    };
    let f = parse_function(text, span.clone()).unwrap();
    assert_eq!(f.name, "remaining");
    assert_eq!(f.parameters.len(), 1);
    assert_eq!(f.parameters[0].name, "n");
    assert_eq!(f.parameters[0].ty, SpecType::Int(None));
    assert_eq!(f.result, SpecType::Float(None));
    assert_eq!(f.span, span);
    assert!(matches!(
        f.body,
        SpecExpr::Binary {
            op: BinaryOp::Sub,
            ..
        }
    ));
    assert!(matches!(
        parse_expression("unknown(1)").unwrap(),
        SpecExpr::NamedCall { .. }
    ));
}

#[test]
fn benchmark_formula_syntax_and_logical_precedence() {
    for text in [
        "k >= 5 ? 1 : a(k)/(\\cosh(1)-\\sum(j in 0..k, a(j)))",
        "(1-p^n)/((1-p)*p^n)",
        "(-1)^(m+1)*\\binom(1/2,m)",
        "\\sum(k in 0..\\inf, (1/4)*(5/8)^(k-1))",
        "\\probability(true) <= 1 && \\expectation(2) < \\inf",
        "n^(-1/2)",
        "[1,2,3][0] == 1",
    ] {
        parse_expression(text).unwrap_or_else(|e| panic!("{text}: {e}"));
    }
    let SpecExpr::Binary { op, left, right } = parse_expression("a || b && c => d => e").unwrap()
    else {
        panic!()
    };
    assert_eq!(op, BinaryOp::Implies);
    assert!(matches!(
        *left,
        SpecExpr::Binary {
            op: BinaryOp::Or,
            ..
        }
    ));
    assert!(matches!(
        *right,
        SpecExpr::Binary {
            op: BinaryOp::Implies,
            ..
        }
    ));
}

#[test]
fn quantifier_scope_extends_right_and_parentheses_can_end_it() {
    for (compact, explicit) in [
        (
            r"\forall i in 0..n; \exists j in i..n; j >= i",
            r"\forall i in 0..n; (\exists j in i..n; (j >= i))",
        ),
        (
            r"\forall i in 0..n; a || b && c => d",
            r"\forall i in 0..n; ((a || (b && c)) => d)",
        ),
        (
            r"a => \forall i in 0..n; p(i) && q(i)",
            r"a => (\forall i in 0..n; (p(i) && q(i)))",
        ),
        (
            r"\forall i in 0..n; a ? p(i) : q(i)",
            r"\forall i in 0..n; (a ? p(i) : q(i))",
        ),
        (
            r"a ? \forall i in 0..n; p(i) : \exists j in 0..n; q(j)",
            r"a ? (\forall i in 0..n; p(i)) : (\exists j in 0..n; q(j))",
        ),
        (
            r"f(\forall i in 0..n; p(i), \exists j in 0..n; q(j))",
            r"f((\forall i in 0..n; p(i)), (\exists j in 0..n; q(j)))",
        ),
        (
            r"\sum(i in 0..n, (\exists j in 0..i; j > 0) ? 1 : 0)",
            r"\sum(i in 0..n, ((\exists j in 0..i; j > 0) ? 1 : 0))",
        ),
    ] {
        assert_eq!(
            parse_expression(compact).unwrap(),
            parse_expression(explicit).unwrap(),
            "{compact}"
        );
    }
    let wide = parse_expression(r"\forall i in 0..n; p(i) && q(n)").unwrap();
    let narrow = parse_expression(r"(\forall i in 0..n; p(i)) && q(n)").unwrap();
    assert!(matches!(wide, SpecExpr::Binder { .. }));
    assert!(matches!(
        narrow,
        SpecExpr::Binary {
            op: BinaryOp::And,
            ..
        }
    ));
    assert_ne!(wide, narrow);
}

#[test]
fn binder_spellings_separators_and_unparenthesized_depth_are_checked() {
    for bad in [
        "forall(i in 0..n, true)",
        "exists(i in 0..n, true)",
        "sum(i in 0..n, i)",
        "product(i in 0..n, i)",
        "sup(i in 0..n, i)",
        "infimum(i in 0..n, i)",
        r"\forall(i in 0..n, true)",
        r"\exists(i in 0..n, true)",
        r"\forall i in 0..n, true",
        r"\forall i in 0..n; ",
        r"\forall i in 0..n; true;",
        r"\forall i: int; i == i",
        r"\forallx i in 0..n; true",
        r"\forall_i i in 0..n; true",
        r"\forallλ i in 0..n; true",
        r"\existsx i in 0..n; true",
        r"\sumx(i in 0..n, i)",
        r"\sum i in 0..n; i",
        r"\sum(i in 0..n; i)",
        r"\unknown(i in 0..n, i)",
    ] {
        assert!(parse_expression(bad).is_err(), "accepted {bad}");
    }
    let nested = format!("{}true", r"\forall i in 0..1; ".repeat(20));
    parse_expression(&nested).unwrap();
    let excessive = format!("{}true", r"\forall i in 0..1; ".repeat(100));
    let error = parse_expression(&excessive).unwrap_err();
    assert!(error.message.contains("complexity budget"));
    let bad = r"\forall i in 0..n; i + )";
    assert_eq!(parse_expression(bad).unwrap_err().offset, bad.len() - 1);
}

#[test]
fn builtin_functions_and_constants_require_backslashes() {
    for (name, args) in [
        ("sqrt", "2"),
        ("abs", "1"),
        ("exp", "1"),
        ("log", "1"),
        ("ln", "1"),
        ("sin", "1"),
        ("cos", "1"),
        ("tan", "1"),
        ("sinh", "1"),
        ("cosh", "1"),
        ("tanh", "1"),
        ("asin", "1"),
        ("acos", "1"),
        ("atan", "1"),
        ("floor", "1"),
        ("ceil", "1"),
        ("binom", "2,1"),
        ("min", "1,2"),
        ("max", "1,2"),
        ("conj", "1"),
        ("re", "1"),
        ("im", "1"),
        ("adjoint", "|0>"),
        ("expectation", "1"),
        ("probability", "true"),
        ("diag", "1,2"),
        ("trace", "1"),
        ("normalize", "1"),
        ("avg_density", "q"),
        ("trace_distance", "1,2"),
    ] {
        assert!(matches!(
            parse_expression(&format!(r"\{name}({args})")).unwrap(),
            SpecExpr::Call { .. }
        ));
        assert!(
            matches!(parse_expression(&format!("{name}({args})")).unwrap(),
            SpecExpr::NamedCall { name: found, .. } if found == name)
        );
    }
    for (name, constant) in [
        ("pi", iqir::NumericConstant::Pi),
        ("tau", iqir::NumericConstant::Tau),
        ("euler", iqir::NumericConstant::Euler),
    ] {
        assert_eq!(
            parse_expression(&format!(r"\{name}")).unwrap(),
            SpecExpr::Constant(constant)
        );
        assert_eq!(parse_expression(name).unwrap(), SpecExpr::Name(name.into()));
    }
    assert_eq!(parse_expression(r"\inf").unwrap(), SpecExpr::Infinity);
    assert_eq!(
        parse_expression("inf").unwrap(),
        SpecExpr::Name("inf".into())
    );
    for bad in [
        r"\sqrt()",
        r"\sqrt(1,2)",
        r"\custom(1)",
        r"\sqrtx(1)",
        r"\ sqrt(1)",
        r"\pi(1)",
        r"\pix",
    ] {
        assert!(parse_expression(bad).is_err(), "accepted {bad}");
    }
}
