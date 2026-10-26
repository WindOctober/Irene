use iqir::*;

#[test]
fn arcsin_and_log_share_typed_certified_evaluation() {
    for (name, op, input, expected) in [
        (
            "arcsin",
            FloatUnary::Asin,
            0.5f32,
            std::f32::consts::FRAC_PI_6,
        ),
        ("log", FloatUnary::Log, 2.0f32, std::f32::consts::LN_2),
    ] {
        let p = parse(&format!(
            "float[32] argument; float[64] result={name}(argument);"
        ));
        let StatementKind::ScalarDeclare {
            initializer: Some(e),
            ..
        } = &p.body.statements[1].kind
        else {
            panic!()
        };
        let ScalarExprKind::FloatCast(inner) = &e.kind.kind else {
            panic!()
        };
        assert!(
            matches!(inner.kind.kind, ScalarExprKind::FloatUnary { op: found, .. } if found == op)
        );
        assert_eq!(inner.ty, ScalarType::Float { width: 32 });
        assert_eq!(e.constant_value().unwrap(), None);
        assert_eq!(
            e.constant_value_with(&|_| Some(ScalarValue::Float32(input.to_bits())))
                .unwrap(),
            Some(ScalarValue::Float64((expected as f64).to_bits()))
        );
        let copied = AstIdGenerator::default().clone_scalar_expr(e);
        let mut ids = Vec::new();
        copied.visit_ids(&mut |id| ids.push(id.index()));
        ids.sort();
        ids.dedup();
        assert_eq!(ids.len(), 3);
        for input in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
            assert!(op.evaluate(ScalarValue::Float64(input.to_bits())).is_err());
        }
    }
    for x in [-0.0f64, 0.0] {
        assert_eq!(
            FloatUnary::Asin
                .evaluate(ScalarValue::Float64(x.to_bits()))
                .unwrap(),
            ScalarValue::Float64(x.to_bits())
        );
        assert!(
            FloatUnary::Log
                .evaluate(ScalarValue::Float64(x.to_bits()))
                .is_err()
        );
    }
    for x in [-2.0f64, 2.0] {
        assert!(
            FloatUnary::Asin
                .evaluate(ScalarValue::Float64(x.to_bits()))
                .is_err()
        );
    }
    assert!(
        FloatUnary::Log
            .evaluate(ScalarValue::Float64((-1.0f64).to_bits()))
            .is_err()
    );
    assert_eq!(
        FloatUnary::Log
            .evaluate(ScalarValue::Float64(1.0f64.to_bits()))
            .unwrap(),
        ScalarValue::Float64(0)
    );
    parse("float[64] p; float[64] theta=arcsin(sqrt(p)); float[64] radius=sqrt(log(p)/2.0);");
}

fn parse(body: &str) -> Program {
    let p = frontend::parse_str(&format!("OPENQASM 3; {body}"), "float.qasm").unwrap();
    let mut ids = vec![];
    p.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort();
    assert_eq!(ids, (0..p.ast_id_bound()).collect::<Vec<_>>());
    p
}

#[test]
fn runtime_math_and_integer_conversion_preserve_nodes_and_ids() {
    let p = parse(
        "float[64] x; float[64] a=floor(x); float[64] b=ceiling(x); float[64] c=sqrt(x); int[64] n=int[64](floor(x));",
    );
    let mut ids = AstIdGenerator::default();
    for (i, op) in [FloatUnary::Floor, FloatUnary::Ceiling, FloatUnary::Sqrt]
        .into_iter()
        .enumerate()
    {
        let StatementKind::ScalarDeclare {
            initializer: Some(e),
            ..
        } = &p.body.statements[i + 1].kind
        else {
            panic!()
        };
        assert!(
            matches!(&e.kind.kind, ScalarExprKind::FloatUnary { op: found, argument } if *found == op && matches!(argument.kind.kind, ScalarExprKind::Read(_)))
        );
        let copied = ids.clone_scalar_expr(e);
        let mut visited = vec![];
        copied.visit_ids(&mut |id| visited.push(id));
        assert_eq!(visited.len(), 2);
        assert_ne!(visited[0], visited[1]);
    }
    let StatementKind::ScalarDeclare {
        initializer: Some(e),
        ..
    } = &p.body.statements[4].kind
    else {
        panic!()
    };
    assert!(matches!(e.kind.kind, ScalarExprKind::IntFromFloat(_)));
    parse("float[32] x; float[64] y=floor(x); float[64] z=float[64](int[8](ceiling(x)));");
}

#[test]
fn arccos_is_retained_and_certifiably_folded_at_each_precision() {
    let p = parse("float[32] argument; float[64] result=arccos(argument);");
    let StatementKind::ScalarDeclare {
        initializer: Some(e),
        ..
    } = &p.body.statements[1].kind
    else {
        panic!()
    };
    let ScalarExprKind::FloatCast(inner) = &e.kind.kind else {
        panic!("{e:?}")
    };
    assert_eq!(inner.ty, ScalarType::Float { width: 32 });
    assert!(matches!(
        inner.kind.kind,
        ScalarExprKind::FloatUnary {
            op: FloatUnary::Acos,
            ..
        }
    ));
    assert_eq!(e.constant_value().unwrap(), None);
    let result = e
        .constant_value_with(&|_| Some(ScalarValue::Float32(0)))
        .unwrap()
        .unwrap();
    assert_eq!(
        result,
        ScalarValue::Float64((std::f32::consts::FRAC_PI_2 as f64).to_bits())
    );
    assert_eq!(
        FloatUnary::Acos
            .evaluate(ScalarValue::Float64(1.0f64.to_bits()))
            .unwrap(),
        ScalarValue::Float64(0)
    );
    for value in [-2.0f64, 2.0, f64::NAN, f64::INFINITY] {
        assert!(
            FloatUnary::Acos
                .evaluate(ScalarValue::Float64(value.to_bits()))
                .is_err()
        );
    }
    // Cloning must refresh the IDs inside the new operation as well.
    let cloned = AstIdGenerator::default().clone_scalar_expr(e);
    let mut seen = vec![];
    cloned.visit_ids(&mut |id| seen.push(id.index()));
    seen.sort();
    seen.dedup();
    assert_eq!(seen.len(), 3);
}

#[test]
fn constant_math_uses_the_same_ieee_operations() {
    for (op, x, expected) in [
        (FloatUnary::Floor, -1.25f64, -2.0f64),
        (FloatUnary::Ceiling, -1.25, -1.0),
        (FloatUnary::Sqrt, 4.0, 2.0),
        (FloatUnary::Floor, -0.0, -0.0),
        (FloatUnary::Ceiling, -0.25, -0.0),
        (FloatUnary::Sqrt, -0.0, -0.0),
    ] {
        assert_eq!(
            op.evaluate(ScalarValue::Float64(x.to_bits())).unwrap(),
            ScalarValue::Float64(expected.to_bits())
        );
        assert_eq!(
            op.evaluate(ScalarValue::Float32((x as f32).to_bits()))
                .unwrap(),
            ScalarValue::Float32((expected as f32).to_bits())
        );
    }
    assert!(
        FloatUnary::Sqrt
            .evaluate(ScalarValue::Float64((-1.0f64).to_bits()))
            .unwrap()
            .as_float()
            .unwrap()
            .is_nan()
    );
}

#[test]
fn sin_retains_runtime_nodes_and_certified_operand_precision() {
    let p = parse("float[32] argument; float[64] result=sin(argument);");
    let StatementKind::ScalarDeclare {
        initializer: Some(e),
        ..
    } = &p.body.statements[1].kind
    else {
        panic!()
    };
    let ScalarExprKind::FloatCast(inner) = &e.kind.kind else {
        panic!("{e:?}")
    };
    assert!(matches!(
        inner.kind.kind,
        ScalarExprKind::FloatUnary {
            op: FloatUnary::Sin,
            ..
        }
    ));
    assert_eq!(e.constant_value().unwrap(), None);
    assert_eq!(
        e.constant_value_with(&|_| Some(ScalarValue::Float32(1.0f32.to_bits())))
            .unwrap(),
        Some(ScalarValue::Float64(
            (f32::from_bits(0x3f576aa4) as f64).to_bits()
        ))
    );
    for value in [0.0f64, -0.0] {
        assert_eq!(
            FloatUnary::Sin
                .evaluate(ScalarValue::Float64(value.to_bits()))
                .unwrap(),
            ScalarValue::Float64(value.to_bits())
        );
    }
    for value in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert!(
            FloatUnary::Sin
                .evaluate(ScalarValue::Float64(value.to_bits()))
                .is_err()
        );
    }
    let p = parse("bool b; float[64] a=0.0; if(b){a=-0.0;} float[64] result=sin(a);");
    assert!(format!("{p:?}").contains("Sin"));
}

#[test]
fn integer_cast_is_truncation_not_saturation_or_floor() {
    let signed = ScalarType::Int {
        width: 8,
        signed: true,
    };
    let unsigned = ScalarType::Int {
        width: 8,
        signed: false,
    };
    for (x, ty, expected) in [
        (-1.75f64, signed, -1),
        (127.9, signed, 127),
        (-128.9, signed, -128),
        (-0.75, unsigned, 0),
        (255.9, unsigned, 255),
    ] {
        assert_eq!(
            ScalarValue::Float64(x.to_bits()).to_integer(ty).unwrap(),
            ScalarValue::Integer(expected)
        );
    }
    for x in [128.0f64, -129.0, f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert!(
            ScalarValue::Float64(x.to_bits())
                .to_integer(signed)
                .is_err()
        );
    }
    assert!(
        ScalarValue::Float64((u64::MAX as f64).to_bits())
            .to_integer(ScalarType::Int {
                width: 64,
                signed: false
            })
            .is_err()
    );
}

#[test]
fn unsupported_runtime_transcendentals_and_invalid_constants_stay_rejected() {
    for body in [
        "float[64] x; float[64] y=cos(x);",
        "float[64] y=arcsin(2.0);",
        "float[64] y=log(0.0);",
        "float[64] y=log(-1.0);",
        "float[64] y=sqrt(-1.0);",
        "int[8] n=int[8](floor(128.0));",
    ] {
        assert!(frontend::parse_str(&format!("OPENQASM 3; {body}"), "bad.qasm").is_err());
    }
}
