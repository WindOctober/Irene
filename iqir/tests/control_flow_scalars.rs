use iqir::*;
use std::collections::{BTreeMap, BTreeSet};

fn parse(body: &str) -> Program {
    let p = frontend::parse_str(
        &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
        "runtime.qasm",
    )
    .unwrap();
    let mut ids = Vec::new();
    p.visit_ast_ids(|id| ids.push(id.index()));
    let unique: BTreeSet<_> = ids.iter().copied().collect();
    assert_eq!(ids.len(), unique.len(), "shared AST identity");
    assert_eq!(
        unique.into_iter().collect::<Vec<_>>(),
        (0..p.ast_id_bound()).collect::<Vec<_>>()
    );
    p
}

#[test]
fn preserves_nested_and_single_statement_while_with_fresh_local_storage() {
    let p = parse(
        "qubit q; bit flag; while (flag) { int[8] local = 0; while (local < 2) { local += 1; } flag = measure q; } while (false) reset q;",
    );
    assert_eq!(p.body.statements.len(), 2);
    let StatementKind::While { condition, body } = &p.body.statements[0].kind else {
        panic!()
    };
    assert!(matches!(condition.kind, ClassicalExprKind::Bit(_)));
    assert!(matches!(
        body.statements[0].kind,
        StatementKind::ScalarDeclare {
            ty: ScalarType::Int { width: 8, .. },
            ..
        }
    ));
    assert!(matches!(
        body.statements[1].kind,
        StatementKind::While { .. }
    ));
    assert!(matches!(
        body.statements[2].kind,
        StatementKind::Measure { .. }
    ));
    let StatementKind::While { body, .. } = &p.body.statements[1].kind else {
        panic!()
    };
    assert!(matches!(body.statements[0].kind, StatementKind::Reset(_)));
}

#[test]
fn loop_body_names_do_not_escape_or_capture_the_guard() {
    let p = parse("int[8] n=1; while(n>0) { int[8] n=2; n-=1; } n=0;");
    let StatementKind::ScalarDeclare { id: outer, .. } = p.body.statements[0].kind else {
        panic!()
    };
    let StatementKind::While { condition, body } = &p.body.statements[1].kind else {
        panic!()
    };
    let ClassicalExprKind::ScalarCompare { left, .. } = &condition.kind else {
        panic!()
    };
    assert_eq!(left.kind.kind, ScalarExprKind::Read(outer));
    let StatementKind::ScalarDeclare { id: inner, .. } = body.statements[0].kind else {
        panic!()
    };
    assert_ne!(inner, outer);
    for body in [
        "while(false) { int[8] x=1; } x=2;",
        "while(false) { bit x; } if(x) {}",
        "while(false) { int[8] n=0; int[8] n=1; }",
    ] {
        assert!(frontend::parse_str(&format!("OPENQASM 3; {body}"), "scope.qasm").is_err());
    }
}

#[test]
fn no_loop_entry_or_exit_constant_facts_are_reused_for_gate_powers() {
    for body in [
        "bit[1] b=\"1\"; qubit q; while(b[0]) { pow(uint[1](b)) @ x q; b[0]=measure q; }",
        "bit[1] b=\"1\"; qubit q; while(b[0]) { b[0]=measure q; } pow(uint[1](b)) @ x q;",
    ] {
        let error = frontend::parse_str(
            &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
            "pow.qasm",
        )
        .unwrap_err();
        assert!(error.to_string().contains("power"), "{error}");
    }
    parse("bit[1] b; qubit q; while(true) { b=\"1\"; pow(uint[1](b)) @ x q; b[0]=measure q; }");
}

#[test]
fn scalar_widths_signedness_and_uninitialized_values_are_retained() {
    let p = parse(
        "int[1] a=-1; int[64] b=-9223372036854775808; int[64] c=9223372036854775807; int d; float f; float[32] g;",
    );
    let widths = p
        .body
        .statements
        .iter()
        .map(|s| match &s.kind {
            StatementKind::ScalarDeclare { ty, .. } => ty.width(),
            _ => panic!(),
        })
        .collect::<Vec<_>>();
    assert_eq!(widths, [1, 64, 64, 32, 64, 32]);
    assert!(matches!(
        p.body.statements[3].kind,
        StatementKind::ScalarDeclare {
            initializer: None,
            ty: ScalarType::Int { .. },
            explicit_width: false,
            ..
        }
    ));
    assert!(matches!(
        p.body.statements[4].kind,
        StatementKind::ScalarDeclare {
            initializer: None,
            ty: ScalarType::Float { .. },
            explicit_width: false,
            ..
        }
    ));
}

// A deliberately small test-only evaluator. It consumes the actual emitted
// typed expression trees, checking ordering/rounding rather than source text.
#[derive(Debug, Clone, Copy, PartialEq)]
enum Value {
    Integer(i128),
    Float(f64),
}
fn value(e: &ScalarExpr, store: &BTreeMap<SymbolId, Value>) -> Value {
    use ScalarArithmetic as A;
    use ScalarExprKind as E;
    let v = match &e.kind.kind {
        E::Integer(n) => Value::Integer(*n),
        E::Float32(n) => Value::Float(f32::from_bits(*n) as f64),
        E::Float64(n) => Value::Float(f64::from_bits(*n)),
        E::Read(id) => store[id],
        E::FloatCast(a) => value(a, store),
        E::Neg(a) => match value(a, store) {
            Value::Integer(n) => Value::Integer(-n),
            Value::Float(n) => Value::Float(-n),
        },
        E::Binary { op, left, right } => match (value(left, store), value(right, store)) {
            (Value::Integer(a), Value::Integer(b)) => Value::Integer(match op {
                A::Add => a + b,
                A::Sub => a - b,
                A::Mul => a * b,
                A::Div => a / b,
                A::Rem => a % b,
            }),
            (Value::Float(a), Value::Float(b)) => Value::Float(match op {
                A::Add => a + b,
                A::Sub => a - b,
                A::Mul => a * b,
                A::Div => a / b,
                _ => panic!(),
            }),
            _ => panic!("mixed operand types"),
        },
    };
    match (e.ty, v) {
        (ScalarType::Float { width: 32, .. }, Value::Float(f)) => Value::Float((f as f32) as f64),
        (ScalarType::Int { width, .. }, Value::Integer(n)) => {
            assert!(
                (-(1_i128 << (width - 1))..(1_i128 << (width - 1))).contains(&n),
                "signed overflow"
            );
            v
        }
        _ => v,
    }
}
fn bool_value(
    e: &ClassicalExpr,
    store: &BTreeMap<SymbolId, Value>,
    bits: &BTreeMap<ClassicalBit, bool>,
) -> bool {
    use ClassicalExprKind as E;
    use ScalarComparison as C;
    match &e.kind {
        E::Bool(v) => *v,
        E::Bit(b) => bits[b],
        E::Not(a) => !bool_value(a, store, bits),
        E::And(a, b) => bool_value(a, store, bits) && bool_value(b, store, bits),
        E::Or(a, b) => bool_value(a, store, bits) || bool_value(b, store, bits),
        E::Eq(a, b) => bool_value(a, store, bits) == bool_value(b, store, bits),
        E::Xor(a, b) => bool_value(a, store, bits) ^ bool_value(b, store, bits),
        E::ScalarCompare { op, left, right } => {
            let order = match (value(left, store), value(right, store)) {
                (Value::Integer(a), Value::Integer(b)) => a.partial_cmp(&b),
                (Value::Float(a), Value::Float(b)) => a.partial_cmp(&b),
                _ => panic!(),
            };
            use std::cmp::Ordering::{Equal, Greater, Less};
            match op {
                C::Eq => order == Some(Equal),
                C::Ne => order != Some(Equal),
                C::Lt => order == Some(Less),
                C::Le => matches!(order, Some(Less | Equal)),
                C::Gt => order == Some(Greater),
                C::Ge => matches!(order, Some(Greater | Equal)),
            }
        }
    }
}
fn execute(
    block: &Block,
    store: &mut BTreeMap<SymbolId, Value>,
    fuel: &mut usize,
    keep_globals: bool,
) {
    let mut locals = Vec::new();
    for s in &block.statements {
        assert!(*fuel > 0);
        *fuel -= 1;
        match &s.kind {
            StatementKind::ScalarDeclare {
                id, initializer, ..
            } => {
                locals.push(*id);
                store.remove(id);
                if let Some(e) = initializer {
                    store.insert(*id, value(e, store));
                }
            }
            StatementKind::ScalarAssign { target, value: e } => {
                store.insert(*target, value(e, store));
            }
            StatementKind::While { condition, body } => {
                while bool_value(condition, store, &BTreeMap::new()) {
                    assert!(*fuel > 0);
                    *fuel -= 1;
                    execute(body, store, fuel, false);
                }
            }
            StatementKind::If {
                condition,
                then_branch,
                else_branch,
            } => execute(
                if bool_value(condition, store, &BTreeMap::new()) {
                    then_branch
                } else {
                    else_branch
                },
                store,
                fuel,
                false,
            ),
            _ => panic!("test expects classical structured IR"),
        }
    }
    if !keep_globals {
        for id in locals {
            store.remove(&id);
        }
    }
}
fn final_value(source: &str, name: &str) -> Value {
    let p = parse(source);
    let id = p
        .body
        .statements
        .iter()
        .find_map(|s| match &s.kind {
            StatementKind::ScalarDeclare { id, name: n, .. } if n == name => Some(*id),
            _ => None,
        })
        .unwrap();
    let mut store = BTreeMap::new();
    execute(&p.body, &mut store, &mut 10000, true);
    store[&id]
}

#[test]
fn arithmetic_and_while_execute_from_ir_with_correct_signed_comparisons() {
    assert_eq!(
        final_value("int[8] n=-3; while(n<2) {n+=1;}", "n"),
        Value::Integer(2)
    );
    assert_eq!(
        final_value("int[8] n=7; n+=1; n-=1;", "n"),
        Value::Integer(7)
    );
    assert_eq!(
        final_value("int[16] n=-7; n/=2; n*=3; n%=4;", "n"),
        Value::Integer(-1)
    );
    assert_eq!(
        final_value(
            "int[8] n=0; while(n<3) {int[8] local=0; local+=1; n+=local;}",
            "n"
        ),
        Value::Integer(3)
    );
}

#[test]
fn float_widths_preserve_stepwise_rounding_signed_zero_and_subnormals() {
    assert_eq!(
        final_value("int[16] n=(200+100)/2;", "n"),
        Value::Integer(150)
    );
    assert_eq!(final_value("float[64] f=1/2;", "f"), Value::Float(0.0));
    assert_eq!(
        final_value(
            "float[32] val=16777216.0; float[32] delta=(val+1.0)-val;",
            "delta"
        ),
        Value::Float(1.0)
    );
    assert_eq!(
        final_value(
            "float[32] val=16777216.0; float[64] wide=val; wide+=1.0;",
            "wide"
        ),
        Value::Float(16777217.0)
    );
    assert_eq!(
        final_value(
            "float[32] val=16777216.0; float[64] wide=16777217.0; int[8] result=0; if(val < wide) {result=1;}",
            "result"
        ),
        Value::Integer(1)
    );
    assert_eq!(
        final_value(
            "float[32] val=16777216.0; float[32] one=1.0; float[32] delta=(val+one)-val;",
            "delta"
        ),
        Value::Float(0.0)
    );
    assert_eq!(
        final_value(
            "float[64] val=16777216.0; float[64] delta=(val+1.0)-val;",
            "delta"
        ),
        Value::Float(1.0)
    );
    assert_eq!(
        final_value("float[64] f=1.0; while(f>0.125) {f*=0.5;}", "f"),
        Value::Float(0.125)
    );
    assert_eq!(
        final_value("float[32] f=1.0000000596046448;", "f"),
        Value::Float(1.0)
    );
    let Value::Float(zero) = final_value("float[64] zero=-0.0;", "zero") else {
        panic!()
    };
    assert_eq!(zero.to_bits(), (-0.0_f64).to_bits());
    assert_eq!(
        final_value("float[64] f=5e-324;", "f"),
        Value::Float(f64::from_bits(1))
    );
}

#[test]
fn register_literal_comparisons_read_all_bits_in_little_endian_order() {
    let p = parse("bit[3] c; while(c==5) {} while(4<c) {}");
    for n in 0..8 {
        let bits = (0..3)
            .map(|index| {
                (
                    ClassicalBit {
                        register: p.classical_registers[0].id,
                        index,
                    },
                    n & (1 << index) != 0,
                )
            })
            .collect();
        for (index, expected) in [n == 5, n > 4].into_iter().enumerate() {
            let StatementKind::While { condition, .. } = &p.body.statements[index].kind else {
                panic!()
            };
            assert_eq!(bool_value(condition, &BTreeMap::new(), &bits), expected);
        }
    }
}

#[test]
fn rejects_unsupported_or_ill_typed_scalar_forms_instead_of_erasing_them() {
    for body in [
        "int[0] n;",
        "const uint[16] inc=1; uint[8] n=255; n=(n+inc)/2;",
        "const uint[16] inc=1; uint[8] n=255; n=(n+(inc+0))/2;",
        "int[65] n;",
        "float[16] f;",
        "int[8] n=128;",
        "uint[8] n=-1;",
        "float[64] f=1e400;",
        "int[8] n=1.5;",
        "int[8] n=1; float[64] f=n;",
        "int[8] n=1; int[16] m=n;",
        "int[8] n=1; n[0]=0;",
        "while(true) {break;}",
        "while(true) {continue;}",
        "qubit q; int[8] n=0; rx(n) q;",
        "int[8] n=0; qubit[n] q;",
    ] {
        assert!(
            frontend::parse_str(
                &format!("OPENQASM 3; include \"stdgates.inc\"; {body}"),
                "negative.qasm"
            )
            .is_err(),
            "accepted: {body}"
        );
    }
}

#[test]
fn scalar_clone_allocates_distinct_ids_for_every_expression_node() {
    let p = parse("int[8] n=0; n=(n+1)*2;");
    let StatementKind::ScalarAssign { value, .. } = &p.body.statements[1].kind else {
        panic!()
    };
    let mut ids = AstIdGenerator::starting_at(p.ast_id_bound());
    let copy = ids.clone_scalar_expr(value);
    assert_eq!(value, &copy);
    let mut old = BTreeSet::new();
    value.visit_ids(&mut |id| {
        old.insert(id.index());
    });
    let mut new = BTreeSet::new();
    copy.visit_ids(&mut |id| {
        new.insert(id.index());
    });
    assert!(old.is_disjoint(&new));
    assert_eq!(old.len(), new.len());
}

#[test]
fn omitted_width_is_spelling_not_a_distinct_type() {
    assert_eq!(
        final_value("int n=1; int[32] m=n; n=m+1; m+=n;", "m"),
        Value::Integer(3)
    );
    assert_eq!(
        final_value("const int k=2; int[32] n=1; n+=k;", "n"),
        Value::Integer(3)
    );
    assert_eq!(
        final_value("const int[32] k=2; int n=1; n=n+k;", "n"),
        Value::Integer(3)
    );
    assert_eq!(
        final_value("float f=1.0; float[64] g=f; f+=g;", "f"),
        Value::Float(2.0)
    );
    let p = parse("int a; int[32] b;");
    let types: Vec<_> = p
        .body
        .statements
        .iter()
        .map(|s| match s.kind {
            StatementKind::ScalarDeclare {
                ty, explicit_width, ..
            } => (ty, explicit_width),
            _ => panic!(),
        })
        .collect();
    assert_eq!(types[0].0, types[1].0);
    assert_eq!((types[0].1, types[1].1), (false, true));
}

#[test]
fn constants_and_variables_share_float_promotion_and_rounding() {
    for (ty, init, rhs, expression, expected) in [
        ("float[32]", "16777216.0", "1.0", "(a+b)-a", 0.0),
        ("float[64]", "16777216.0", "1.0", "(a+b)-a", 1.0),
        ("float[32]", "16777216.0", "1.0", "(a+1.0)-a", 1.0),
        ("float[32]", "16777216.0", "1.0", "float[32](a+1.0)-a", 0.0),
        ("float[32]", "16777216.0", "1.0", "float[64](a)+b-a", 1.0),
        ("float[32]", "-0.0", "1.0", "a*b", -0.0),
        ("float[64]", "5e-324", "1.0", "a*b", f64::from_bits(1)),
    ] {
        for qualifier in ["", "const "] {
            let source = format!(
                "{qualifier}{ty} a={init}; {qualifier}{ty} b={rhs}; {qualifier}{ty} result={expression}; {ty} out=result;"
            );
            let Value::Float(actual) = final_value(&source, "out") else {
                panic!()
            };
            assert_eq!(actual.to_bits(), expected.to_bits(), "{source}");
        }
    }
}

#[test]
fn closed_expressions_use_the_production_constant_evaluator() {
    for source in [
        "float[32] f=(16777216.0+1.0)-16777216.0;",
        "int[8] n=(200+100)/2-100;",
    ] {
        let p = parse(source);
        let StatementKind::ScalarDeclare {
            initializer: Some(expr),
            ..
        } = &p.body.statements[0].kind
        else {
            panic!()
        };
        let expected = value(expr, &BTreeMap::new());
        let actual = expr.constant_value().unwrap().unwrap();
        match (expected, actual) {
            (Value::Integer(a), ScalarValue::Integer(b)) => assert_eq!(a, b),
            (Value::Float(a), b) => assert_eq!(a.to_bits(), b.as_float().unwrap().to_bits()),
            _ => panic!(),
        }
    }
}

#[test]
fn const_qualification_is_not_inferred_from_known_initializers() {
    for source in [
        "int n=3; const int k=n;",
        "float f=1.0; const float c=f;",
        "int n=3; qubit[n] q;",
        "const int n=3; n=2;",
        "const float f=1.0; f+=1.0;",
        "for int n in [1:2] {const int k=n;}",
        "for int n in [1:2] {n=0;}",
        "const int n=n;",
    ] {
        assert!(
            frontend::parse_str(&format!("OPENQASM 3; {source}"), "const.qasm").is_err(),
            "{source}"
        );
    }
    parse("const uint[8] n=3; qubit[n] q;");
    // A self-read in a variable initializer remains a read of its own
    // uninitialized storage; shadowing must not capture the outer value.
    let p = parse("int n=1; if(true) {int n=n;}");
    let StatementKind::If { then_branch, .. } = &p.body.statements[1].kind else {
        panic!()
    };
    let StatementKind::ScalarDeclare {
        id,
        initializer: Some(expr),
        ..
    } = &then_branch.statements[0].kind
    else {
        panic!()
    };
    assert_eq!(expr.kind.kind, ScalarExprKind::Read(*id));
    assert_eq!(expr.constant_value().unwrap(), None);
}

#[test]
fn scalar_constants_can_feed_existing_boolean_and_gate_paths() {
    let p = parse(
        "const float[32] a=1.0; const float[64] b=2.0; const bool less=a<b; bit flag=less; qubit q; rx(a) q;",
    );
    assert!(matches!(
        p.body.statements[0].kind,
        StatementKind::Assign { .. }
    ));
    assert!(matches!(
        p.body.statements[1].kind,
        StatementKind::Apply { .. }
    ));
    let p = parse("if(1.0<2.0) {}");
    let StatementKind::If { condition, .. } = &p.body.statements[0].kind else {
        panic!()
    };
    assert_eq!(condition.kind, ClassicalExprKind::Bool(true));
}

#[test]
fn destination_width_does_not_hide_closed_integer_overflow() {
    for qualifier in ["", "const "] {
        for source in [
            format!("{qualifier}int[64] n=2147483647+1;"),
            format!("const int[8] a=127; {qualifier}int[16] n=a+1;"),
            format!("{qualifier}int[8] n=1/0;"),
            format!("const int[8] a=-128; {qualifier}int[8] n=a%-1;"),
        ] {
            assert!(
                frontend::parse_str(&format!("OPENQASM 3; {source}"), "overflow.qasm").is_err(),
                "{source}"
            );
        }
    }
}
