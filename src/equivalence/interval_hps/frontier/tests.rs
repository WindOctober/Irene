use super::*;
fn parse(n: usize, gates: &str) -> Program {
    crate::frontend::openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[{n}] q; {gates}"),
        "frontier",
    )
    .unwrap()
}
#[test]
fn shared_gate_lowering_encloses_independent_trace_values() {
    // Exact normalized squared traces for full operators, including spectators.
    for (body, r) in [
        ("h q[0];", 0),
        ("cx q[0],q[1];", 1),
        ("cz q[0],q[1];", 1),
        ("swap q[0],q[1];", 1),
        ("h q[0]; h q[0];", 4),
    ] {
        let p = parse(2, body);
        let report = identity_bound(&p).unwrap();
        let exact_lower =
            super::super::exact_trace_distance_lower(&BigRational::new(r.into(), 4.into()))
                .unwrap();
        let slack = BigRational::new(1.into(), 1_000_000_000_000i64.into());
        assert!(
            report.lower_bound.as_ref().unwrap() + slack >= exact_lower,
            "{body}: {report:?}"
        );
        if r == 4 {
            assert!(
                report.bound.unwrap() < BigRational::new(1.into(), 1_000_000_000_000i64.into())
            );
        }
    }
}
#[test]
fn inverse_random_mixed_circuits_and_relative_phase() {
    for seed in 0..6 {
        let body = format!(
            "h q[2]; cx q[2],q[0]; ry(0.{}23) q[1]; crz(0.371) q[0],q[2]; ccx q[1],q[0],q[2]; swap q[2],q[1]; t q[0];",
            seed + 1
        );
        let p = parse(3, &body);
        let (miter, _) = unitary_miter::miter(&p, &p).unwrap();
        let report = identity_bound(&miter).unwrap();
        assert!(report.bound.unwrap() < BigRational::new(1.into(), 1_000_000_000_000i64.into()));
        assert_eq!(
            report.lower_bound.unwrap(),
            BigRational::from_integer(0.into())
        );
    }
    let global = identity_bound(&parse(2, "rx(2*pi) q[0];")).unwrap();
    assert_eq!(
        global.lower_bound.unwrap(),
        BigRational::from_integer(0.into())
    );
    let relative = identity_bound(&parse(2, "crx(2*pi) q[0],q[1];")).unwrap();
    assert!(relative.lower_bound.unwrap() > BigRational::from_integer(1.into()));
}
#[test]
fn width_admission_includes_ten_but_not_eleven() {
    assert!(identity_bound(&parse(11, "h q[0];")).is_none());
    let report = identity_bound(&parse(10, "z q[9];")).unwrap();
    assert_eq!(report.max_width, 10);
    assert_eq!(
        report.lower_bound.unwrap(),
        BigRational::from_integer(2.into())
    );
}
#[test]
fn rejects_invalid_domains_and_nonunitary_operations() {
    let mut p = parse(2, "rx(1) q[0];");
    let mut ids = crate::ir::AstIdGenerator::starting_at(p.ast_id_bound());
    let one = ids.node(crate::ir::NumericExprKind::Rational(
        BigRational::from_integer(1.into()),
    ));
    let zero = ids.node(crate::ir::NumericExprKind::Rational(
        BigRational::from_integer(0.into()),
    ));
    let invalid = ids.node(crate::ir::NumericExprKind::Div(
        Box::new(one),
        Box::new(zero),
    ));
    let StatementKind::Apply { parameters, .. } = &mut p.body.statements[0].kind else {
        unreachable!()
    };
    parameters[0] = invalid;
    assert!(identity_bound(&p).is_none());
    assert!(identity_bound(&parse(2, "reset q[0];")).is_none());
}
