use super::*;

#[test]
fn ball_sum_products_encloses_exact_complex_sums_with_strided_inputs() {
    let input_values = [(2, 3), (-1, 4), (3, -2)];
    let coefficient_values = [(4, 5), (-2, 1), (1, -3)];
    let mut inputs = Balls::new(input_values.len());
    for (i, (re, im)) in input_values.into_iter().enumerate() {
        inputs.set_enclosure(
            i,
            &Complex {
                re: Interval::n(re),
                im: Interval::n(im),
            },
            64,
        );
    }
    // Forward, reverse and repeated inputs exercise positive, negative and
    // zero strides; one/three terms also retain the generic fallback.
    for indices in [vec![0, 2], vec![2, 0], vec![1, 1], vec![2], vec![2, 0, 1]] {
        let mut coefficients = Balls::new(indices.len());
        let (mut re, mut im) = (0, 0);
        for (j, &i) in indices.iter().enumerate() {
            let (a, b) = input_values[i];
            let (c, d) = coefficient_values[j];
            re += a * c - b * d;
            im += a * d + b * c;
            coefficients.set_enclosure(
                j,
                &Complex {
                    re: Interval::n(c),
                    im: Interval::n(d),
                },
                64,
            );
        }
        let mut output = Balls::new(1);
        output.sum_products(0, &inputs, &coefficients, indices.into_iter(), 64);
        let result = output.enclosure(0).unwrap();
        assert!(result.re.lo <= re && result.re.hi >= re);
        assert!(result.im.lo <= im && result.im.hi >= im);
    }
}

#[test]
fn ball_short_dot_preserves_input_and_coefficient_uncertainty() {
    let real = |lo: i32, hi: i32| {
        Complex::real(Interval {
            lo: Interval::n(lo).lo,
            hi: Interval::n(hi).hi,
        })
    };
    let mut inputs = Balls::new(2);
    inputs.set_enclosure(0, &real(-1, 2), 64);
    inputs.set_enclosure(1, &real(3, 4), 64);
    let mut coefficients = Balls::new(2);
    coefficients.set_enclosure(0, &real(2, 3), 64);
    coefficients.set_enclosure(1, &real(-2, -1), 64);
    let mut output = Balls::new(1);
    output.sum_products(0, &inputs, &coefficients, [0, 1].into_iter(), 64);
    let result = output.enclosure(0).unwrap();
    // Independent extrema of [-1,2]*[2,3] + [3,4]*[-2,-1].
    assert!(result.re.lo <= -11 && result.re.hi >= 3);
    assert!(result.im.lo <= 0 && result.im.hi >= 0);
}

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
        let (miter, _) = unitary::miter(&p, &p).unwrap();
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

#[test]
fn low_precision_norm_error_survives_deep_mixing() {
    let body = "h q[0]; ry(0.173) q[1]; cx q[1],q[2]; rz(0.291) q[0]; ".repeat(120);
    let p = parse(3, &body);
    let (miter, _) = unitary::miter(&p, &p).unwrap();
    let report = identity_bound(&miter).unwrap();
    assert_eq!(report.precision, 64);
    assert!(report.bound.unwrap() < BigRational::new(1.into(), 1_000_000_000_000i64.into()));
    assert_eq!(
        report.lower_bound.unwrap(),
        BigRational::from_integer(0.into())
    );
}

#[test]
fn adaptive_precision_respects_tiny_real_mismatches() {
    let tolerance = BigRational::new(1.into(), 1_000_000_000_000i64.into());
    for angle in ["0.3", "0.0000000001", "0.000000000002", "0.00000000000001"] {
        let p = parse(2, &format!("rz({angle}) q[0];"));
        let StatementKind::Apply { parameters, .. } = &p.body.statements[0].kind else {
            unreachable!()
        };
        // Independent analytic channel distance for Rz(theta): 2 sin(theta/2).
        let distance = number(&parameters[0], 0)
            .unwrap()
            .mul(&Interval::rational(&BigRational::new(1.into(), 2.into())).unwrap())
            .trig(true)
            .mul(&Interval::n(2));
        let report = identity_bound_with_tolerance(&p, &tolerance).unwrap();
        assert!(
            report.bound.as_ref().unwrap() >= &float_rational(&distance.lo).unwrap(),
            "{angle}: {report:?}"
        );
        assert!(
            report.lower_bound.as_ref().unwrap() <= &float_rational(&distance.hi).unwrap(),
            "{angle}: {report:?}"
        );
        if angle == "0.00000000000001" {
            assert!(report.bound.unwrap() < tolerance);
        } else {
            assert!(report.lower_bound.unwrap() > tolerance, "{angle}");
        }
    }
}

#[test]
fn tighter_target_retries_without_claiming_float_equality() {
    let p = parse(2, "h q[0]; ry(0.173) q[1]; cx q[1],q[0];");
    let (miter, _) = unitary::miter(&p, &p).unwrap();
    let target = BigRational::new(1.into(), BigInt::from(10).pow(24));
    let report = identity_bound_with_tolerance(&miter, &target).unwrap();
    assert_eq!(report.precision, 128);
    assert!(report.bound.unwrap() < target);
    assert_eq!(
        report.lower_bound.unwrap(),
        BigRational::from_integer(0.into())
    );
}
