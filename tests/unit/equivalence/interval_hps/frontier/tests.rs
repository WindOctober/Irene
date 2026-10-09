use super::*;

#[test]
fn gathered_fusion_dots_preserve_uncertainty() {
    for len in [3, 4, 8] {
        let real = |lo: i32, hi: i32| {
            Complex::real(Interval {
                lo: Interval::n(lo).lo,
                hi: Interval::n(hi).hi,
            })
        };
        let mut inputs = Balls::new(len);
        let mut coefficients = Balls::new(len);
        for i in 0..len {
            inputs.set_enclosure(i, &real(-1, 2), 64);
            coefficients.set_enclosure(i, &real(-2, 3), 64);
        }
        let mut output = Balls::new(1);
        output.sum_products(0, &inputs, &coefficients, (0..len).rev(), 64);
        let value = output.enclosure(0).unwrap();
        assert!(value.re.lo <= -4 * len as i32);
        assert!(value.re.hi >= 6 * len as i32);
        assert!(value.im.lo <= 0 && value.im.hi >= 0);
    }
}

#[test]
fn adjacent_fusion_preserves_noncommuting_gate_order() {
    let p = parse(1, "h q[0]; z q[0]; h q[0];");
    let blocks = crate::equivalence::operator::blocks(&p).unwrap();
    assert_eq!(blocks.len(), 2);
    let wires = super::super::super::qubits(&p);
    let domain = super::super::super::numeric::Enclosure { precision: 128 };
    let matrix = block_matrix(&p, &p.body.statements, &wires, &domain).unwrap();
    // In gate order H Z H = X, independently: only off-diagonal entries 1.
    // Reordering to H H Z would incorrectly give a diagonal Z.
    for (row, entries) in matrix.iter().enumerate() {
        let off = entries.iter().find(|(col, _)| *col == 1 - row).unwrap();
        assert!(off.1.re.lo <= 1 && off.1.re.hi >= 1);
        assert!(off.1.im.lo <= 0 && off.1.im.hi >= 0);
        for (col, value) in entries {
            if *col == row {
                assert!(value.re.lo <= 0 && value.re.hi >= 0);
            }
        }
    }
}

fn witness(p: &Program, precision: u32) -> Report {
    let wires = super::super::super::qubits(p);
    let blocks = crate::equivalence::operator::blocks(p).unwrap();
    contract(
        p,
        &wires,
        &blocks,
        Instant::now(),
        precision,
        true,
        &mut MAX_CELL_STEPS.clone(),
    )
    .unwrap()
}

#[test]
fn witness_global_phase_and_agreement_never_prove_eq() {
    for precision in [64, 128] {
        for body in ["rx(2*pi) q[0];", "h q[0]; h q[0];"] {
            let p = parse(2, body);
            let r = witness(&p, precision);
            assert_eq!(r.lower_bound.unwrap(), BigRational::from_integer(0.into()));
            assert_eq!(r.bound.unwrap(), BigRational::from_integer(2.into()));
            let fallback = identity_bound(&p).unwrap();
            assert_eq!(fallback.method, "frontier");
            assert!(
                fallback.bound.unwrap() < BigRational::new(1.into(), 1_000_000_000_000i64.into())
            );
        }
        assert!(
            witness(&parse(2, "z q[1];"), precision)
                .lower_bound
                .unwrap()
                > BigRational::from_integer(1.into())
        );
    }
}

#[test]
fn witness_h_distance_is_independently_sqrt_two() {
    let expected = Interval::n(2).sqrt().unwrap();
    let slack = BigRational::new(1.into(), 1_000_000_000_000i64.into());
    for precision in [64, 128] {
        let lower = witness(&parse(2, "h q[0];"), precision)
            .lower_bound
            .unwrap();
        // |<0|H|0>| = |<1|H|1>| = |<+|H|+>| = 1/sqrt(2).
        assert!(lower <= float_rational(&expected.hi).unwrap());
        assert!(lower + &slack >= float_rational(&expected.lo).unwrap());
    }
}

#[test]
fn witness_near_tolerance_and_preprocessing_fall_back() {
    let tolerance = BigRational::new(1.into(), 1_000_000_000_000i64.into());
    let tiny = parse(2, "rz(0.0000000000001) q[0];");
    assert!(witness(&tiny, 128).lower_bound.unwrap() <= tolerance);
    assert_eq!(
        identity_bound_with_tolerance(&tiny, &tolerance)
            .unwrap()
            .method,
        "frontier"
    );
    let h = parse(2, "h q[0];");
    assert_eq!(
        identity_bound_with_tolerance(&h, &tolerance)
            .unwrap()
            .method,
        "state-witness"
    );
    // 1.5 preprocessing error exceeds the sqrt(2) state witness; never stop
    // on that witness. The full trace certificate is still allowed to refine.
    let corrected_threshold = &tolerance + BigRational::new(3.into(), 2.into());
    let r = identity_bound_with_witness_target(&h, &tolerance, &corrected_threshold).unwrap();
    assert_eq!(r.method, "frontier");
    assert!(r.lower_bound.unwrap() > corrected_threshold);
}

#[test]
fn refused_witness_and_shared_budget_are_conservative() {
    let p = parse(2, "h q[0];");
    let wires = super::super::super::qubits(&p);
    let blocks = crate::equivalence::operator::blocks(&p).unwrap();
    let mut too_small = 11;
    assert!(
        contract(
            &p,
            &wires,
            &blocks,
            Instant::now(),
            64,
            true,
            &mut too_small
        )
        .is_none()
    );
    let mut enough = MAX_CELL_STEPS;
    assert!(contract(&p, &wires, &blocks, Instant::now(), 64, false, &mut enough).is_some());
    // Zero-wire witness refuses; the complete operator can still prove EQ.
    let p = crate::frontend::openqasm3::parse_str("OPENQASM 3.0;", "empty").unwrap();
    assert_eq!(identity_bound(&p).unwrap().method, "frontier");
}

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
        // Retain this independent full-operator trace test: do not replace
        // its obligation with the potentially weaker state-input bound.
        let wires = super::super::super::qubits(&p);
        let blocks = crate::equivalence::operator::blocks(&p).unwrap();
        let report = contract(
            &p,
            &wires,
            &blocks,
            Instant::now(),
            64,
            false,
            &mut MAX_CELL_STEPS.clone(),
        )
        .unwrap();
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

#[test]
fn low_precision_norm_error_survives_deep_mixing() {
    let body = "h q[0]; ry(0.173) q[1]; cx q[1],q[2]; rz(0.291) q[0]; ".repeat(120);
    let p = parse(3, &body);
    let (miter, _) = unitary_miter::miter(&p, &p).unwrap();
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
    let (miter, _) = unitary_miter::miter(&p, &p).unwrap();
    let target = BigRational::new(1.into(), BigInt::from(10).pow(24));
    let report = identity_bound_with_tolerance(&miter, &target).unwrap();
    assert_eq!(report.precision, 128);
    assert!(report.bound.unwrap() < target);
    assert_eq!(
        report.lower_bound.unwrap(),
        BigRational::from_integer(0.into())
    );
}
