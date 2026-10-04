use super::*;
use crate::frontend::openqasm3;

fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; {body}"),
        "stage1.qasm",
    )
    .unwrap()
}

fn config(left: &Program, right: &Program) -> EquivalenceConfig {
    EquivalenceConfig::positional(left, right).unwrap()
}

fn rational(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

#[test]
fn public_entry_returns_exact_trace_evidence_in_both_directions() {
    for (left, right, norm) in [
        ("h q[0]; h q[0];", "", rational(1, 1)),
        ("h q[0];", "", rational(0, 1)),
        ("h q[0]; cz q[0],q[1]; h q[0];", "", rational(1, 4)),
        // The extra XZXZ contributes only a global minus sign.
        (
            "h q[0]; x q[0]; z q[0]; x q[0]; z q[0];",
            "h q[0];",
            rational(1, 1),
        ),
    ] {
        let left = parse(left);
        let right = parse(right);
        for (a, b) in [(&left, &right), (&right, &left)] {
            let before = (a.clone(), b.clone());
            let result = analyze(a, b, &config(a, b)).unwrap();
            if norm == rational(1, 1) {
                assert_eq!(result.verdict, Verdict::Equivalent);
                assert_eq!(result.evidence, Evidence::UnitaryTraceExact);
            } else {
                assert_eq!(result.verdict, Verdict::NotEquivalent);
                assert_eq!(
                    result.evidence,
                    Evidence::UnitaryTraceMismatch {
                        normalized_trace_norm_squared: norm.clone(),
                    }
                );
            }
            assert_eq!(
                (&before.0, &before.1),
                (a, b),
                "must not mutate source programs"
            );
        }
    }
}

#[test]
fn public_entry_preserves_nonrational_mismatch_coefficients() {
    let left = parse("h q[0];");
    let right = parse("h q[0]; t q[0];");
    let order = 1u64 << 62;
    for (a, b) in [(&left, &right), (&right, &left)] {
        let result = analyze(a, b, &config(a, b)).unwrap();
        assert_eq!(result.verdict, Verdict::NotEquivalent);
        // cos^2(pi/8) = 1/2 + sqrt(2)/4.
        assert_eq!(
            result.evidence,
            Evidence::UnitaryTraceCyclotomicMismatch {
                normalized_trace_norm_squared: vec![
                    (0, rational(1, 2)),
                    (order / 8, rational(1, 4)),
                    (3 * order / 8, rational(-1, 4)),
                ],
            }
        );
    }
}

#[test]
fn incomplete_or_inapplicable_trace_is_unknown_not_a_negative_certificate() {
    for (left, right) in [
        ("reset q[0];", ""),
        ("bit c; c = measure q[0];", "bit c = 0;"),
        ("h q[0]; p(pi/3) q[0]; h q[0];", ""),
        ("rx(pi/3) q[0];", ""),
    ] {
        let left = parse(left);
        let right = parse(right);
        let config = config(&left, &right);
        assert!(unitary_trace::certificate(&left, &right, &config).is_none());
        let result = analyze(&left, &right, &config).unwrap();
        // Trace refusal is not a negative certificate. Later support reasoning
        // may independently establish a mismatch.
        assert!(matches!(
            result.evidence,
            Evidence::KernelAggregationRequired | Evidence::OutputSupportMismatch
        ));
    }
}

#[test]
fn partial_initialized_and_nonpositional_interfaces_do_not_use_full_trace() {
    let left = parse("h q[0];");
    let right = parse("h q[0];");
    let full = config(&left, &right);
    let mut partial = full.clone();
    partial.output_pairs.pop();
    let mut initialized = full.clone();
    initialized.input_pairs.pop();
    let mut permuted = full;
    let (a, b) = permuted.output_pairs.split_at_mut(1);
    std::mem::swap(&mut a[0].right, &mut b[0].right);
    for cfg in [partial, initialized, permuted] {
        assert!(unitary_trace::certificate(&left, &right, &cfg).is_none());
        let result = analyze(&left, &right, &cfg).unwrap();
        assert!(matches!(
            result.evidence,
            Evidence::ExactHps
                | Evidence::KernelAggregationRequired
                | Evidence::OutputSupportMismatch
        ));
    }
}

#[test]
fn malformed_interfaces_are_errors_before_any_successful_certificate() {
    let left = parse("h q[0]; h q[0];");
    let right = parse("");
    let full = config(&left, &right);
    let mut duplicate_input = full.clone();
    duplicate_input
        .input_pairs
        .push(full.input_pairs[0].clone());
    let mut duplicate_output = full.clone();
    duplicate_output
        .output_pairs
        .push(full.output_pairs[0].clone());
    let mut unknown_input = full.clone();
    unknown_input.input_pairs[0].left = Endpoint::Quantum(Qubit {
        register: SymbolId(999),
        index: 0,
    });
    let mut unknown_output = full.clone();
    unknown_output.output_pairs[0].right = Endpoint::Quantum(Qubit {
        register: SymbolId(999),
        index: 0,
    });
    let mut classical_input = full;
    classical_input.input_pairs[0].left = Endpoint::Classical(ClassicalBit {
        register: SymbolId(999),
        index: 0,
    });
    for cfg in [
        duplicate_input,
        duplicate_output,
        unknown_input,
        unknown_output,
        classical_input,
    ] {
        let error = analyze(&left, &right, &cfg).unwrap_err();
        assert!(!matches!(error, InterfaceError::Unsupported(_)));
        // Trace refusal falls through to the existing preparation rules.
        assert_eq!(error, prepare_comparison(&left, &right, &cfg).unwrap_err());
    }
}

#[test]
fn malformed_numeric_pairing_is_not_hidden_by_unsupported_semantics() {
    let left = parse("input float[64] theta;");
    let right = parse("input float[64] theta;");
    let full = config(&left, &right);
    let mut duplicate = full.clone();
    duplicate
        .numeric_input_pairs
        .push(full.numeric_input_pairs[0]);
    assert!(matches!(
        analyze(&left, &right, &duplicate),
        Err(InterfaceError::DuplicateNumericInput { .. })
    ));
    let mut unknown = full.clone();
    unknown.numeric_input_pairs[0].left = SymbolId(999);
    assert!(matches!(
        analyze(&left, &right, &unknown),
        Err(InterfaceError::UnknownNumericInput { .. })
    ));
    let mut mismatch = right;
    mismatch.numeric_inputs[0].ty = crate::ir::NumericType::Angle(Some(64));
    assert!(matches!(
        analyze(&left, &mismatch, &full),
        Err(InterfaceError::NumericTypeMismatch { .. })
    ));
}

#[test]
fn cancelling_invalid_angles_never_produces_a_certificate() {
    use crate::ir::{AstIdGenerator, NumericExprKind, StatementKind};
    let mut left = parse("rx(pi/2) q[0]; rx(-pi/2) q[0];");
    let mut ids = AstIdGenerator::default();
    for statement in &mut left.body.statements {
        let StatementKind::Apply { parameters, .. } = &mut statement.kind else {
            unreachable!()
        };
        let zero = ids.node(NumericExprKind::Rational(rational(0, 1)));
        parameters[0] = ids.node(NumericExprKind::Div(
            Box::new(parameters[0].clone()),
            Box::new(zero),
        ));
    }
    let right = parse("");
    assert!(matches!(
        analyze(&left, &right, &config(&left, &right)),
        Err(InterfaceError::Execution { .. })
    ));
}
