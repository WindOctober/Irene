//! Certified distances through the public interval backend, independent of routing.
use irene::{equivalence::interval_hps::*, frontend::openqasm3};
use num_bigint::BigInt;
use num_rational::BigRational;

#[test]
fn exact_trace_distance_lower_is_positive_only_for_valid_mismatches() {
    let r = |n: i64, d: i64| BigRational::new(n.into(), d.into());
    for (norm, lower) in [
        (r(0i64, 1i64), r(2, 1)),
        (r(1, 16), r(15, 8)),
        (r(1, 4), r(3, 2)),
        (r(1, 1), r(0, 1)),
    ] {
        let bound = exact_trace_distance_lower(&norm).unwrap();
        assert_eq!(bound, lower);
        // Squaring checks the lower enclosure against 2 sqrt(1-r).
        assert!(&bound * &bound <= r(4, 1) * (r(1, 1) - norm));
    }
    assert!(exact_trace_distance_lower(&r(-1, 1)).is_none());
    assert!(exact_trace_distance_lower(&r(2, 1)).is_none());
}

fn run(body: &str) -> Report {
    let p = openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; {body}"),
        "test",
    )
    .unwrap();
    identity_bound(&p)
}

fn tolerance() -> BigRational {
    BigRational::new(1.into(), 1_000_000_000_000i64.into())
}

#[test]
fn arbitrary_rotation_inverse_cancels() {
    let r = run("rx(0.123456789) q[0]; rx(-0.123456789) q[0];");
    assert!(r.bound.as_ref().is_some_and(|b| b < &tolerance()), "{r:?}");
    assert_eq!(r.lower_bound.unwrap(), BigRational::from_integer(0.into()));
}

#[test]
fn phase_and_amplitude_differences_have_positive_lower_bounds() {
    for body in ["x q[0];", "z q[0];", "cz q[0],q[1];", "rx(0.123) q[0];"] {
        let r = run(body);
        assert!(
            r.lower_bound.as_ref().is_some_and(|b| b > &tolerance()),
            "{r:?}"
        );
        assert!(r.lower_bound.as_ref().unwrap() <= r.bound.as_ref().unwrap());
    }
}

#[test]
fn global_phase_and_destructive_interference_are_not_neq() {
    for body in [
        "rx(2*pi) q[0];",
        "h q[0]; h q[0];",
        "p(0.123) q[0]; p(-0.123) q[0];",
    ] {
        let r = run(body);
        assert_eq!(
            r.lower_bound.as_ref(),
            Some(&BigRational::from_integer(0.into())),
            "{body}: {r:?}"
        );
    }
}

#[test]
fn lower_bound_subtracts_preprocessing_error() {
    let r = run("rx(1e-8) q[0];");
    let zero = BigRational::from_integer(0.into());
    let lower = r.lower_bound.as_ref().unwrap();
    assert!(lower > &tolerance());
    assert_eq!(r.corrected_lower_bound(lower), Some(zero.clone()));
    assert_eq!(
        r.corrected_lower_bound(&(lower * BigInt::from(2))),
        Some(zero.clone())
    );
    assert_eq!(
        r.corrected_lower_bound(&(lower / BigInt::from(2))),
        Some(lower / BigInt::from(2))
    );
    assert!(
        r.corrected_lower_bound(&BigRational::from_integer((-1).into()))
            .is_none()
    );
    assert!(
        run("bit c; c=measure q[0];")
            .corrected_lower_bound(&zero)
            .is_none()
    );
}

#[test]
fn noncommuting_inverse_sequence_and_global_phase() {
    let r = run("rx(0.123) q[0]; ry(0.456) q[0]; ry(-0.456) q[0]; rx(-0.123) q[0]; rx(2*pi) q[1];");
    assert!(r.bound.as_ref().is_some_and(|b| b < &tolerance()), "{r:?}");
    let wrong = run("rx(0.123) q[0]; ry(0.456) q[0]; rx(-0.123) q[0]; ry(-0.456) q[0];");
    assert!(wrong.lower_bound.unwrap() > tolerance());
}

#[test]
fn small_scalar_and_phase_residuals_are_bounded() {
    for body in ["rx(1e-15) q[0];", "p(1e-15) q[0];"] {
        let r = run(body);
        assert!(r.bound.as_ref().is_some_and(|b| b < &tolerance()), "{r:?}");
    }
}

#[test]
fn measurements_refuse() {
    assert!(run("bit c; c=measure q[0];").bound.is_none());
}

#[test]
fn analytic_distances_are_enclosed_without_assuming_a_backend() {
    // ||Rz(theta) - I||_diamond = 2 sin(theta/2), for 0 <= theta <= pi.
    // Squared distances here are rational, so no floating-point oracle is needed.
    for (body, squared_distance) in [
        ("rz(pi/3) q[0];", 1),
        ("rz(pi/2) q[0];", 2),
        ("rz(pi) q[0];", 4),
        ("h q[0];", 4),
        // CX fixes |0>, |1> (control q[1]) and the uniform superposition.
        // Agreement on the three probe states must not be reported as EQ.
        ("cx q[1],q[0];", 4),
    ] {
        let r = run(body);
        let expected = BigRational::from_integer(squared_distance.into());
        let (lower, upper) = (r.lower_bound.unwrap(), r.bound.unwrap());
        assert!(lower > tolerance(), "{body}");
        assert!(&lower * &lower <= expected, "{body}: lower={lower}");
        assert!(&upper * &upper >= expected, "{body}: upper={upper}");
    }
}
