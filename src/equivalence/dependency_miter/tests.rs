use super::*;
use crate::frontend::openqasm3;
fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {body}"),
        "dag-test",
    )
    .unwrap()
}
fn options(tolerance: bool) -> Options {
    Options {
        mode: Mode::Dag,
        exact_order: 256,
        diamond_tolerance: tolerance
            .then(|| BigRational::new(1.into(), 1_000_000_000_000i64.into())),
    }
}
fn build(a: &str, b: &str, approx: bool) -> Candidate {
    let a = parse(a);
    let b = parse(b);
    let config = EquivalenceConfig::positional(&a, &b).unwrap();
    candidate(&a, &b, &config, &options(approx)).unwrap()
}
#[test]
fn nested_inverse_cascade_reaches_fixed_point() {
    let body = "h q[0]; cx q[0],q[1]; t q[1]; ccx q[0],q[1],q[2];".repeat(100);
    let c = build(&body, &body, false);
    assert_eq!(c.statistics.after, 0);
    assert!(c.is_exact());
    assert!(c.statistics.removed_h >= 200);
}
#[test]
fn commuting_control_phase_cancels_without_crossing_target() {
    let c = build("cx q[0],q[1]; t q[0]; cx q[0],q[1];", "t q[0];", false);
    assert_eq!(c.statistics.after, 0);
    let c = build("cx q[0],q[1]; t q[1]; cx q[0],q[1];", "t q[1];", false);
    assert_ne!(c.statistics.after, 0);
}
#[test]
fn directed_pi_comparison_is_tolerant_not_exact() {
    let c = build("rz(pi/2) q[0];", "rz(1.5707963267948966) q[0];", true);
    assert_eq!(c.statistics.after, 0);
    assert!(!c.is_exact());
    assert_eq!(c.statistics.approximate_pairs, 1);
    assert!(c.statistics.diamond_error < options(true).diamond_tolerance.unwrap());
    let exact = build("rz(pi/2) q[0];", "rz(1.5707963267948966) q[0];", false);
    assert_ne!(exact.statistics.after, 0);
}
#[test]
fn tolerance_does_not_leak_across_parallel_wires() {
    let c = build(
        "p(0.0000000000002) q[0];p(0.0000000000002) q[1];p(0.0000000000002) q[2];",
        "p(0) q[0];p(0) q[1];p(0) q[2];",
        true,
    );
    assert_ne!(c.statistics.after, 0);
    assert!(c.statistics.diamond_error <= options(true).diamond_tolerance.unwrap());
}
#[test]
fn controlled_rotation_keeps_four_pi_period() {
    let c = build(
        "crz(6.283185307179586) q[0],q[1];",
        "crz(0) q[0],q[1];",
        true,
    );
    assert_ne!(c.statistics.after, 0);
    let c = build(
        "crz(12.566370614359172) q[0],q[1];",
        "crz(0) q[0],q[1];",
        true,
    );
    assert_eq!(c.statistics.after, 0);
    assert!(!c.is_exact());
}
#[test]
fn clearly_different_and_noncommuting_rotations_are_not_erased() {
    assert_ne!(
        build("rz(0.001) q[0];", "rz(0) q[0];", true)
            .statistics
            .after,
        0
    );
    assert_ne!(
        build(
            "rx(0.7) q[0]; rz(0.2) q[0];",
            "rz(0.2) q[0]; rx(0.7) q[0];",
            true
        )
        .statistics
        .after,
        0
    );
}
#[test]
fn reject_partial_interface_measurement_and_bad_numeric_domain() {
    let a = parse("h q[0];");
    let b = a.clone();
    let mut config = EquivalenceConfig::positional(&a, &b).unwrap();
    config.output_pairs.pop();
    assert!(candidate(&a, &b, &config, &options(true)).is_none());
    let a = parse("reset q[0];");
    let config = EquivalenceConfig::positional(&a, &a).unwrap();
    assert!(candidate(&a, &a, &config, &options(true)).is_none());
    assert!(
        openqasm3::parse_str(
            "OPENQASM 3.0; include \"stdgates.inc\"; qubit q; rz(pi/0) q;",
            "invalid"
        )
        .is_err()
    );
}

#[test]
fn mixed_phase_block_cancels_and_exposes_inverse_rotations() {
    let body = "rx(2.146706) q[0]; p(pi/2) q[0]; p(0.6381575) q[0]; \
        p(-2.2089538267948967) q[0]; rx(-2.146706) q[0];";
    let c = build(body, "", true);
    assert_eq!(c.statistics.after, 0);
    assert_eq!(c.statistics.approximate_blocks, 1);
    assert!(!c.is_exact());
    assert!(
        c.statistics.diamond_error < BigRational::new(1.into(), 1_000_000_000_000_000i64.into())
    );
    assert_ne!(build(body, "", false).statistics.after, 0);
}

#[test]
fn phase_block_can_cross_disjoint_and_proven_commuting_gates() {
    let body = "p(pi/2) q[0]; h q[2]; p(0.6381575) q[0]; \
        cx q[0],q[1]; p(-2.2089538267948967) q[0];";
    let c = build(body, "h q[2]; cx q[0],q[1];", true);
    assert_eq!(c.statistics.after, 0);
    assert_eq!(c.statistics.approximate_blocks, 1);
}

#[test]
fn phase_block_never_crosses_noncommuting_target_or_hadamard() {
    for barrier in ["h q[0];", "cx q[1],q[0];"] {
        let body =
            format!("p(pi/2) q[0]; {barrier} p(0.6381575) q[0]; p(-2.2089538267948967) q[0];");
        let c = build(&body, "", true);
        assert_ne!(c.statistics.after, 0);
        assert_eq!(c.statistics.approximate_blocks, 0);
    }
}

#[test]
fn phase_blocks_respect_global_error_and_reject_clear_difference() {
    let body = (0..3)
        .map(|q| format!("p(pi/2) q[{q}]; p(0.6) q[{q}]; p(-2.1707963267946966) q[{q}];"))
        .collect::<String>();
    let c = build(&body, "", true);
    assert_ne!(c.statistics.after, 0);
    assert!(c.statistics.diamond_error <= options(true).diamond_tolerance.unwrap());
    assert_ne!(
        build("p(pi/2) q[0]; p(0.6) q[0]; p(-2.17) q[0];", "", true)
            .statistics
            .after,
        0
    );
}

#[test]
fn controlled_rotation_blocks_keep_operator_period_and_wire_order() {
    for (last, empty) in [("4.11238898038469", false), ("10.395574287564276", true)] {
        let body = format!("crz(pi/2) q[0],q[1]; crz(0.6) q[0],q[1]; crz({last}) q[0],q[1];");
        let c = build(&body, "", true);
        assert_eq!(c.statistics.after == 0, empty);
    }
    let c = build(
        "cp(pi/2) q[0],q[1]; cp(0.6381575) q[0],q[2]; cp(-2.2089538267948967) q[0],q[1];",
        "",
        true,
    );
    assert_ne!(c.statistics.after, 0);
    assert_eq!(c.statistics.approximate_blocks, 0);
}

#[test]
fn exact_single_gate_identities_are_removed_without_tolerance() {
    let c = build(
        "p(0*pi) q[0]; rx(-0) q[0]; ry(1.25-1.25) q[0]; \
        rz(pi-pi) q[0]; cp(2*pi) q[0],q[1]; crx(4*pi) q[0],q[1]; \
        cry(-4*pi) q[1],q[2]; crz(0) q[0],q[2];",
        "",
        false,
    );
    assert_eq!(c.statistics.after, 0);
    assert!(c.is_exact());
    assert!(c.statistics.exact_identity_gates > 0);
    assert_eq!(c.statistics.approximate_pairs, 0);
    assert_eq!(c.statistics.approximate_blocks, 0);
}

#[test]
fn single_identity_removal_reconnects_different_axis_neighbors() {
    let c = build("rx(0.7) q[0]; rz(0) q[0]; rx(-0.7) q[0];", "", false);
    assert_eq!(c.statistics.after, 0);
    assert!(c.is_exact());
    let c = build(
        "rz(3*pi/2) q[0]; ry(pi/2) q[0]; rz(-0) q[0]; \
        ry(-1.5707963267948966) q[0]; rz(-4.71238898038469) q[0];",
        "",
        true,
    );
    assert_eq!(c.statistics.after, 0);
    assert_eq!(c.statistics.exact_identity_gates, 1);
    assert!(!c.is_exact());
}

#[test]
fn near_zero_and_two_pi_controlled_rotations_are_not_exact_identities() {
    for body in [
        "p(0.00000000000000001) q[0];",
        "rx(2*pi) q[0];",
        "crx(2*pi) q[0],q[1];",
        "cry(2*pi) q[0],q[1];",
        "crz(2*pi) q[0],q[1];",
    ] {
        let c = build(body, "", false);
        assert_ne!(c.statistics.after, 0, "{body}");
        assert_eq!(c.statistics.exact_identity_gates, 0, "{body}");
        assert!(c.is_exact());
    }
}

#[test]
fn tolerant_singleton_remains_explicit_after_removing_its_zero_partner() {
    let c = build(
        "crz(12.566370614359172) q[0],q[1];",
        "crz(0) q[0],q[1];",
        true,
    );
    assert_eq!(c.statistics.after, 0);
    assert!(c.statistics.exact_identity_gates > 0);
    assert_eq!(c.statistics.approximate_single_gates, 1);
    assert!(!c.is_exact());
    assert_ne!(
        build("crz(6.283185307179586) q[0],q[1];", "", true)
            .statistics
            .after,
        0
    );
}

#[test]
fn tiny_exact_inverse_pair_is_preferred_to_tolerant_singletons() {
    let c = build(
        "rx(0.00000000000000001) q[0]; rz(0) q[0]; rx(-0.00000000000000001) q[0];",
        "",
        true,
    );
    assert_eq!(c.statistics.after, 0);
    assert!(c.is_exact());
    assert_eq!(c.statistics.approximate_single_gates, 0);
}

#[test]
fn gate_ablation_declines_all_miter_modes_before_rewriting() {
    use crate::ablation::{self, Config, Group};
    for body in ["h q[0]; h q[0];", "p(0.00000000000000001) q[0];"] {
        let left = parse(body);
        let right = parse("");
        let config = EquivalenceConfig::positional(&left, &right).unwrap();
        for mode in [Mode::Wire, Mode::Dag, Mode::DagScheduled] {
            for tolerant in [false, true] {
                let options = Options {
                    mode,
                    ..options(tolerant)
                };
                let (result, report) = ablation::run(Config::without([Group::GateRewrite]), || {
                    candidate(&left, &right, &config, &options)
                });
                assert!(result.is_none(), "{mode:?}, tolerant={tolerant}");
                assert_eq!(report.counts(Group::GateRewrite).skipped, 1);
                assert_eq!(report.counts(Group::GateRewrite).admitted, 0);
                assert!(candidate(&left, &right, &config, &options).is_some());
            }
        }
    }
}
