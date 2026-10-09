//! Rewriting is checked as an operator/channel transformation, not by gate counts.
mod common;
use irene::{
    equivalence::{
        EquivalenceConfig, Verdict, analyze,
        dependency_miter::{Mode, Options, candidate},
        interval_hps, unitary_miter,
    },
    frontend::openqasm3,
    ir::Program,
};
use num_rational::BigRational;

fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; {body}"),
        "rewrite-contract.qasm",
    )
    .unwrap()
}
fn tolerance() -> BigRational {
    BigRational::new(1.into(), 1_000_000_000_000i64.into())
}
fn options(mode: Mode, approximate: bool) -> Options {
    Options {
        mode,
        exact_order: 256,
        diamond_tolerance: approximate.then(tolerance),
    }
}

#[test]
fn exact_candidates_preserve_complete_operators_in_all_modes() {
    // Compare every matrix entry, not just the trace or a few input states.
    // These cases deliberately include nonidentities and noncommuting barriers.
    for (left, right) in [
        (
            "cx q[0],q[1]; cx q[1],q[0]; cx q[0],q[1];",
            "swap q[0],q[1];",
        ),
        ("h q[0]; swap q[0],q[1]; h q[1];", ""),
        ("h q[0]; t q[0];", "h q[0];"),
        ("s q[0]; rx(pi/2) q[0]; s q[0];", "h q[0];"),
        (
            "t q[0]; t q[0]; x q[1]; rx(pi/2) q[0]; s q[0];",
            "x q[1]; h q[0];",
        ),
        (
            "s q[0]; cx q[1],q[0]; rx(pi/2) q[0]; s q[0];",
            "cx q[1],q[0]; h q[0];",
        ),
        ("cx q[0],q[1]; t q[0]; cx q[0],q[1];", "t q[0];"),
        ("cx q[0],q[1]; t q[1]; cx q[0],q[1];", "t q[1];"),
        (
            "h q[1]; crx(pi/2) q[0],q[1]; h q[1]; rz(0.5709439576515822) q[1];",
            "crz(pi/2) q[0],q[1]; rz(0.5709439576515822) q[1];",
        ),
        ("rx(0.7) q[0]; rz(0) q[0]; rx(-0.7) q[0];", ""),
        ("crx(2*pi) q[0],q[1]; cry(4*pi) q[1],q[2];", ""),
        ("rx(0.7) q[0]; rz(0.2) q[0];", "rz(0.2) q[0]; rx(0.7) q[0];"),
    ] {
        let (left, right) = (parse(left), parse(right));
        for (a, b) in [(&left, &right), (&right, &left)] {
            let config = EquivalenceConfig::positional(a, b).unwrap();
            // The public candidate chooses the longer program as the forward side.
            let (forward, inverse) = if a.operation_count() >= b.operation_count() {
                (a, b)
            } else {
                (b, a)
            };
            let original = unitary_miter::miter(forward, inverse).unwrap().0;
            for mode in [Mode::Wire, Mode::Dag, Mode::DagScheduled] {
                let c = candidate(a, b, &config, &options(mode, false)).unwrap();
                assert!(c.is_exact());
                common::unitary::assert_same(&c.circuit, &original);
            }
        }
    }
}

#[test]
fn mixed_circuit_rewrites_match_an_independent_matrix_oracle() {
    let choices = [
        "h q[0];",
        "s q[1];",
        "t q[2];",
        "rx(pi/2) q[0];",
        "cx q[2],q[0];",
        "cz q[1],q[2];",
        "swap q[0],q[2];",
        "swap q[1],q[2];",
        "crz(pi/4) q[0],q[2];",
        "cx q[0],q[1]; cx q[1],q[0]; cx q[0],q[1];",
    ];
    let identity = parse("");
    for seed in 0..32u64 {
        let mut n = seed + 1;
        let mut body = String::new();
        for _ in 0..16 {
            n = n.wrapping_mul(6364136223846793005).wrapping_add(1);
            body.push_str(choices[(n >> 32) as usize % choices.len()]);
        }
        let source = parse(&body);
        let config = EquivalenceConfig::positional(&source, &identity).unwrap();
        for mode in [Mode::Wire, Mode::Dag, Mode::DagScheduled] {
            let c = candidate(&source, &identity, &config, &options(mode, false)).unwrap();
            assert!(c.is_exact());
            common::unitary::assert_same(&source, &c.circuit);
        }
    }
}

#[test]
fn controlled_periods_and_global_phases_remain_distinct() {
    let identity = parse("");
    for (body, expected) in [
        ("rx(2*pi) q[0];", Verdict::Equivalent),
        ("crx(2*pi) q[0],q[1];", Verdict::NotEquivalent),
        ("cry(2*pi) q[0],q[1];", Verdict::NotEquivalent),
        ("crz(2*pi) q[0],q[1];", Verdict::NotEquivalent),
        ("crx(4*pi) q[0],q[1];", Verdict::Equivalent),
        ("cp(2*pi) q[0],q[1];", Verdict::Equivalent),
        ("p(pi/1048576) q[0];", Verdict::NotEquivalent),
    ] {
        let p = parse(body);
        let config = EquivalenceConfig::positional(&p, &identity).unwrap();
        assert_eq!(
            analyze(&p, &identity, &config).unwrap().verdict,
            expected,
            "{body}"
        );
    }
    // Exact analysis can refuse an arbitrary-radian decimal; it cannot round
    // that nonzero angle away. Its inability to prove NEQ is not a proof of EQ.
    let tiny = parse("p(0.00000000000000001) q[0];");
    let config = EquivalenceConfig::positional(&tiny, &identity).unwrap();
    assert_ne!(
        analyze(&tiny, &identity, &config).unwrap().verdict,
        Verdict::Equivalent
    );
    let c = candidate(&tiny, &identity, &config, &options(Mode::Dag, false)).unwrap();
    assert!(c.is_exact());
    assert!(!c.circuit.body.statements.is_empty());
}

#[test]
fn approximate_rewrites_carry_a_global_error_certificate() {
    for (left, right) in [
        ("rz(pi/2) q[0];", "rz(1.5707963267948966) q[0];"),
        ("crz(12.566370614359172) q[0],q[1];", ""),
        (
            "rx(2.146706) q[0]; p(pi/2) q[0]; p(0.6381575) q[0]; p(-2.2089538267948967) q[0]; rx(-2.146706) q[0];",
            "",
        ),
        (
            "p(pi/2) q[0]; h q[2]; p(0.6381575) q[0]; cx q[0],q[1]; p(-2.2089538267948967) q[0];",
            "h q[2]; cx q[0],q[1];",
        ),
    ] {
        let (a, b) = (parse(left), parse(right));
        let config = EquivalenceConfig::positional(&a, &b).unwrap();
        let c = candidate(&a, &b, &config, &options(Mode::Dag, true)).unwrap();
        let residual = interval_hps::identity_bound(&c.circuit);
        assert!(c.statistics.diamond_error >= BigRational::from_integer(0.into()));
        assert!(c.statistics.diamond_error <= tolerance());
        assert!(residual.bound.unwrap() + &c.statistics.diamond_error <= tolerance());
        // A decimal approximation must never become an exact equality proof.
        let exact = candidate(&a, &b, &config, &options(Mode::Dag, false)).unwrap();
        assert!(exact.is_exact());
        assert!(!exact.circuit.body.statements.is_empty());
    }
}

#[test]
fn approximation_cannot_erase_noncommuting_or_control_dependent_differences() {
    let identity = parse("");
    for body in [
        "crz(6.283185307179586) q[0],q[1];",
        "p(pi/2) q[0]; h q[0]; p(0.6381575) q[0]; p(-2.2089538267948967) q[0];",
        "p(pi/2) q[0]; cx q[1],q[0]; p(0.6381575) q[0]; p(-2.2089538267948967) q[0];",
        "cp(pi/2) q[0],q[1]; cp(0.6381575) q[0],q[2]; cp(-2.2089538267948967) q[0],q[1];",
        "p(0.001) q[0]; p(0.001) q[1]; p(0.001) q[2];",
    ] {
        let p = parse(body);
        let config = EquivalenceConfig::positional(&p, &identity).unwrap();
        let c = candidate(&p, &identity, &config, &options(Mode::Dag, true)).unwrap();
        let residual = interval_hps::identity_bound(&c.circuit);
        assert!(
            residual
                .corrected_lower_bound(&c.statistics.diamond_error)
                .unwrap()
                > tolerance(),
            "{body}"
        );
    }
}

#[test]
fn candidates_refuse_partial_interfaces_nonunitaries_and_invalid_options() {
    let p = parse("h q[0];");
    let config = EquivalenceConfig::positional(&p, &p).unwrap();
    let mut partial = config.clone();
    partial.output_pairs.pop();
    assert!(candidate(&p, &p, &partial, &options(Mode::Dag, false)).is_none());
    let mut initialized = config.clone();
    initialized.input_pairs.pop();
    let mut reordered = config.clone();
    reordered.input_pairs.swap(0, 1);
    let mut permuted = config.clone();
    let first = permuted.output_pairs[0].right.clone();
    permuted.output_pairs[0].right = permuted.output_pairs[1].right.clone();
    permuted.output_pairs[1].right = first;
    for interface in [initialized, reordered, permuted] {
        assert!(candidate(&p, &p, &interface, &options(Mode::Dag, false)).is_none());
    }
    for body in ["reset q[0];", "bit c; c=measure q[0];"] {
        let p = parse(body);
        let config = EquivalenceConfig::positional(&p, &p).unwrap();
        assert!(candidate(&p, &p, &config, &options(Mode::Dag, false)).is_none());
    }
    for bad in [
        Options {
            exact_order: 3,
            ..options(Mode::Dag, false)
        },
        Options {
            diamond_tolerance: Some(BigRational::from_integer((-1).into())),
            ..options(Mode::Dag, false)
        },
    ] {
        assert!(candidate(&p, &p, &config, &bad).is_none());
    }
}
