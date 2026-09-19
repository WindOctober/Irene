use super::*;
use crate::frontend::openqasm3::parse_str;
use crate::symbolic::{ExecutionConfig, OutputSelection, execute};

#[test]
fn execution_checks_domains_even_when_all_outputs_are_discarded() {
    for body in [
        "p(0.0*(1.0/(0.0+0.0))) q;",
        "if (false) { p(1.0/(0.0+0.0)) q; }",
        "if (true) { } else { p(1.0/(0.0+0.0)) q; }",
        "for int i in [0:0] { p(1.0/(0.0+0.0)) q; }",
    ] {
        assert!(
            matches!(
                execute(
                    &parse(body),
                    &ExecutionConfig::zero(),
                    &OutputSelection::new([], [])
                ),
                Err(SymbolicError::NumericDomain(_))
            ),
            "{body}"
        );
    }
    assert!(
        execute(
            &parse("p(1.0/pi) q;"),
            &ExecutionConfig::zero(),
            &OutputSelection::new([], [])
        )
        .is_ok()
    );
}

fn parse(body: &str) -> Program {
    parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit q; {body}"),
        "numeric-domain.qasm",
    )
    .unwrap()
}

#[test]
fn all_rational_signs_and_constant_divisors_are_checked_exactly() {
    for numerator in -4..=4 {
        for denominator in -4..=4 {
            // Floating-source nodes keep the composite divisor in the IR.
            let source = parse(&format!("p(({numerator}.0)/(0.0+({denominator}.0))) q;"));
            let result = numeric_domains(&source);
            assert_eq!(
                result.is_ok(),
                denominator != 0,
                "{numerator}/{denominator}"
            );
        }
    }
    for angle in [
        "pi/2",
        "pi/(0.5+0.5)",
        "1.0/pi",
        "1.0/(-pi)",
        "1.0/(tau-euler)",
        "0.0/(pi*pi)",
    ] {
        assert!(
            numeric_domains(&parse(&format!("p({angle}) q;"))).is_ok(),
            "{angle}"
        );
    }
}

#[test]
fn zero_products_inactive_branches_and_dead_wires_do_not_hide_domains() {
    for body in [
        "p(0.0*(1.0/(0.0+0.0))) q;",
        "p(1.0/(0.0*(1.0/(0.0+0.0)))) q;",
        "if (false) { p(1.0/(0.0+0.0)) q; }",
        "if (true) { } else { p(1.0/(0.0+0.0)) q; }",
        "qubit dead; p(1.0/(0.0+0.0)) dead;",
        "p(1.0/(pi-pi)) q;",
        "p(1.0/(tau-2*pi)) q;",
    ] {
        assert!(numeric_domains(&parse(body)).is_err(), "{body}");
    }
}

#[test]
fn formal_inputs_are_not_implicitly_assumed_nonzero_and_refusal_is_bounded() {
    for (body, accepted) in [
        ("input angle theta; p(theta/2) q;", true),
        ("input angle theta; p(theta*pi) q;", true),
        ("input angle theta; p(1.0/theta) q;", false),
        ("input angle theta; p(0.0*(1.0/theta)) q;", false),
    ] {
        assert_eq!(numeric_domains(&parse(body)).is_ok(), accepted, "{body}");
    }
    let source = parse("p(pi/(0.5+0.5)) q;");
    let mut work = MAX_WORK;
    block(&source.body, &mut work, 0).unwrap();
    let mut short = MAX_WORK - work - 1;
    assert!(block(&source.body, &mut short, 0).is_err());
    let mut work = MAX_WORK;
    assert!(block(&source.body, &mut work, MAX_DEPTH).is_err());
}
