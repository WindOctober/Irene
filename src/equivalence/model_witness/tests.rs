use super::*;
use super::super::smt::{PortfolioConsensus, Solver, SolverResult};
use num_rational::BigRational;
fn q(i: usize) -> Qubit { Qubit { register: crate::ir::SymbolId(9), index: i } }
fn x(i: usize) -> BooleanPolynomial { BooleanPolynomial::variable(Variable::Input(q(i))) }
fn sat(stdout: &str) -> PortfolioResult {
    PortfolioResult { consensus: PortfolioConsensus::Sat, results: vec![SolverResult {
        solver: Solver::Bitwuzla, status: SolverStatus::Sat, stdout: stdout.into(),
        stderr: String::new(), duration: std::time::Duration::ZERO,
    }] }
}
#[test]
fn fse_parser_uses_first_named_value_and_accepts_loose_token_layout() {
    assert_eq!(parse_boolean_values("sat ((x1 false) (x0 true))", 2, "x"), Some(vec![true, false]));
    assert_eq!(parse_boolean_values("((x0 true) (x0 false))", 1, "x"), Some(vec![true]));
    assert_eq!(parse_boolean_values("sat ((x0 true)) ((x1 false))", 2, "x"), Some(vec![true, false]));
    assert_eq!(parse_boolean_values("sat ((x0 true))", 2, "x"), None);
    assert_eq!(parse_boolean_values("((x0 0))", 1, "x"), None);
    assert_eq!(parse_boolean_values("", 0, "x"), Some(vec![]));
}
#[test]
fn fse_missing_boolean_bindings_default_to_false() {
    assert!(!evaluate_boolean(&x(0), &BTreeMap::new()));
    let map = [(q(0), 1), (q(1), 0)].into();
    let b = input_bindings(&[true, false], &map);
    assert!(!b[&Variable::Input(q(0))]);
    assert!(b[&Variable::Input(q(1))]);
}
#[test]
fn output_models_are_still_reevaluated() {
    let pos = [(q(0), 0)].into();
    assert_eq!(validated_model(&sat("sat ((x0 false))"), &[x(0)], &pos, "x"), None);
    assert_eq!(validated_model(&sat("sat ((x0 true))"), &[x(0)], &pos, "x"), Some(vec![true]));
    let mut p = sat("sat ((x0 true))");
    p.consensus = PortfolioConsensus::Inconclusive;
    // FSE filters the individual records; callers establish consensus.
    assert_eq!(validated_model(&p, &[x(0)], &pos, "x"), Some(vec![true]));
    p.results[0].status = SolverStatus::Unknown;
    assert_eq!(validated_model(&p, &[x(0)], &pos, "x"), None);
}
#[test]
fn phase_models_use_two_assignments_and_exact_turns() {
    let pos = [(q(0), 0)].into();
    let phase = [(x(0), BigRational::new(1.into(), 2.into()))].into();
    assert_eq!(validated_phase_model(&sat("sat ((x0 false) (z0 true))"), &phase, &pos), Some((vec![false], vec![true])));
    assert_eq!(validated_phase_model(&sat("sat ((x0 true) (z0 true))"), &phase, &pos), None);
}
