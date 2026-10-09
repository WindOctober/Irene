use super::*;
use crate::frontend::openqasm3;
use crate::symbolic::PhaseCoefficient;
use std::cell::RefCell;
use std::collections::VecDeque;

fn fixture() -> PreparedComparison {
    let program = openqasm3::parse_str(
        "OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q;",
        "deterministic.qasm",
    )
    .unwrap();
    let config = EquivalenceConfig::positional(&program, &program).unwrap();
    prepare_comparison(&program, &program, &config).unwrap()
}

fn phase(p: &mut PreparedComparison) {
    let x = p.left.terminals[0].outputs[0].value.clone();
    p.left.hps.components[0].phase.add_boolean(
        &x,
        PhaseCoefficient::rational(BigRational::new(1.into(), 2.into())),
    );
}

fn run(p: &PreparedComparison, answers: &[PortfolioConsensus]) -> Option<Analysis> {
    let uncached = run_with_snapshots(p, answers, None);
    if p.left.hps.components.len() == 1 && p.right.hps.components.len() == 1 {
        let cached = run_with_snapshots(
            p,
            answers,
            Some((complete_snapshot(&p.left), complete_snapshot(&p.right))),
        );
        assert_eq!(
            cached, uncached,
            "snapshot reuse must preserve all proof obligations"
        );
    }
    uncached
}

fn run_with_snapshots(
    p: &PreparedComparison,
    answers: &[PortfolioConsensus],
    snapshots: Option<(HybridPathSum, HybridPathSum)>,
) -> Option<Analysis> {
    let queue = RefCell::new(VecDeque::from(answers.to_vec()));
    let answer = || {
        Ok(PortfolioResult {
            consensus: queue
                .borrow_mut()
                .pop_front()
                .expect("unexpected solver call"),
            results: vec![],
        })
    };
    let result = compare_with(p, (0, 0), snapshots, |_, _| answer(), |_| answer());
    assert!(queue.borrow().is_empty(), "missing required solver call");
    result.map(Result::unwrap)
}

#[test]
fn syntactically_equal_outputs_and_phase_need_no_solver() {
    let p = fixture();
    assert_eq!(run(&p, &[]).unwrap().verdict, Verdict::Equivalent);
}

#[test]
fn output_sat_is_negative_even_without_optional_model() {
    let mut p = fixture();
    p.right.terminals[0].outputs[0].value = BooleanPolynomial::zero();
    let a = run(&p, &[PortfolioConsensus::Sat]).unwrap();
    assert_eq!(a.evidence, Evidence::OutputCounterexample);
    assert_eq!(a.verdict, Verdict::NotEquivalent);
    assert!(a.counterexample.is_none());
    assert_eq!(a.solver_queries.len(), 1);
    assert_eq!(
        run(&p, &[PortfolioConsensus::Inconclusive])
            .unwrap()
            .verdict,
        Verdict::Unknown
    );
}

#[test]
fn output_unsat_does_not_skip_phase_obligation() {
    let mut p = fixture();
    phase(&mut p);
    // Stub only the solver boundary to verify orchestration, not formula truth.
    p.right.terminals[0].outputs[0].value = BooleanPolynomial::zero();
    let a = run(&p, &[PortfolioConsensus::Unsat, PortfolioConsensus::Sat]).unwrap();
    assert_eq!(a.evidence, Evidence::PhaseCounterexample);
    assert_eq!(a.solver_queries.len(), 2);
}

#[test]
fn phase_results_have_distinct_verdicts() {
    let mut p = fixture();
    phase(&mut p);
    for (answer, verdict) in [
        (PortfolioConsensus::Sat, Verdict::NotEquivalent),
        (PortfolioConsensus::Unsat, Verdict::Equivalent),
        (PortfolioConsensus::Inconclusive, Verdict::Unknown),
    ] {
        let a = run(&p, &[answer]).unwrap();
        assert_eq!(a.verdict, verdict);
        assert_eq!(a.solver_queries.len(), 1);
    }
}

#[test]
fn injectivity_sat_is_not_program_inequivalence() {
    let mut p = fixture();
    phase(&mut p);
    for side in [&mut p.left, &mut p.right] {
        side.terminals[0].outputs[1].value = BooleanPolynomial::zero();
    }
    for answer in [PortfolioConsensus::Sat, PortfolioConsensus::Inconclusive] {
        let a = run(&p, &[answer]).unwrap();
        assert_eq!(a.verdict, Verdict::Unknown);
        assert_eq!(a.evidence, Evidence::SolverInconclusive);
    }
    let a = run(&p, &[PortfolioConsensus::Unsat, PortfolioConsensus::Sat]).unwrap();
    assert_eq!(a.evidence, Evidence::PhaseCounterexample);
    assert_eq!(a.solver_queries.len(), 2);
}

#[test]
fn refusal_boundaries_do_not_query_or_panic() {
    let original = fixture();
    let mut p = original.clone();
    p.left.hps.components[0].scalar = Scalar::Rational(BigRational::from_integer(2.into()));
    assert!(run(&p, &[]).is_none());
    let mut p = original.clone();
    p.left.hps.components.push(p.left.hps.components[0].clone());
    assert!(run(&p, &[]).is_none());
    let mut p = original;
    phase(&mut p);
    p.left.hps.components[0]
        .output
        .history
        .push(HistoryEntry::Discard {
            value: p.left.terminals[0].outputs[0].value.clone(),
        });
    assert!(run(&p, &[]).is_none());
}

#[test]
fn classical_phase_erasure_preserves_remaining_snapshot_obligations() {
    let mut p = fixture();
    phase(&mut p);
    p.output_kinds.fill(PreparedOutputKind::Classical);
    for side in [&mut p.left, &mut p.right] {
        for output in &mut side.terminals[0].outputs {
            output.kind = PreparedOutputKind::Classical;
        }
    }
    assert_eq!(run(&p, &[]).unwrap().verdict, Verdict::Equivalent);
    // Unobserved history must not be discarded by merely clearing phase.
    p.left.terminals[0].outputs.pop();
    p.right.terminals[0].outputs.pop();
    p.output_kinds.pop();
    let value = p.left.hps.input.quantum.values().nth(1).unwrap().clone();
    p.left.hps.components[0]
        .output
        .history
        .push(HistoryEntry::Discard { value });
    assert!(run(&p, &[]).is_none());
}

#[test]
fn solver_conflict_propagates_as_error() {
    let mut p = fixture();
    phase(&mut p);
    let error = SolverDisagreement { answers: vec![] };
    let result = compare_with(
        &p,
        (0, 0),
        None,
        |_, _| Err(error.clone()),
        |_| panic!("unexpected injectivity query"),
    );
    assert_eq!(result.unwrap().unwrap_err(), error);
}

#[test]
#[ignore = "requires installed SMT solvers"]
fn real_solver_checks_parsed_output_and_phase_differences() {
    let mut p = fixture();
    phase(&mut p);
    let a = compare(&p, (0, 0), None).unwrap().unwrap();
    assert_eq!(a.evidence, Evidence::PhaseCounterexample);
    assert!(a.counterexample.unwrap().bra_inputs.is_some());
    let mut p = fixture();
    p.right.terminals[0].outputs[0].value = BooleanPolynomial::zero();
    let a = compare(&p, (0, 0), None).unwrap().unwrap();
    assert_eq!(a.evidence, Evidence::OutputCounterexample);
    assert!(a.counterexample.is_some());
}

#[test]
#[ignore = "requires installed SMT solvers"]
fn public_analysis_reaches_nonlinear_output_query() {
    let parse = |body: &str| {
        openqasm3::parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[3] q; bit c = 0; {body}"),
            "deterministic-api.qasm",
        )
        .unwrap()
    };
    let left = parse("ccx q[0],q[1],q[2];");
    let right = parse("");
    let mut config = EquivalenceConfig::positional(&left, &right).unwrap();
    // Retain one quantum output and the classical observation, bypassing
    // the full-unitary trace route; the CCX output is not affine.
    config.output_pairs.retain(|pair| match &pair.left {
        Endpoint::Quantum(q) => q.index == 2,
        Endpoint::Classical(_) => true,
    });
    let a = analyze(&left, &right, &config).unwrap();
    assert_eq!(a.evidence, Evidence::OutputCounterexample);
    assert_eq!(a.verdict, Verdict::NotEquivalent);
    assert!(!a.solver_queries.is_empty());
    assert!(a.counterexample.is_some());
}
