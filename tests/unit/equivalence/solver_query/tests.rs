use super::*;
use std::time::Duration;

fn observation(status: SolverStatus) -> SolverResult {
    SolverResult {
        solver: Solver::Bitwuzla,
        status,
        stdout: String::new(),
        stderr: format!("diagnostic {status:?}"),
        duration: Duration::from_millis(3),
    }
}
fn portfolio(status: SolverStatus) -> PortfolioResult {
    let result = observation(status);
    PortfolioResult {
        consensus: smt::consensus(std::slice::from_ref(&result)).unwrap(),
        results: vec![result],
    }
}
const STATUSES: [SolverStatus; 6] = [
    SolverStatus::Sat,
    SolverStatus::Unsat,
    SolverStatus::Unknown,
    SolverStatus::Timeout,
    SolverStatus::Unavailable,
    SolverStatus::Error,
];

#[test]
fn designated_definite_answer_does_not_launch_fallback() {
    for status in [SolverStatus::Sat, SolverStatus::Unsat] {
        let result = run_graph_query_with(
            "query",
            |solver, query| {
                assert_eq!(solver, Solver::Bitwuzla);
                assert_eq!(query, "query");
                observation(status)
            },
            |_| panic!("must not invoke fallback after a definite answer"),
        )
        .unwrap();
        assert_eq!(result, portfolio(status));
    }
}

#[test]
fn nonanswers_fall_back_on_the_identical_query_and_keep_diagnostics() {
    for status in [
        SolverStatus::Unknown,
        SolverStatus::Timeout,
        SolverStatus::Unavailable,
        SolverStatus::Error,
    ] {
        for later in STATUSES {
            let result = run_graph_query_with(
                "query",
                |_, _| observation(status),
                |query| {
                    assert_eq!(query, "query");
                    Ok(portfolio(later))
                },
            )
            .unwrap();
            assert_eq!(result.consensus, portfolio(later).consensus);
            assert_eq!(result.results[0].duration, Duration::from_millis(6));
            assert!(
                result.results[0]
                    .stderr
                    .contains(&format!("initial graph attempt: {status:?}"))
            );
            assert!(
                result.results[0]
                    .stderr
                    .contains(&format!("diagnostic {later:?}"))
            );
        }
    }
}

#[test]
fn conflicting_fallback_answers_remain_an_error() {
    let error = smt::consensus(&[
        observation(SolverStatus::Sat),
        observation(SolverStatus::Unsat),
    ])
    .unwrap_err();
    assert_eq!(
        run_graph_query_with(
            "query",
            |_, _| observation(SolverStatus::Timeout),
            |_| Err(error.clone())
        ),
        Err(error)
    );
}

#[test]
fn get_value_is_requested_only_after_sat_and_only_when_values_are_needed() {
    let query = "(set-logic QF_BV)\n(check-sat)\n";
    for status in STATUSES {
        let mut calls = Vec::new();
        let result = run_miter_with(query, &["x0".into(), "z0".into()], |q| {
            calls.push(q.to_owned());
            Ok(portfolio(status))
        })
        .unwrap();
        assert_eq!(result.consensus, portfolio(status).consensus);
        assert_eq!(calls[0], query);
        if status == SolverStatus::Sat {
            assert_eq!(
                calls,
                vec![query.to_owned(), format!("{query}(get-value (x0 z0))\n")]
            );
        } else {
            assert_eq!(calls.len(), 1);
        }
    }
    let mut calls = 0;
    run_miter_with(query, &[], |_| {
        calls += 1;
        Ok(portfolio(SolverStatus::Sat))
    })
    .unwrap();
    assert_eq!(calls, 1);
}

#[test]
fn optional_model_failure_preserves_sat_but_opposite_answer_is_an_error() {
    for status in STATUSES {
        let mut calls = 0;
        let result = run_miter_with("(check-sat)\n", &["x0".into()], |_| {
            calls += 1;
            Ok(portfolio(if calls == 1 {
                SolverStatus::Sat
            } else {
                status
            }))
        });
        assert_eq!(calls, 2);
        if status == SolverStatus::Unsat {
            assert!(result.is_err());
        } else {
            let result = result.unwrap();
            assert_eq!(result.consensus, PortfolioConsensus::Sat);
            assert_eq!(result.results.len(), 2);
            assert_eq!(result.results[0].status, status);
            assert_eq!(result.results[1].status, SolverStatus::Sat);
        }
    }
}

#[test]
fn all_same_query_status_pairs_obey_consensus_without_majority_voting() {
    for first in STATUSES {
        for second in STATUSES {
            let result = combine_same_query_results(portfolio(first), portfolio(second));
            let statuses = [first, second];
            let sat = statuses.contains(&SolverStatus::Sat);
            let unsat = statuses.contains(&SolverStatus::Unsat);
            if sat && unsat {
                assert!(result.is_err());
            } else {
                let result = result.unwrap();
                assert_eq!(
                    result.consensus,
                    if sat {
                        PortfolioConsensus::Sat
                    } else if unsat {
                        PortfolioConsensus::Unsat
                    } else {
                        PortfolioConsensus::Inconclusive
                    }
                );
                assert_eq!(
                    result.results,
                    vec![observation(second), observation(first)]
                );
            }
        }
    }
    assert!(
        smt::consensus(&[
            observation(SolverStatus::Sat),
            observation(SolverStatus::Sat),
            observation(SolverStatus::Unsat)
        ])
        .is_err()
    );
}

#[test]
fn conflict_while_getting_model_is_not_silently_swallowed() {
    let error = smt::consensus(&[
        observation(SolverStatus::Sat),
        observation(SolverStatus::Unsat),
    ])
    .unwrap_err();
    let mut calls = 0;
    let result = run_miter_with("(check-sat)\n", &["x0".into()], |_| {
        calls += 1;
        if calls == 1 {
            Ok(portfolio(SolverStatus::Sat))
        } else {
            Err(error.clone())
        }
    });
    assert_eq!(result, Err(error));
}

#[test]
#[ignore = "requires external SMT executables; exercises the process-based adapter"]
fn actual_solver_roundtrip_obtains_sat_values_and_does_not_query_unsat_values() {
    let sat = "(set-logic QF_BV)\n(set-option :produce-models true)\n(declare-fun x0 () Bool)\n(assert x0)\n(check-sat)\n";
    let result = run_miter(sat, &["x0".into()]).unwrap();
    assert_eq!(result.consensus, PortfolioConsensus::Sat);
    assert!(result.results.iter().any(|r| r.status == SolverStatus::Sat
        && r.stdout.contains("x0")
        && r.stdout.contains("true")));
    let unsat = "(set-logic QF_BV)\n(assert false)\n(check-sat)\n";
    let result = run_miter(unsat, &["x0".into()]).unwrap();
    assert_eq!(result.consensus, PortfolioConsensus::Unsat);
    assert!(result.results.iter().all(|r| !r.stdout.contains("(error")));
}
