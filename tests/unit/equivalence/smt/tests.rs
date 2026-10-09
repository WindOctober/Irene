use super::*;

fn result(solver: Solver, status: SolverStatus) -> SolverResult {
    SolverResult {
        solver,
        status,
        stdout: String::new(),
        stderr: String::new(),
        duration: Duration::ZERO,
    }
}

#[test]
fn solver_commands_use_the_same_budget_as_the_watchdog() {
    let millis = solver_timeout().as_millis().to_string();
    for (solver, flag) in [
        (Solver::Z3, format!("-t:{millis}")),
        (Solver::Cvc5, format!("--tlimit-per={millis}")),
        (Solver::Bitwuzla, millis.clone()),
    ] {
        assert!(solver.command().get_args().any(|a| a == flag.as_str()));
    }
}

#[test]
fn parser_accepts_only_standalone_status_lines() {
    assert_eq!(
        parse_status("success\n sat \n(model)\n"),
        Some(SolverStatus::Sat)
    );
    assert_eq!(parse_status("\r\nunsat\r\n"), Some(SolverStatus::Unsat));
    assert_eq!(parse_status("unknown\n"), Some(SolverStatus::Unknown));
    assert_eq!(parse_status("(error \"unsat core unavailable\")\n"), None);
    assert_eq!(parse_status("satisfiable\n"), None);
}

#[test]
fn parser_rejects_duplicate_contradictory_and_malformed_statuses() {
    assert_eq!(parse_status("sat\nsat\n"), None);
    assert_eq!(parse_status("sat\nunsat\n"), None);
    assert_eq!(parse_status("unknown\nunsat\n"), None);
    assert_eq!(parse_status("SAT\n"), None);
    assert_eq!(parse_status("unsat trailing-noise\n"), None);
    assert_eq!(parse_status("(unknown)\n"), None);
    assert_eq!(parse_status("sat\n(error \"resource limit\")\n"), None);
}

#[test]
fn parser_allows_non_status_output_around_one_status() {
    assert_eq!(
        parse_status("success\n; solver banner\nsat\n((x #b1))\n"),
        Some(SolverStatus::Sat)
    );
}

#[test]
fn consensus_accepts_any_definite_answer_unless_contradicted() {
    let statuses = [
        SolverStatus::Sat,
        SolverStatus::Unsat,
        SolverStatus::Unknown,
        SolverStatus::Timeout,
        SolverStatus::Unavailable,
        SolverStatus::Error,
    ];
    // Every combination, including UNSAT/timeout/UNSAT and a sole answer.
    for a in statuses {
        for b in statuses {
            for c in statuses {
                let answers = [a, b, c];
                let results = Solver::ALL
                    .into_iter()
                    .zip(answers)
                    .map(|(solver, status)| result(solver, status))
                    .collect::<Vec<_>>();
                if answers.contains(&SolverStatus::Sat)
                    && answers.contains(&SolverStatus::Unsat)
                {
                    let error = consensus(&results).expect_err("conflict must be an error");
                    assert_eq!(error.answers.len(), 3);
                } else {
                    let expected = if answers.contains(&SolverStatus::Sat) {
                        PortfolioConsensus::Sat
                    } else if answers.contains(&SolverStatus::Unsat) {
                        PortfolioConsensus::Unsat
                    } else {
                        PortfolioConsensus::Inconclusive
                    };
                    assert_eq!(consensus(&results), Ok(expected), "{answers:?}");
                }
            }
        }
    }
    for solver in Solver::ALL {
        assert_eq!(
            consensus(&[result(solver, SolverStatus::Sat)]),
            Ok(PortfolioConsensus::Sat)
        );
        assert_eq!(
            consensus(&[result(solver, SolverStatus::Unsat)]),
            Ok(PortfolioConsensus::Unsat)
        );
    }
    assert_eq!(consensus(&[]), Ok(PortfolioConsensus::Inconclusive));
}

#[test]
fn repeated_backend_answers_also_detect_contradictions() {
    let same = [
        result(Solver::Bitwuzla, SolverStatus::Unsat),
        result(Solver::Bitwuzla, SolverStatus::Unsat),
    ];
    assert_eq!(consensus(&same), Ok(PortfolioConsensus::Unsat));
    let conflicting = [
        result(Solver::Bitwuzla, SolverStatus::Sat),
        result(Solver::Bitwuzla, SolverStatus::Unsat),
    ];
    let error = consensus(&conflicting).expect_err("same-query replay conflict");
    let surfaced = super::super::InterfaceError::from(error);
    assert!(surfaced.to_string().contains("SAT and UNSAT"));
}

#[test]
fn solver_output_capture_is_bounded() {
    let input = vec![b'x'; MAX_RETAINED_OUTPUT_BYTES + 17];
    let output = read_all(input.as_slice()).expect("in-memory read succeeds");
    assert_eq!(output.bytes.len(), MAX_RETAINED_OUTPUT_BYTES);
    assert!(output.truncated);
}

#[test]
#[ignore = "requires at least one of z3, cvc5, or bitwuzla installed"]
fn installed_solvers_accept_a_small_smt2_query() {
    let query = "\
(set-logic QF_BV)\n\
(declare-fun x () Bool)\n\
(assert x)\n\
(check-sat)\n\
(get-value (x))\n";
    let portfolio = run_portfolio(query).expect("installed solvers must not contradict");
    let available = portfolio
        .results
        .iter()
        .filter(|result| result.status != SolverStatus::Unavailable)
        .count();
    assert!(
        available > 0,
        "installed solver integration test requires z3, cvc5, or bitwuzla"
    );

    for result in portfolio.results {
        if result.status == SolverStatus::Unavailable {
            continue;
        }
        assert_eq!(
            result.status,
            SolverStatus::Sat,
            "{} failed: stdout={:?}, stderr={:?}",
            result.solver.executable(),
            result.stdout,
            result.stderr
        );
        assert!(
            result.stdout.contains("true"),
            "{} did not return the requested assignment: {:?}",
            result.solver.executable(),
            result.stdout
        );
    }
}
