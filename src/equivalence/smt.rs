//! A small, process-based SMT solver portfolio.
//!
//! One definite SAT or UNSAT answer suffices. Non-answers do not veto it.
//! Contradictory definite answers are errors, never ordinary Unknown results.
//! The exact density encoder instead uses `run_solver` with Bitwuzla alone.

use std::io::{self, Read, Write};
use std::process::{Command, ExitStatus, Stdio};
use std::thread;
use std::time::{Duration, Instant};

#[cfg(unix)]
use std::os::unix::process::CommandExt;

/// Default solver-side and wall-clock limit used by [`run_portfolio`].
/// `IRENE_TUNE_SOLVER_SECONDS` overrides both limits together.
pub const SOLVER_TIMEOUT: Duration = Duration::from_secs(30);

pub(crate) fn solver_timeout() -> Duration {
    Duration::from_secs(super::tuning::limits().solver_seconds)
}

const POLL_INTERVAL: Duration = Duration::from_millis(5);
const MAX_RETAINED_OUTPUT_BYTES: usize = 1024 * 1024;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Solver {
    Z3,
    Cvc5,
    Bitwuzla,
}

impl Solver {
    pub const ALL: [Self; 3] = [Self::Z3, Self::Cvc5, Self::Bitwuzla];

    pub const fn executable(self) -> &'static str {
        match self {
            Self::Z3 => "z3",
            Self::Cvc5 => "cvc5",
            Self::Bitwuzla => "bitwuzla",
        }
    }

    const fn index(self) -> usize {
        match self {
            Self::Z3 => 0,
            Self::Cvc5 => 1,
            Self::Bitwuzla => 2,
        }
    }

    fn command(self) -> Command {
        let mut command = Command::new(self.executable());
        let millis = solver_timeout().as_millis().to_string();
        match self {
            // `-t` is Z3's per-query soft limit in milliseconds.
            Self::Z3 => {
                command.args(["-in", "-smt2"]).arg(format!("-t:{millis}"));
            }
            // cvc5 and Bitwuzla express their limits in milliseconds.
            Self::Cvc5 => {
                command
                    .args(["--lang=smt2", "--produce-models"])
                    .arg(format!("--tlimit-per={millis}"));
            }
            Self::Bitwuzla => {
                command.args(["--lang", "smt2", "-t", &millis, "-m"]);
            }
        }
        // A solver may launch helper processes. Giving each invocation its
        // own process group lets the wall-clock timeout stop the whole run,
        // including descendants that still hold stdout or stderr open.
        #[cfg(unix)]
        command.process_group(0);
        command
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SolverStatus {
    Sat,
    Unsat,
    Unknown,
    Timeout,
    Unavailable,
    Error,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SolverResult {
    pub solver: Solver,
    pub status: SolverStatus,
    pub stdout: String,
    pub stderr: String,
    pub duration: Duration,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PortfolioConsensus {
    Sat,
    Unsat,
    Inconclusive,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PortfolioResult {
    pub consensus: PortfolioConsensus,
    /// `run_portfolio` returns Z3, cvc5, Bitwuzla in that order.
    /// A designated-backend query (exact graph/density SMT) contains only Bitwuzla.
    pub results: Vec<SolverResult>,
}

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("SMT solver disagreement: SAT and UNSAT for the same query ({answers:?})")]
pub struct SolverDisagreement {
    pub answers: Vec<(Solver, SolverStatus)>,
}

/// Runs Z3, cvc5, and Bitwuzla concurrently on the same SMT-LIB2 input.
///
/// Each solver receives a 15-second CLI limit and is independently guarded by
/// a 15-second wall-clock limit. A satisfiable answer needs one solver and no
/// disagreement. The same policy applies to an unsatisfiable answer.
pub fn run_portfolio(smt2: &str) -> Result<PortfolioResult, SolverDisagreement> {
    let mut results = thread::scope(|scope| {
        let handles: Vec<_> = Solver::ALL
            .into_iter()
            .map(|solver| (solver, scope.spawn(move || run_solver(solver, smt2))))
            .collect();

        handles
            .into_iter()
            .map(|(solver, handle)| {
                handle.join().unwrap_or_else(|_| SolverResult {
                    solver,
                    status: SolverStatus::Error,
                    stdout: String::new(),
                    stderr: "solver worker panicked".to_owned(),
                    duration: Duration::ZERO,
                })
            })
            .collect::<Vec<_>>()
    });

    // Do not make callers depend on thread completion order.
    results.sort_by_key(|result| result.solver.index());
    Ok(PortfolioResult {
        consensus: consensus(&results)?,
        results,
    })
}

/// Accept either definite answer unless another result contradicts it.
/// Unknown, timeout, unavailable and error results do not invalidate a proof.
pub fn consensus(results: &[SolverResult]) -> Result<PortfolioConsensus, SolverDisagreement> {
    let has_sat = results
        .iter()
        .any(|result| result.status == SolverStatus::Sat);
    let has_unsat = results
        .iter()
        .any(|result| result.status == SolverStatus::Unsat);

    if has_sat && has_unsat {
        return Err(SolverDisagreement {
            answers: results.iter().map(|r| (r.solver, r.status)).collect(),
        });
    }
    if has_sat {
        return Ok(PortfolioConsensus::Sat);
    }

    if has_unsat {
        Ok(PortfolioConsensus::Unsat)
    } else {
        Ok(PortfolioConsensus::Inconclusive)
    }
}

pub(crate) fn run_solver(solver: Solver, smt2: &str) -> SolverResult {
    let started = Instant::now();
    let mut child = match solver
        .command()
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
    {
        Ok(child) => child,
        Err(error) => {
            let status = if error.kind() == io::ErrorKind::NotFound {
                SolverStatus::Unavailable
            } else {
                SolverStatus::Error
            };
            return SolverResult {
                solver,
                status,
                stdout: String::new(),
                stderr: error.to_string(),
                duration: started.elapsed(),
            };
        }
    };

    // Drain both output pipes concurrently. Waiting before draining can
    // deadlock once either OS pipe buffer fills.
    let stdout = child.stdout.take().expect("piped solver stdout");
    let stderr = child.stderr.take().expect("piped solver stderr");
    let stdout_reader = thread::spawn(move || read_all(stdout));
    let stderr_reader = thread::spawn(move || read_all(stderr));

    let mut stdin = child.stdin.take().expect("piped solver stdin");
    let input = smt2.as_bytes().to_vec();
    let stdin_writer = thread::spawn(move || {
        stdin.write_all(&input)?;
        // Closing stdin tells interactive solvers that the script is complete.
        drop(stdin);
        Ok::<(), io::Error>(())
    });

    let (exit_status, timed_out, wait_error) = wait_with_timeout(&mut child, started);
    let write_error = match stdin_writer.join() {
        Ok(Ok(())) => None,
        Ok(Err(error)) => Some(format!("failed to write SMT-LIB2 input: {error}")),
        Err(_) => Some("SMT-LIB2 input writer panicked".to_owned()),
    };
    let (stdout, stdout_error) = finish_reader(stdout_reader, "stdout");
    let (stderr, stderr_error) = finish_reader(stderr_reader, "stderr");

    let io_failed = write_error.is_some()
        || wait_error.is_some()
        || stdout_error.is_some()
        || stderr_error.is_some();

    let mut diagnostics = Vec::new();
    if !stderr.is_empty() {
        diagnostics.push(stderr);
    }
    diagnostics.extend(write_error);
    diagnostics.extend(wait_error);
    diagnostics.extend(stdout_error);
    diagnostics.extend(stderr_error);
    if let Some(exit_status) = exit_status.filter(|status| !status.success()) {
        diagnostics.push(format!("solver exited with status {exit_status}"));
    }
    let stderr = diagnostics.join("\n");

    let status = if timed_out {
        SolverStatus::Timeout
    } else if io_failed || exit_status.is_none_or(|status| !status.success()) {
        SolverStatus::Error
    } else {
        parse_status(&stdout).unwrap_or(SolverStatus::Error)
    };

    SolverResult {
        solver,
        status,
        stdout,
        stderr,
        duration: started.elapsed(),
    }
}

fn wait_with_timeout(
    child: &mut std::process::Child,
    started: Instant,
) -> (Option<ExitStatus>, bool, Option<String>) {
    loop {
        match child.try_wait() {
            Ok(Some(status)) => return (Some(status), false, None),
            Ok(None) if started.elapsed() < solver_timeout() => {
                let remaining = solver_timeout().saturating_sub(started.elapsed());
                thread::sleep(POLL_INTERVAL.min(remaining));
            }
            Ok(None) => {
                let kill_error = kill_solver(child).err();
                let reaped = child.wait();
                let mut errors = Vec::new();
                if let Some(error) = kill_error {
                    errors.push(format!("failed to kill timed-out solver: {error}"));
                }
                let status = match reaped {
                    Ok(status) => Some(status),
                    Err(error) => {
                        errors.push(format!("failed to reap timed-out solver: {error}"));
                        None
                    }
                };
                let error = (!errors.is_empty()).then(|| errors.join("; "));
                return (status, true, error);
            }
            Err(error) => {
                // `wait` is still required to reap the child when possible.
                let reap_error = child.wait().err();
                let message = match reap_error {
                    Some(reap_error) => {
                        format!(
                            "failed to poll solver: {error}; failed to reap solver: {reap_error}"
                        )
                    }
                    None => format!("failed to poll solver: {error}"),
                };
                return (None, false, Some(message));
            }
        }
    }
}

/// Stops the complete solver process tree on Unix. Other platforms retain the
/// direct-child behavior provided by [`std::process::Child::kill`].
fn kill_solver(child: &mut std::process::Child) -> io::Result<()> {
    #[cfg(unix)]
    {
        // `Solver::command` starts the child as leader of a fresh process
        // group, so its PID is also the group ID. A negative target asks
        // `kill(2)` to signal every process in that group.
        let result = unsafe { libc::kill(-(child.id() as libc::pid_t), libc::SIGKILL) };
        if result == 0 {
            Ok(())
        } else {
            Err(io::Error::last_os_error())
        }
    }
    #[cfg(not(unix))]
    {
        child.kill()
    }
}

#[derive(Debug)]
struct BoundedOutput {
    bytes: Vec<u8>,
    truncated: bool,
}

fn read_all(mut pipe: impl Read) -> io::Result<BoundedOutput> {
    let mut bytes = Vec::new();
    let mut truncated = false;
    let mut chunk = [0_u8; 8192];
    loop {
        let read = pipe.read(&mut chunk)?;
        if read == 0 {
            break;
        }

        let remaining = MAX_RETAINED_OUTPUT_BYTES.saturating_sub(bytes.len());
        let retained = remaining.min(read);
        bytes.extend_from_slice(&chunk[..retained]);
        truncated |= retained < read;
    }
    Ok(BoundedOutput { bytes, truncated })
}

fn finish_reader(
    reader: thread::JoinHandle<io::Result<BoundedOutput>>,
    stream: &str,
) -> (String, Option<String>) {
    match reader.join() {
        Ok(Ok(output)) => {
            let error = output.truncated.then(|| {
                format!(
                    "solver {stream} exceeded the {MAX_RETAINED_OUTPUT_BYTES}-byte capture limit"
                )
            });
            (String::from_utf8_lossy(&output.bytes).into_owned(), error)
        }
        Ok(Err(error)) => (
            String::new(),
            Some(format!("failed to read solver {stream}: {error}")),
        ),
        Err(_) => (
            String::new(),
            Some(format!("solver {stream} reader panicked")),
        ),
    }
}

fn parse_status(stdout: &str) -> Option<SolverStatus> {
    let mut status = None;
    for line in stdout.lines() {
        let line = line.trim();
        let parsed = match line {
            "sat" => Some(SolverStatus::Sat),
            "unsat" => Some(SolverStatus::Unsat),
            "unknown" => Some(SolverStatus::Unknown),
            _ => None,
        };

        if let Some(parsed) = parsed {
            if status.replace(parsed).is_some() {
                return None;
            }
        } else if is_malformed_status(line) || line.starts_with("(error") {
            return None;
        }
    }
    status
}

fn is_malformed_status(line: &str) -> bool {
    let first_word = line.split_ascii_whitespace().next().unwrap_or_default();
    let unparenthesized = line
        .strip_prefix('(')
        .and_then(|line| line.strip_suffix(')'))
        .unwrap_or(line);

    [line, first_word, unparenthesized]
        .into_iter()
        .any(|token| {
            matches!(
                token.to_ascii_lowercase().as_str(),
                "sat" | "unsat" | "unknown"
            )
        })
}

#[cfg(test)]
#[path = "../../tests/unit/equivalence/smt/tests.rs"]
mod tests;
