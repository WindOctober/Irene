use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::Parser;
use irene::ablation;
use irene::equivalence::{self, EquivalenceConfig, Verdict};
use irene::frontend::{openqasm2, openqasm3};
use irene::symbolic::representation_stats;
use irene::utils::load_openqasm_source;

#[derive(Debug, Parser)]
#[command(version, about)]
struct Cli {
    /// Left-hand OpenQASM program.
    left: PathBuf,
    /// Right-hand OpenQASM program.
    right: PathBuf,
    /// Disable optimization groups (comma-separated), or `all`. Overrides IRENE_ABLATE.
    #[arg(long)]
    ablate: Option<String>,
    /// Print effective ablation switches and entry-gate counts to stderr.
    #[arg(long)]
    ablation_report: bool,
    /// Write read-only HPS Boolean-graph snapshots to a NEW JSONL file; ANF analysis is offline.
    #[arg(long)]
    representation_stats: Option<PathBuf>,
    /// Observe every N retained statement/summary checkpoints (1 records every checkpoint).
    #[arg(long, default_value_t = 32)]
    representation_stats_every: usize,
}

fn main() -> ExitCode {
    let Cli {
        left,
        right,
        ablate,
        ablation_report,
        representation_stats,
        representation_stats_every,
    } = Cli::parse();
    let config = match ablate
        .as_deref()
        .map(ablation::Config::parse)
        .unwrap_or_else(ablation::Config::from_env)
    {
        Ok(config) => config,
        Err(error) => {
            eprintln!("{error}");
            return ExitCode::FAILURE;
        }
    };
    let statistics = match representation_stats
        .map(|path| {
            representation_stats::Session::start(
                path,
                representation_stats::Config {
                    every: representation_stats_every,
                    ..Default::default()
                },
            )
        })
        .transpose()
    {
        Ok(session) => session,
        Err(error) => {
            eprintln!("representation statistics: {error}");
            return ExitCode::FAILURE;
        }
    };
    let (result, report) = ablation::run(config, || check_equivalence(&left, &right));
    if let Some(session) = statistics {
        if let Err(error) = session.finish() {
            // Observation failure never changes the verification result.
            eprintln!("representation statistics incomplete: {error}");
        }
    }
    if ablation_report {
        eprint!("{report}");
    }
    match result {
        Ok(verdict) => {
            println!("{verdict}");
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}

fn check_equivalence(left_path: &Path, right_path: &Path) -> Result<Verdict, String> {
    let left_source = load_openqasm_source(left_path)
        .map_err(|error| format!("{}: {error}", left_path.display()))?;
    let right_source = load_openqasm_source(right_path)
        .map_err(|error| format!("{}: {error}", right_path.display()))?;

    let (left, right) = match (left_source.version.major, right_source.version.major) {
        (2, 2) => {
            let left =
                openqasm2::parse_str(&left_source.text, left_path.to_string_lossy().as_ref())
                    .map_err(|error| format!("{}: {error}", left_path.display()))?;
            let right =
                openqasm2::parse_str(&right_source.text, right_path.to_string_lossy().as_ref())
                    .map_err(|error| format!("{}: {error}", right_path.display()))?;
            (left, right)
        }
        (3, 3) => {
            let left =
                openqasm3::parse_str(&left_source.text, left_path.to_string_lossy().as_ref())
                    .map_err(|error| format!("{}: {error}", left_path.display()))?;
            let right =
                openqasm3::parse_str(&right_source.text, right_path.to_string_lossy().as_ref())
                    .map_err(|error| format!("{}: {error}", right_path.display()))?;
            (left, right)
        }
        (left, right) => {
            return Err(format!(
                "both programs must use OpenQASM 2.x or both must use OpenQASM 3.x; found {left}.x and {right}.x"
            ));
        }
    };

    let Some(interface) = EquivalenceConfig::positional(&left, &right) else {
        return Ok(Verdict::Unknown);
    };
    equivalence::analyze(&left, &right, &interface)
        .map(|analysis| analysis.verdict)
        .map_err(|error| error.to_string())
}
