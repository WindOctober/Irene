use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::Parser;
use irene::equivalence::{self, Verdict};
use irene::frontend::openqasm3;
use irene::utils::load_openqasm_source;

#[derive(Debug, Parser)]
#[command(version, about)]
struct Cli {
    /// Left-hand OpenQASM program.
    left: PathBuf,
    /// Right-hand OpenQASM program.
    right: PathBuf,
}

fn main() -> ExitCode {
    let Cli { left, right } = Cli::parse();
    match check_equivalence(&left, &right) {
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
        (2, 2) => todo!("OpenQASM 2 frontend"),
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

    Ok(equivalence::analyze(&left, &right))
}
