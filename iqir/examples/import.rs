//! Inspect frontend imports without linking IreneQ.
use std::process::ExitCode;

fn main() -> ExitCode {
    let mut total = 0;
    let mut failed = 0;
    for path in std::env::args_os().skip(1) {
        total += 1;
        match iqir::frontend::parse_file(&path) {
            Ok(p) => println!(
                "PASS {}: {} AST IDs, {} annotations, {} helpers",
                path.to_string_lossy(),
                p.ast_id_bound(),
                p.annotations.values().map(Vec::len).sum::<usize>(),
                p.spec_functions.len()
            ),
            Err(error) => {
                failed += 1;
                eprintln!("FAIL {}: {error}", path.to_string_lossy());
            }
        }
    }
    println!("{total} programs, {failed} failed");
    ExitCode::from(if total == 0 {
        2
    } else if failed > 0 {
        1
    } else {
        0
    })
}
