//! Opt-in experiment: cargo run --release --example unitary_miter --
//! FORWARD.qasm ADJOINT_OF.qasm [--hps-only]
//! Uses full arbitrary-input/quantum-output semantics, NOT zero initialization.
use irene::{
    equivalence,
    frontend::{openqasm2, openqasm3},
    ir::{Program, unitary},
    symbolic::{ExecutionConfig, OutputSelection, execute},
    utils::load_openqasm_source,
};
use std::{path::Path, time::Instant};

fn parse(path: &str) -> Result<Program, String> {
    let source = load_openqasm_source(Path::new(path)).map_err(|e| e.to_string())?;
    match source.version.major {
        2 => openqasm2::parse_str(&source.text, path).map_err(|e| e.to_string()),
        3 => openqasm3::parse_str(&source.text, path).map_err(|e| e.to_string()),
        _ => Err("unsupported QASM version".into()),
    }
}

fn main() -> Result<(), String> {
    let args: Vec<_> = std::env::args().skip(1).collect();
    if !(args.len() == 2 || (args.len() == 3 && args[2] == "--hps-only")) {
        return Err("usage: unitary_miter FORWARD.qasm ADJOINT_OF.qasm [--hps-only]".into());
    }
    let start = Instant::now();
    let (forward, inverse) = (parse(&args[0])?, parse(&args[1])?);
    let (circuit, identity) = unitary::miter(&forward, &inverse).map_err(|e| e.to_string())?;
    eprintln!(
        "miter: forward={} inverse={} qubits={} gates={}",
        args[0],
        args[1],
        circuit.quantum_registers[0].width,
        circuit.operation_count()
    );
    if args.len() == 3 {
        let outputs = OutputSelection::new(
            circuit.quantum_registers.iter().flat_map(|r| {
                (0..r.width).map(move |index| irene::ir::Qubit {
                    register: r.id,
                    index,
                })
            }),
            [],
        );
        let hps = execute(&circuit, &ExecutionConfig::all_symbolic(), &outputs)
            .map_err(|e| e.to_string())?;
        for (i, c) in hps.components.iter().enumerate() {
            println!(
                "component={i} paths={} guards={} history={} phase_selectors={}",
                c.path_support.len(),
                c.guard.len(),
                c.output.history.len(),
                c.phase.selectors().count()
            );
        }
    } else {
        let interface = equivalence::EquivalenceConfig::positional(&circuit, &identity)
            .ok_or("miter and identity interfaces must have the same shape")?;
        let result =
            equivalence::analyze(&circuit, &identity, &interface).map_err(|e| e.to_string())?;
        println!("verdict={}", result.verdict);
    }
    println!("elapsed_seconds={:.6}", start.elapsed().as_secs_f64());
    Ok(())
}
