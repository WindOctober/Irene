use irene::{
    ablation, equivalence,
    frontend::openqasm3,
    symbolic::representation_stats::{Config, Session},
};
use std::sync::atomic::{AtomicUsize, Ordering};

fn path() -> std::path::PathBuf {
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    std::env::temp_dir().join(format!(
        "irene-representation-test-{}-{}.jsonl",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ))
}

#[test]
fn observation_preserves_verdict_evidence_and_ablation_counts() {
    let parse = |body: &str| {
        openqasm3::parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
            "test.qasm",
        )
        .unwrap()
    };
    let left = parse("qubit q; bit c; h q; c = measure q; if (c) { x q; } c = false;");
    let right = parse("qubit q; bit c; reset q; c = false;");
    let config = equivalence::EquivalenceConfig::positional(&left, &right).unwrap();
    let run = || {
        ablation::run(ablation::Config::default(), || {
            equivalence::analyze(&left, &right, &config).unwrap()
        })
    };
    let (normal, normal_ablation) = run();
    let path = path();
    let session = Session::start(
        &path,
        Config {
            every: 1,
            ..Config::default()
        },
    )
    .unwrap();
    let (observed, observed_ablation) = run();
    session.finish().unwrap();
    assert_eq!(normal.verdict, observed.verdict);
    assert_eq!(normal.evidence, observed.evidence);
    assert_eq!(normal_ablation, observed_ablation);
    let trace = std::fs::read_to_string(&path).unwrap();
    assert!(trace.contains("\"type\":\"snapshot\""));
    assert!(trace.lines().last().unwrap().contains("\"type\":\"end\""));
    // No implicit overwrite, and scope restoration allows a subsequent session.
    assert!(Session::start(&path, Config::default()).is_err());
    std::fs::remove_file(path).unwrap();
}

#[test]
fn drop_and_sampling_limits_are_explicit() {
    let path = path();
    let session = Session::start(&path, Config::default()).unwrap();
    assert!(Session::start(path.with_extension("nested"), Config::default()).is_err());
    drop(session);
    let trace = std::fs::read_to_string(&path).unwrap();
    assert!(!trace.contains("\"type\":\"end\""));
    std::fs::remove_file(path).unwrap();
}

#[test]
fn rotation_scalar_conditions_are_observed_without_changing_hps() {
    use irene::ir::Qubit;
    use irene::symbolic::{ExecutionConfig, OutputSelection, execute};
    let program = openqasm3::parse_str(
        "OPENQASM 3.0; include \"stdgates.inc\"; qubit q; rx(pi/7) q;",
        "rotation.qasm",
    )
    .unwrap();
    let outputs = OutputSelection::new(
        [Qubit {
            register: program.quantum_registers[0].id,
            index: 0,
        }],
        [],
    );
    let run = || execute(&program, &ExecutionConfig::all_symbolic(), &outputs).unwrap();
    let normal = run();
    let path = path();
    let session = Session::start(
        &path,
        Config {
            every: 1,
            ..Config::default()
        },
    )
    .unwrap();
    assert_eq!(normal, run());
    session.finish().unwrap();
    let trace = std::fs::read_to_string(&path).unwrap();
    assert!(trace.contains("\"stage\":\"hps_final\""));
    assert!(trace.contains("\"xag_edges\":"));
    std::fs::remove_file(path).unwrap();
}
