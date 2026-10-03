use std::{
    path::PathBuf,
    process::Command,
    sync::atomic::{AtomicUsize, Ordering},
};

struct Sources(PathBuf);

impl Sources {
    fn new(left: &str, right: &str) -> Self {
        static SERIAL: AtomicUsize = AtomicUsize::new(0);
        let now = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "irene-stage1-cli-{}-{now}-{}",
            std::process::id(),
            SERIAL.fetch_add(1, Ordering::Relaxed)
        ));
        std::fs::create_dir(&path).unwrap();
        let sources = Self(path);
        std::fs::write(sources.0.join("left.qasm"), left).unwrap();
        std::fs::write(sources.0.join("right.qasm"), right).unwrap();
        sources
    }

    fn run(&self, strategy: &str) -> std::process::Output {
        Command::new(env!("CARGO_BIN_EXE_irene"))
            .arg(self.0.join("left.qasm"))
            .arg(self.0.join("right.qasm"))
            .env("IRENE_UNITARY_REWRITE", strategy)
            .output()
            .unwrap()
    }
}

impl Drop for Sources {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn qasm3(body: &str) -> String {
    format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit q; {body}")
}

#[test]
fn cli_reports_eq_neq_and_unknown_without_panicking() {
    for (left, right, expected) in [
        ("h q; h q;", "", "equivalent\n"),
        ("h q;", "", "not-equivalent\n"),
        (
            "input float[64] theta;",
            "input float[64] theta;",
            "unknown\n",
        ),
    ] {
        let sources = Sources::new(&qasm3(left), &qasm3(right));
        for strategy in ["off", "scan", "wire"] {
            let output = sources.run(strategy);
            assert!(
                output.status.success(),
                "{}",
                String::from_utf8_lossy(&output.stderr)
            );
            assert_eq!(String::from_utf8(output.stdout).unwrap(), expected);
        }
    }
}

#[test]
fn qasm2_cli_uses_the_same_validated_trace_entry() {
    let sources = Sources::new(
        "OPENQASM 2.0; include \"qelib1.inc\"; qreg q[1]; h q[0]; h q[0];",
        "OPENQASM 2.0; include \"qelib1.inc\"; qreg r[1];",
    );
    let output = sources.run("off");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "equivalent\n");
}

#[test]
fn cli_cannot_infer_incompatible_interfaces_and_rejects_invalid_strategy() {
    let sources = Sources::new(&qasm3(""), "OPENQASM 3.0; qubit[2] q;");
    let output = sources.run("off");
    assert!(output.status.success());
    assert_eq!(String::from_utf8(output.stdout).unwrap(), "unknown\n");

    let sources = Sources::new(&qasm3("h q; h q;"), &qasm3(""));
    let output = sources.run("invalid-stage1-test-strategy");
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    assert!(String::from_utf8_lossy(&output.stderr).contains("invalid equivalence configuration"));
}
