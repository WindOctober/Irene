use iqir::frontend::{self, ImportError};
use iqir::{Gate, StatementKind};

const QASM2: &str =
    "OPENQASM 2.0; include \"qelib1.inc\"; qreg q[1]; creg c[1]; h q[0]; measure q[0] -> c[0];";
const QASM3: &str = "OPENQASM 3.0; include \"stdgates.inc\"; qubit q; bit c; h q; c = measure q;";

#[test]
fn both_frontends_import_gates_and_measurement_without_irene() {
    for (source, major) in [(QASM2, 2), (QASM3, 3)] {
        let program = frontend::parse_str(source, "input.qasm").unwrap();
        assert_eq!(program.version.major, major);
        assert_eq!(program.quantum_registers[0].width, 1);
        assert!(program.body.statements.iter().any(|statement| {
            matches!(statement.kind, StatementKind::Apply { gate: Gate::H, .. })
        }));
        assert!(
            program
                .body
                .statements
                .iter()
                .any(|statement| { matches!(statement.kind, StatementKind::Measure { .. }) })
        );
        let direct = match major {
            2 => frontend::openqasm2::parse_str(source, "input.qasm").unwrap(),
            _ => frontend::openqasm3::parse_str(source, "input.qasm").unwrap(),
        };
        assert_eq!(program, direct);
    }
}

#[test]
fn import_reports_header_and_frontend_errors() {
    assert!(matches!(
        frontend::parse_str("qubit q;", "missing-header.qasm"),
        Err(ImportError::Source(_))
    ));
    assert!(matches!(
        frontend::parse_str("OPENQASM 4.0;", "unsupported.qasm"),
        Err(ImportError::UnsupportedVersion(_))
    ));
    for (source, major) in [
        ("OPENQASM 2.0; qreg q[1]; x missing;", 2),
        ("OPENQASM 3.0; qubit q; x missing;", 3),
    ] {
        let error = frontend::parse_str(source, "invalid.qasm").unwrap_err();
        assert!(matches!(
            (major, error),
            (2, ImportError::OpenQasm2(_)) | (3, ImportError::OpenQasm3(_))
        ));
    }
}

#[test]
fn file_import_returns_ir_and_preserves_read_errors() {
    use std::io::Write;
    use std::time::{SystemTime, UNIX_EPOCH};

    let path = std::env::temp_dir().join(format!(
        "iqir-import-{}-{}.qasm",
        std::process::id(),
        SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos(),
    ));
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(&path)
        .unwrap();
    file.write_all(QASM3.as_bytes()).unwrap();
    drop(file);
    let result = frontend::parse_file(&path);
    std::fs::remove_file(&path).unwrap();
    assert_eq!(
        result.unwrap(),
        frontend::parse_str(QASM3, "input.qasm").unwrap()
    );
    assert!(matches!(
        frontend::parse_file(&path),
        Err(ImportError::Source(
            frontend::OpenQasmSourceError::Read { .. }
        ))
    ));
}
