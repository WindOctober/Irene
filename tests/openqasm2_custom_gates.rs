use irene::frontend::openqasm2;
use irene::ir::{Block, Gate, StatementKind};

fn source(body: &str) -> String {
    format!("OPENQASM 2.0; include \"qelib1.inc\"; {body}")
}

fn gates(block: &Block, output: &mut Vec<(Gate, Vec<usize>)>) {
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::Apply { gate, qubits, .. } => {
                output.push((*gate, qubits.iter().map(|q| q.index).collect()))
            }
            StatementKind::Scope(body) => gates(body, output),
            StatementKind::If { then_branch, .. } => gates(then_branch, output),
            _ => {}
        }
    }
}

#[test]
fn nested_broadcast_and_conditional_expansion() {
    let program = openqasm2::parse_str(&source("gate pair a,b { h a; cx a,b; } gate wrap a,b { pair b,a; barrier a,b; } qreg q[2]; qreg r[2]; creg c[1]; if(c==0) wrap q,r;"), "test").unwrap();
    let mut actual = Vec::new();
    gates(&program.body, &mut actual);
    assert_eq!(actual.len(), 4);
    assert_eq!(
        actual.iter().map(|(_, q)| q.clone()).collect::<Vec<_>>(),
        vec![vec![0], vec![0, 0], vec![1], vec![1, 1]]
    );
    assert!(
        program
            .body
            .statements
            .iter()
            .any(|s| matches!(s.kind, StatementKind::If { .. }))
    );
}

#[test]
fn lexical_parameters_and_division_validation() {
    for body in [
        "gate inner(t) a { ry(t) a; } gate outer(t) a { inner(t/2) a; } qreg q[1]; outer(pi/2) q[0];",
        "gate empty a {} qreg q[1]; empty q;",
        "gate rot(theta) a { rz(theta) a; } qreg theta[1]; rot(pi/4) theta;",
    ] {
        openqasm2::parse_str(&source(body), "test").unwrap();
    }
    assert!(
        openqasm2::parse_str(
            &source("gate g(t) a { ry(1/t) a; } qreg q[1]; g(0) q;"),
            "test"
        )
        .is_err()
    );
}

#[test]
fn invalid_definitions_and_calls_are_rejected() {
    for body in [
        "gate g a { g a; }",
        "gate g a { later a; } gate later a { x a; }",
        "gate g(t,t) a { x a; }",
        "gate g(t) t { x t; }",
        "gate g a { reset a; }",
        "gate g a { measure a; }",
        "gate g a { qreg b[1]; }",
        "qreg q[1]; gate g a { x q; }",
        "gate g a { x a[0]; }",
        "gate g a { ry(missing) a; }",
        "gate g a { cx a,a; }",
        "gate g a { x a; } qreg q[1]; g(1) q;",
        "gate g a,b { cx a,b; } qreg q[1]; g q,q;",
        "gate g a,b { cx a,b; } qreg q[2]; qreg r[3]; g q,r;",
        "gate g a {} gate g b {}",
        "gate g(t,) a { ry(t) a; }",
        "gate g a, { x a; }",
        "gate g a { x a,; }",
        "gate g a { if(c==0) x a; }",
    ] {
        assert!(
            openqasm2::parse_str(&source(body), "test").is_err(),
            "accepted: {body}"
        );
    }
}

#[test]
fn explicit_ccz_definition_overrides_only_the_extension() {
    let program = openqasm2::parse_str(
        &source("gate ccz a,b,c { x a; } qreg q[3]; ccz q[0],q[1],q[2];"),
        "test",
    )
    .unwrap();
    let mut actual = Vec::new();
    gates(&program.body, &mut actual);
    assert_eq!(actual.len(), 1);
    assert_eq!(actual[0].1, vec![0]);
    assert!(openqasm2::parse_str(&source("gate h a { x a; }"), "test").is_err());
    assert!(openqasm2::parse_str(&source("gate ccz a {} gate ccz b {}"), "test").is_err());
}

#[test]
fn legal_acyclic_chain_has_no_fixed_depth_cap() {
    let mut body = String::from("gate g0 a { x a; }");
    for i in 1..70 {
        body.push_str(&format!("gate g{i} a {{ g{} a; }}", i - 1));
    }
    body.push_str("qreg q[1]; g69 q;");
    assert_eq!(
        openqasm2::parse_str(&source(&body), "test")
            .unwrap()
            .operation_count(),
        1
    );
}

#[test]
fn itertestq_custom_gate_examples_parse() {
    let base =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("benchmarks/itertestq/programs");
    if !base.is_dir() {
        return;
    } // External corpus is optional in a source checkout.
    for id in ["itertestq-0078", "itertestq-0157"] {
        for side in ["left", "right"] {
            let path = base.join(id).join(format!("{side}.qasm"));
            let text = std::fs::read_to_string(&path).unwrap();
            openqasm2::parse_str(&text, path.to_str().unwrap()).unwrap();
        }
    }
}

#[test]
fn nested_parameters_preserve_unitary_semantics() {
    use irene::equivalence::{
        Endpoint, EquivalenceConfig, InputPair, OutputPair, Verdict, analyze,
    };
    use irene::ir::Qubit;
    let left = openqasm2::parse_str(&source("gate inner(t) a,b { ry(t) a; cx a,b; } gate outer(t) a,b { inner(t/2) b,a; } qreg q[2]; outer(pi/2) q[0],q[1];"), "left").unwrap();
    let right =
        openqasm2::parse_str(&source("qreg q[2]; ry(pi/4) q[1]; cx q[1],q[0];"), "right").unwrap();
    let mut ids = Vec::new();
    left.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort_unstable();
    assert_eq!(ids, (0..left.ast_id_bound()).collect::<Vec<_>>());
    let endpoint = |p: &irene::ir::Program, index| {
        Endpoint::Quantum(Qubit {
            register: p.quantum_registers[0].id,
            index,
        })
    };
    let config = EquivalenceConfig {
        input_pairs: (0..2)
            .map(|i| InputPair {
                left: endpoint(&left, i),
                right: endpoint(&right, i),
            })
            .collect(),
        output_pairs: (0..2)
            .map(|i| OutputPair {
                left: endpoint(&left, i),
                right: endpoint(&right, i),
            })
            .collect(),
        ..Default::default()
    };
    assert_eq!(
        analyze(&left, &right, &config).unwrap().verdict,
        Verdict::Equivalent
    );
}

#[test]
fn scan_optional_itertestq_corpus() {
    let base =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("benchmarks/itertestq/programs");
    if !base.is_dir() {
        return;
    }
    let mut passed = 0;
    let mut errors = std::collections::BTreeMap::<String, usize>::new();
    for entry in std::fs::read_dir(base).unwrap() {
        let entry = entry.unwrap();
        let mut failure = None;
        for side in ["left", "right"] {
            let path = entry.path().join(format!("{side}.qasm"));
            let text = std::fs::read_to_string(path).unwrap();
            if let Err(error) = openqasm2::parse_str(&text, "corpus") {
                failure = Some(error.to_string());
                break;
            }
        }
        if let Some(error) = failure {
            *errors.entry(error).or_default() += 1;
        } else {
            passed += 1;
        }
    }
    eprintln!("IterTestQ parse pairs: {passed} passed; failures: {errors:?}");
    assert!(passed > 0, "the optional corpus must not be empty");
    assert!(errors.is_empty());
}
