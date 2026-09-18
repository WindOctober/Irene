use irene::frontend::openqasm2;
use irene::ir::{Block, Gate, NumericExpr, Program, Qubit, StatementKind};
use irene::symbolic::{ExecutionConfig, OutputSelection, PhaseCoefficient, execute};
use num_rational::BigRational;

fn parse(body: &str) -> Program {
    openqasm2::parse_str(
        &format!("OPENQASM 2.0; include \"qelib1.inc\"; {body}"),
        "custom-gate-scope.qasm",
    )
    .unwrap()
}

fn applies<'a>(body: &'a Block, output: &mut Vec<(Gate, &'a [NumericExpr], &'a [Qubit])>) {
    for statement in &body.statements {
        match &statement.kind {
            StatementKind::Scope(body) => applies(body, output),
            StatementKind::Apply {
                gate,
                parameters,
                qubits,
            } => output.push((*gate, parameters, qubits)),
            _ => panic!("expected a unitary gate expansion"),
        }
    }
}

fn wire(program: &Program, name: &str, index: usize) -> Qubit {
    Qubit {
        register: program
            .quantum_registers
            .iter()
            .find(|r| r.name == name)
            .unwrap()
            .id,
        index,
    }
}

const DEFINITIONS: &str = "gate inner(theta) a,b { p(theta) a; cx a,b; }
     gate outer(theta) a,b { inner(theta/2) b,a; p(theta) a; }
     qreg q[2]; qreg r[2]; qreg theta[1];";

#[test]
fn empty_barriers_in_gate_bodies_remain_noops() {
    let program = parse("gate g a { barrier; x a; barrier a; } qreg q[1]; g q;");
    let mut actual = Vec::new();
    applies(&program.body, &mut actual);
    assert_eq!(actual.len(), 1);
    assert_eq!(actual[0].0, Gate::X);
    assert_eq!(actual[0].2, [wire(&program, "q", 0)]);
}

#[test]
fn nested_frames_restore_parameters_and_broadcast_real_register_cells() {
    let program = parse(&format!(
        "{DEFINITIONS} outer(pi/2) q,r; outer(pi/4) r[0],q[1];"
    ));
    let mut actual = Vec::new();
    applies(&program.body, &mut actual);
    let q0 = wire(&program, "q", 0);
    let q1 = wire(&program, "q", 1);
    let r0 = wire(&program, "r", 0);
    let r1 = wire(&program, "r", 1);
    let expected = [
        (Gate::P, vec![r0.clone()], Some((1, 8))),
        (Gate::Cx, vec![r0.clone(), q0.clone()], None),
        (Gate::P, vec![q0], Some((1, 4))),
        (Gate::P, vec![r1.clone()], Some((1, 8))),
        (Gate::Cx, vec![r1, q1.clone()], None),
        (Gate::P, vec![q1.clone()], Some((1, 4))),
        (Gate::P, vec![q1.clone()], Some((1, 16))),
        (Gate::Cx, vec![q1, r0.clone()], None),
        (Gate::P, vec![r0], Some((1, 8))),
    ];
    assert_eq!(actual.len(), expected.len());
    for ((gate, parameters, qubits), (expected_gate, expected_qubits, turns)) in
        actual.into_iter().zip(expected)
    {
        assert_eq!(gate, expected_gate);
        assert_eq!(qubits, expected_qubits);
        if let Some((n, d)) = turns {
            assert_eq!(parameters.len(), 1);
            assert_eq!(
                PhaseCoefficient::angle(parameters[0].clone(), BigRational::from_integer(1.into())),
                PhaseCoefficient::rational(BigRational::new(n.into(), d.into())),
            );
        } else {
            assert!(parameters.is_empty());
        }
    }
    let mut ids = Vec::new();
    program.visit_ast_ids(|id| ids.push(id.index()));
    ids.sort_unstable();
    assert_eq!(ids, (0..program.ast_id_bound()).collect::<Vec<_>>());
}

#[test]
fn nested_macro_and_explicit_inline_have_identical_symbolic_semantics() {
    let left = parse(&format!(
        "{DEFINITIONS} outer(pi/2) q,r; outer(pi/4) r[0],q[1];"
    ));
    let right = parse(&format!(
        "{DEFINITIONS}
         p(pi/4) r[0]; cx r[0],q[0]; p(pi/2) q[0];
         p(pi/4) r[1]; cx r[1],q[1]; p(pi/2) q[1];
         p(pi/8) q[1]; cx q[1],r[0]; p(pi/4) r[0];"
    ));
    let run = |p: &Program| {
        let qubits = p.quantum_registers.iter().flat_map(|r| {
            (0..r.width).map(|index| Qubit {
                register: r.id,
                index,
            })
        });
        execute(
            p,
            &ExecutionConfig::all_symbolic(),
            &OutputSelection::new(qubits, []),
        )
        .unwrap()
    };
    assert_eq!(run(&left), run(&right));
}

#[test]
fn scalar_operands_broadcast_without_allocating_or_capturing_registers() {
    let program = parse("gate g a,b { cx a,b; } qreg a[1]; qreg b[2]; g a[0],b;");
    assert_eq!(program.quantum_registers.len(), 2);
    let mut actual = Vec::new();
    applies(&program.body, &mut actual);
    assert_eq!(actual.len(), 2);
    for (index, (gate, parameters, qubits)) in actual.into_iter().enumerate() {
        assert_eq!(gate, Gate::Cx);
        assert!(parameters.is_empty());
        assert_eq!(qubits, [wire(&program, "a", 0), wire(&program, "b", index)]);
    }
}
