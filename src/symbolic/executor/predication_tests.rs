use super::*;
use crate::ir::SymbolId;

// Include independent ket/bra inputs and all output off-diagonals, rather
// than testing only computational-basis output probabilities.
fn run(body: &str, live_result: bool, before_final_simplify: bool) -> HybridPathSum {
    run_with_scope(body, live_result, before_final_simplify, false)
}

fn run_with_scope(
    body: &str,
    live_result: bool,
    before_final_simplify: bool,
    wrap_scope: bool,
) -> HybridPathSum {
    let source = format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; bit c; {body}");
    let mut program = crate::frontend::openqasm3::parse_str(&source, "predication.qasm").unwrap();
    if wrap_scope {
        let mut ids = AstIdGenerator::starting_at(program.ast_id_bound());
        for statement in &mut program.body.statements {
            if let StatementKind::If { then_branch, .. } = &mut statement.kind {
                let first = then_branch.statements.remove(0);
                let inner = ids.node(crate::ir::BlockData {
                    statements: vec![first],
                    ..Default::default()
                });
                then_branch
                    .statements
                    .insert(0, ids.node(StatementKind::Scope(inner)));
            }
        }
    }
    let register = program.quantum_registers[0].id;
    let classical = ClassicalBit {
        register: program.classical_registers[0].id,
        index: 0,
    };
    let selection = OutputSelection::new(
        [Qubit { register, index: 1 }],
        if live_result { vec![classical] } else { vec![] },
    );
    let mut hps = if before_final_simplify {
        let plan = slice::build_slice_plan(&program, &selection).unwrap();
        execute_with_plan(&program, &ExecutionConfig::all_symbolic(), &plan).unwrap()
    } else {
        execute(&program, &ExecutionConfig::all_symbolic(), &selection).unwrap()
    };
    // Canonical input names used by the test-only density oracle.
    for c in &mut hps.components {
        for index in 0..2 {
            super::super::optimize::substitute_component(
                c,
                &Variable::Input(Qubit { register, index }),
                &BooleanPolynomial::variable(Variable::Input(Qubit {
                    register: SymbolId(0),
                    index,
                })),
            );
        }
    }
    hps
}

fn same_channel(actual: &str, reference: &str, live_result: bool) {
    let actual = run(actual, live_result, false);
    let reference = run(reference, live_result, false);
    super::super::optimize::assert_density(&actual.components, &reference.components);
}

#[test]
fn delayed_discard_matches_explicit_split_for_asymmetric_dependencies() {
    for prefix in ["", "h q[0]; cx q[0],q[1];"] {
        for (left, right) in [
            ("cx q[0],q[1];", ""),
            ("cz q[0],q[1];", "x q[1];"),
            ("swap q[0],q[1];", "s q[1];"),
            ("p(pi/4) q[1]; cx q[0],q[1];", "z q[1];"),
        ] {
            for live_result in [false, true] {
                let actual =
                    format!("{prefix} c = measure q[0]; if (c) {{ {left} }} else {{ {right} }}");
                // H;H is identity, but H excludes the reference branches
                // from guarded monomial execution and forces explicit splits.
                let reference = format!(
                    "{prefix} c = measure q[0];                      if (c) {{ h q[1]; h q[1]; {left} }}                      else {{ h q[1]; h q[1]; {right} }}"
                );
                same_channel(&actual, &reference, live_result);
            }
        }
    }
}

#[test]
fn branch_local_last_use_does_not_force_a_component_split() {
    let hps = run(
        "h q[0]; c = measure q[0]; if (c) { cx q[0],q[1]; }",
        true,
        true,
    );
    assert_eq!(hps.components.len(), 1);
    assert_eq!(hps.components[0].output.quantum.len(), 1);
    assert_eq!(hps.components[0].output.classical.len(), 1);
}

#[test]
fn a_future_classical_use_survives_the_first_join() {
    same_channel(
        "c = measure q[0]; if (c) { x q[1]; } if (c) { z q[1]; }",
        "c = measure q[0]; if (c) { h q[1]; h q[1]; x q[1]; z q[1]; }",
        false,
    );
}

#[test]
fn repeated_quantum_use_is_not_discarded_at_the_inner_scope_exit() {
    let actual = run_with_scope(
        "c = measure q[0]; if (c) { cx q[0],q[1]; cz q[0],q[1]; }",
        false,
        false,
        true,
    );
    let reference = run(
        "c = measure q[0]; if (c) { h q[1]; h q[1]; cx q[0],q[1]; cz q[0],q[1]; }",
        false,
        false,
    );
    super::super::optimize::assert_density(&actual.components, &reference.components);
}

#[test]
fn nonunitary_branch_effects_still_use_general_execution() {
    for effect in ["reset q[1];", "c = measure q[1];", "c = false;"] {
        same_channel(
            &format!("c = measure q[0]; if (c) {{ {effect} }} x q[1];"),
            &format!("c = measure q[0]; if (c) {{ h q[1]; h q[1]; {effect} }} x q[1];"),
            true,
        );
    }
}
