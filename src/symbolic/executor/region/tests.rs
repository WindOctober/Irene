use super::*;

const TDG: &str = "reset q[1]; h q[1]; reset q[2]; h q[2];
    cz q[0],q[1]; cz q[1],q[2]; tdg q[0]; h q[0];
    measure q[0] -> c[0]; h q[1]; measure q[1] -> c[1];
    if(c[0]==1) z q[2]; if(c[1]==1) x q[2];";

fn setup(
    body: &str,
    outputs: &[usize],
    observed: &[usize],
) -> (Program, SlicePlan, Component, Executor) {
    let source = format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit[4] q; bit[2] c; {body}");
    let program = crate::frontend::openqasm3::parse_str(&source, "region.qasm").unwrap();
    let wire = |index| Qubit {
        register: program.quantum_registers[0].id,
        index,
    };
    let bit = |index| ClassicalBit {
        register: program.classical_registers[0].id,
        index,
    };
    let plan = slice::build_slice_plan(
        &program,
        &OutputSelection::new(
            outputs.iter().map(|i| wire(*i)),
            observed.iter().map(|i| bit(*i)),
        ),
    )
    .unwrap();
    let component = Component {
        guard: vec![],
        scalar: Scalar::one(),
        phase: PhasePolynomial::zero(),
        path_support: BTreeSet::new(),
        output: initial_memory(&program, &InitialState::AllSymbolic, &plan.live_quantum).unwrap(),
    };
    let executor = Executor {
        next_path: 0,
        ids: AstIdGenerator::starting_at(program.ast_id_bound()),
        boundaries_since_compaction: 0,
        compaction_interval: MIN_COMPACTION_INTERVAL,
        pending_feedback: BTreeSet::new(),
        summarize_regions: false,
    };
    (program, plan, component, executor)
}

// Independent test-only contraction of every |x><x'| -> |q><q'|
// density entry. In particular this tests input coherence/entangled references,
// not merely the outcome probabilities of computational-basis samples.
fn channel(components: &[Component], inputs: &[Qubit]) -> Vec<(f64, f64)> {
    use crate::symbolic::ScalarBindings;
    let outputs = components[0].output.quantum.len();
    type Environment = Vec<(Option<ClassicalBit>, bool)>;
    type Amplitudes = BTreeMap<(Environment, Vec<bool>, usize), (f64, f64)>;
    let mut amplitudes = vec![Amplitudes::new(); 1 << inputs.len()];
    for (input, world) in amplitudes.iter_mut().enumerate() {
        for c in components {
            assert!(c.path_support.len() <= 8);
            for assignment in 0..1usize << c.path_support.len() {
                let mut bindings = ScalarBindings::default();
                for (i, wire) in inputs.iter().enumerate() {
                    bindings
                        .booleans
                        .insert(Variable::Input(wire.clone()), input & (1 << i) != 0);
                }
                for (i, path) in c.path_support.iter().enumerate() {
                    bindings
                        .booleans
                        .insert(Variable::Path(*path), assignment & (1 << i) != 0);
                }
                let monomial =
                    |m: &crate::symbolic::Monomial| m.variables().all(|v| bindings.booleans[v]);
                let boolean =
                    |p: &BooleanPolynomial| p.terms().filter(|m| monomial(m)).count() % 2 == 1;
                if c.guard.iter().any(boolean) {
                    continue;
                }
                let turns: f64 = c
                    .phase
                    .terms()
                    .filter(|(m, _)| monomial(m))
                    .map(|(_, coef)| {
                        let r = coef.as_rational().unwrap();
                        r.numer().to_string().parse::<f64>().unwrap()
                            / r.denom().to_string().parse::<f64>().unwrap()
                    })
                    .sum();
                let history = c
                    .output
                    .history
                    .iter()
                    .map(|h| match h {
                        HistoryEntry::Write { target, value } => {
                            (Some(target.clone()), boolean(value))
                        }
                        HistoryEntry::Discard { value } => (None, boolean(value)),
                    })
                    .collect();
                let output = c
                    .output
                    .quantum
                    .values()
                    .enumerate()
                    .fold(0, |bits, (i, p)| bits | (usize::from(boolean(p)) << i));
                let classical = c.output.classical.values().map(boolean).collect();
                let amplitude = world.entry((history, classical, output)).or_default();
                let scale = c.scalar.evaluate(128, &bindings).unwrap().to_f64();
                amplitude.0 += scale * (std::f64::consts::TAU * turns).cos();
                amplitude.1 += scale * (std::f64::consts::TAU * turns).sin();
            }
        }
    }
    let mut entries = vec![];
    for left in &amplitudes {
        for right in &amplitudes {
            for q in 0..1 << outputs {
                for qp in 0..1 << outputs {
                    let mut entry = (0., 0.);
                    for ((history, classical, output), a) in left {
                        if *output == q
                            && let Some(b) = right.get(&(history.clone(), classical.clone(), qp))
                        {
                            entry.0 += a.0 * b.0 + a.1 * b.1;
                            entry.1 += a.1 * b.0 - a.0 * b.1;
                        }
                    }
                    entries.push(entry);
                }
            }
        }
    }
    entries
}

fn assert_channel(a: &[Component], b: &[Component], inputs: &[Qubit]) {
    let left = channel(a, inputs);
    let right = channel(b, inputs);
    assert_eq!(left.len(), right.len());
    for (a, b) in left.into_iter().zip(right) {
        assert!(
            (a.0 - b.0).abs() < 1e-10 && (a.1 - b.1).abs() < 1e-10,
            "{a:?} != {b:?}"
        );
    }
}

#[test]
fn isolated_tdg_composes_before_final_simplification() {
    let (program, plan, prefix, mut executor) = setup(TDG, &[2], &[]);
    let inputs: Vec<_> = prefix.output.quantum.keys().cloned().collect();
    let (length, composed) = executor
        .summarize_region(
            std::slice::from_ref(&prefix),
            &program.body.statements,
            &plan,
        )
        .unwrap();
    assert_eq!(length, program.body.statements.len());
    assert!(composed[0].output.history.is_empty());
    assert!(composed[0].path_support.is_empty());
    let raw = executor
        .execute_block(vec![prefix], &program.body, &plan, false)
        .unwrap();
    assert_channel(&raw, &composed, &inputs);
    assert_eq!(composed[0].scalar, Scalar::one());
    let (monomial, coefficient) = composed[0].phase.terms().next().unwrap();
    assert_eq!(composed[0].phase.terms().count(), 1);
    assert_eq!(monomial.variables().count(), 1);
    assert_eq!(coefficient, PhaseCoefficient::rational(ratio(-1, 8)));
}

#[test]
fn complex_prefix_and_existing_history_do_not_enter_local_proof() {
    let (program, plan, mut prefix, mut executor) = setup(TDG, &[2, 3], &[]);
    let wires: Vec<_> = prefix.output.quantum.keys().cloned().collect();
    let input = prefix.output.quantum[&wires[0]].clone();
    let reference = prefix.output.quantum[&wires[1]].clone();
    // A nonlinear boundary value involving both a free input and an old path.
    let value = input.xor(&reference.and(&path_value(90)));
    prefix.output.quantum.insert(wires[0].clone(), value);
    prefix.output.history.push(HistoryEntry::Discard {
        value: path_value(90),
    });
    prefix.path_support.insert(90);
    prefix.scalar = Scalar::sqrt(Scalar::rational(ratio(1, 2)));
    executor.next_path = 91;
    let (_, composed) = executor
        .summarize_region(
            std::slice::from_ref(&prefix),
            &program.body.statements,
            &plan,
        )
        .unwrap();
    assert_eq!(composed[0].output.history, prefix.output.history);
    assert_eq!(composed[0].path_support, prefix.path_support);
    let raw = executor
        .execute_block(vec![prefix], &program.body, &plan, false)
        .unwrap();
    assert_channel(&raw, &composed, &wires);
}

#[test]
fn incomplete_correction_or_visible_outcome_cannot_be_collapsed() {
    for (body, observed) in [
        (TDG.replace("if(c[1]==1) x q[2];", ""), vec![]),
        (TDG.to_owned(), vec![0]),
    ] {
        let (program, plan, prefix, mut executor) = setup(&body, &[2], &observed);
        assert!(
            executor
                .summarize_region(&[prefix], &program.body.statements, &plan)
                .is_none()
        );
    }
}

#[test]
fn correction_targets_are_independent_inputs_not_assumed_ancillas() {
    let (program, plan, prefix, mut executor) = setup(
        "h q[0]; c[0] = measure q[0]; if(c[0]==1) z q[1];",
        &[1],
        &[],
    );
    assert_eq!(prefix.output.quantum.len(), 2);
    assert!(
        executor
            .summarize_region(&[prefix], &program.body.statements, &plan)
            .is_none()
    );
}

#[test]
fn simultaneous_substitution_does_not_capture_other_boundary_inputs() {
    let body = format!("cz q[0],q[3]; {TDG}");
    let (program, plan, mut prefix, mut executor) = setup(&body, &[2, 3], &[]);
    let wires: Vec<_> = prefix.output.quantum.keys().cloned().collect();
    let a = prefix.output.quantum[&wires[0]].clone();
    let b = prefix.output.quantum[&wires[1]].clone();
    prefix.output.quantum.insert(wires[0].clone(), b);
    prefix.output.quantum.insert(wires[1].clone(), a);
    let (_, composed) = executor
        .summarize_region(
            std::slice::from_ref(&prefix),
            &program.body.statements,
            &plan,
        )
        .unwrap();
    let raw = executor
        .execute_block(vec![prefix], &program.body, &plan, false)
        .unwrap();
    assert_channel(&raw, &composed, &wires);
}

#[test]
fn large_unrelated_prefix_is_not_a_summary_budget() {
    let (program, plan, mut prefix, mut executor) = setup(TDG, &[2], &[]);
    for path in 0..256 {
        prefix.path_support.insert(path);
        prefix.output.history.push(HistoryEntry::Discard {
            value: path_value(path),
        });
        prefix
            .guard
            .push(path_value(path).xor(&path_value((path + 1) % 256)));
    }
    executor.next_path = 256;
    let (_, composed) = executor
        .summarize_region(
            std::slice::from_ref(&prefix),
            &program.body.statements,
            &plan,
        )
        .unwrap();
    assert_eq!(composed[0].output.history, prefix.output.history);
    assert_eq!(composed[0].guard, prefix.guard);
    assert_eq!(composed[0].path_support, prefix.path_support);
}

#[test]
fn the_same_summary_preserves_coherent_prefix_cross_terms() {
    let (program, plan, prefix, mut executor) = setup(TDG, &[2], &[]);
    let wires: Vec<_> = prefix.output.quantum.keys().cloned().collect();
    let mut other = prefix.clone();
    other.phase.add_boolean(
        &BooleanPolynomial::one(),
        PhaseCoefficient::rational(ratio(1, 4)),
    );
    let prefixes = vec![prefix, other];
    let (_, composed) = executor
        .summarize_region(&prefixes, &program.body.statements, &plan)
        .unwrap();
    assert_eq!(composed.len(), 2);
    let raw = executor
        .execute_block(prefixes, &program.body, &plan, false)
        .unwrap();
    assert_channel(&raw, &composed, &wires);
}

#[test]
fn summaries_with_remaining_coherent_paths_are_freshened() {
    let (program, plan, mut prefix, mut executor) = setup(
        "reset q[1]; h q[1]; cz q[0],q[1]; h q[0]; c[0] = measure q[0]; if(c[0]==1) x q[1];",
        &[1],
        &[],
    );
    let wires: Vec<_> = prefix.output.quantum.keys().cloned().collect();
    prefix.output.history.push(HistoryEntry::Discard {
        value: path_value(0),
    });
    prefix.path_support.insert(0);
    prefix.scalar = Scalar::sqrt(Scalar::rational(ratio(1, 2)));
    executor.next_path = 1;
    let (_, composed) = executor
        .summarize_region(
            std::slice::from_ref(&prefix),
            &program.body.statements,
            &plan,
        )
        .unwrap();
    assert_eq!(composed[0].path_support.len(), 2);
    assert_eq!(composed[0].output.history, prefix.output.history);
    let raw = executor
        .execute_block(vec![prefix], &program.body, &plan, false)
        .unwrap();
    assert_channel(&raw, &composed, &wires);
}

#[test]
fn symbolic_external_classical_control_and_budget_failure_are_atomic() {
    let body = format!("if(c[0]==1) x q[3]; {TDG}");
    let (program, plan, mut prefix, mut executor) = setup(&body, &[2, 3], &[]);
    let bit = ClassicalBit {
        register: program.classical_registers[0].id,
        index: 0,
    };
    prefix.output.classical.insert(bit, path_value(9));
    prefix.path_support.insert(9);
    executor.next_path = 10;
    assert!(
        executor
            .summarize_region(&[prefix], &program.body.statements, &plan)
            .is_none()
    );
    assert_eq!(executor.next_path, 10);

    let body = format!("{} {TDG}", "x q[0]; ".repeat(MAX_STATEMENTS));
    let (program, plan, prefix, mut executor) = setup(&body, &[2], &[]);
    assert!(
        executor
            .summarize_region(&[prefix], &program.body.statements, &plan)
            .is_none()
    );
    assert_eq!(executor.next_path, 0);
}

#[test]
fn automatic_summary_execution_matches_ordinary_execution_and_fallback() {
    for body in [
        TDG.to_owned(),
        TDG.replace("tdg q[0];", "t q[0];"),
        TDG.replace("if(c[1]==1) x q[2];", ""),
    ] {
        let (program, plan, prefix, mut enabled) = setup(&body, &[2], &[]);
        let (_, _, _, mut disabled) = setup(&body, &[2], &[]);
        let inputs: Vec<_> = prefix.output.quantum.keys().cloned().collect();
        enabled.summarize_regions = true;
        let actual = enabled
            .execute_block(vec![prefix.clone()], &program.body, &plan, true)
            .unwrap();
        let expected = disabled
            .execute_block(vec![prefix], &program.body, &plan, true)
            .unwrap();
        assert_channel(&actual, &expected, &inputs);
    }
}

#[test]
fn fresh_path_overflow_abandons_summary_without_mutating_executor() {
    let (program, plan, prefix, mut executor) = setup(
        "reset q[1]; h q[1]; cz q[0],q[1]; h q[0]; c[0] = measure q[0]; if(c[0]==1) x q[1];",
        &[1],
        &[],
    );
    executor.next_path = usize::MAX;
    let id_bound = executor.ids.clone().node(()).ast_id;
    assert!(
        executor
            .summarize_region(&[prefix], &program.body.statements, &plan)
            .is_none()
    );
    assert_eq!(executor.next_path, usize::MAX);
    assert_eq!(executor.ids.clone().node(()).ast_id, id_bound);
}
