use super::*;
use crate::ir::SymbolId;

fn assert_density(before: &[Component], after: &[Component]) {
    super::super::optimize::assert_density(before, after);
}

#[test]
fn immediate_and_batched_path_reduction_preserve_density() {
    let mut component = visible_path();
    component.path_support.insert(1);
    let path = BooleanPolynomial::variable(Variable::Path(1));
    let input = BooleanPolynomial::variable(Variable::Input(Qubit {
        register: SymbolId(0),
        index: 0,
    }));
    let output = component.output.quantum.values().next().unwrap();
    component.phase.add_boolean(
        &path.and(&input.xor(output)),
        PhaseCoefficient::rational(ratio(1, 2)),
    );
    component.scalar = Scalar::rational(ratio(1, 2));
    let original = vec![component];
    let immediate = compact_components(original.clone(), true);
    assert_density(&original, &immediate);
    assert!(immediate[0].path_support.len() < original[0].path_support.len());
    let mut executor = executor();
    let mut batched = original.clone();
    for _ in 0..MAX_COMPACTION_INTERVAL {
        batched = executor.compact_at_boundary(batched, true);
    }
    assert_density(&original, &batched);
}

#[test]
fn partial_compaction_preserves_cross_terms_with_an_outside_summand() {
    let mut a = visible_path();
    let mut outside = visible_path();
    for c in [&mut a, &mut outside] {
        let path = c.output.quantum.pop_first().unwrap().1;
        c.output.history.push(HistoryEntry::Discard { value: path });
        c.scalar = Scalar::rational(ratio(1, 2));
    }
    outside.phase.add_boolean(
        &BooleanPolynomial::variable(Variable::Path(0)),
        PhaseCoefficient::rational(ratio(1, 2)),
    );
    let before = vec![a.clone(), outside.clone()];
    let mut after = compact_components(vec![a], false);
    after.push(outside);
    assert_density(&before, &after);
}

#[test]
fn complete_hidden_history_reduction_preserves_density() {
    let mut component = visible_path();
    let path = component.output.quantum.pop_first().unwrap().1;
    component
        .output
        .history
        .push(HistoryEntry::Discard { value: path });
    let original = vec![component];
    let result = compact_components(original.clone(), true);
    assert_density(&original, &result);
    assert!(result[0].path_support.is_empty());
}

// Deliberately call execute_with_plan, BEFORE execute()'s final simplify.
// These assertions distinguish construction-time convergence from a final
// density-kernel or end-of-execution optimization.
fn correction_boundary(source_tail: &str, classical_live: bool) -> HybridPathSum {
    let source = format!(
        "OPENQASM 2.0; include \"qelib1.inc\"; qreg q[2]; creg c[1];
        h q[1]; cz q[0],q[1]; h q[0]; measure q[0] -> c[0]; {source_tail}"
    );
    let program = crate::frontend::openqasm2::parse_str(&source, "boundary.qasm").unwrap();
    let wire = |index| Qubit {
        register: program.quantum_registers[0].id,
        index,
    };
    let bit = ClassicalBit {
        register: program.classical_registers[0].id,
        index: 0,
    };
    let selection =
        OutputSelection::new([wire(1)], if classical_live { vec![bit] } else { vec![] });
    let plan = slice::build_slice_plan(&program, &selection).unwrap();
    execute_with_plan(
        &program,
        &ExecutionConfig::with_symbolic_inputs([wire(0)]),
        &plan,
    )
    .unwrap()
}

#[test]
fn future_control_and_observed_classical_outcome_stay_live() {
    let observed = correction_boundary("if(c==1) x q[1];", true);
    assert!(!observed.components[0].output.history.is_empty());
    assert_eq!(observed.components[0].output.classical.len(), 1);
    // The second correction is wrong for H: its random relative phase
    // dephases the output. The first join must not erase its future control.
    let wrong = correction_boundary("if(c==1) x q[1]; if(c==1) z q[1];", false);
    assert!(!wrong.components[0].output.history.is_empty());
}

#[test]
fn partial_component_sets_never_apply_local_density_convergence() {
    let source = correction_boundary("if(c==1) x q[1];", true);
    let mut component = source.components[0].clone();
    component.output.classical.clear();
    let before = component.clone();
    let partial = compact_components(vec![component], false);
    assert!(!partial[0].output.history.is_empty());
    assert_eq!(partial[0].output.history, before.output.history);
    let complete = compact_components(partial, true);
    assert!(complete[0].output.history.is_empty());
}

fn executor() -> Executor {
    Executor {
        next_path: 1,
        ids: AstIdGenerator::starting_at(0),
        boundaries_since_compaction: 0,
        compaction_interval: MIN_COMPACTION_INTERVAL,
        pending_feedback: BTreeSet::new(),
        summarize_regions: false,
    }
}

fn visible_path() -> Component {
    Component {
        guard: Vec::new(),
        scalar: Scalar::one(),
        path_support: BTreeSet::from([0]),
        phase: PhasePolynomial::zero(),
        output: HybridMemory {
            quantum: BTreeMap::from([(
                Qubit {
                    register: SymbolId(0),
                    index: 0,
                },
                BooleanPolynomial::variable(Variable::Path(0)),
            )]),
            ..HybridMemory::default()
        },
    }
}

#[test]
fn idle_scans_back_off_but_productive_reduction_restores_short_interval() {
    let mut executor = executor();
    let original = visible_path();
    let mut components = vec![original.clone()];
    for interval in [32, 64, 128, 256, 512, 512] {
        assert_eq!(executor.compaction_interval, interval);
        for _ in 0..interval {
            components = executor.compact_at_boundary(components, true);
        }
        assert_eq!(components, vec![original.clone()]);
        assert_eq!(executor.boundaries_since_compaction, 0);
    }
    components[0].path_support.insert(1);
    for _ in 0..MAX_COMPACTION_INTERVAL {
        components = executor.compact_at_boundary(components, true);
    }
    assert_eq!(executor.compaction_interval, MIN_COMPACTION_INTERVAL);
    assert_eq!(components[0].path_support, BTreeSet::from([0]));
    assert_eq!(components[0].scalar, Scalar::rational(ratio(2, 1)));
}

#[test]
fn component_joins_compact_immediately_even_after_backoff() {
    let mut executor = executor();
    executor.compaction_interval = MAX_COMPACTION_INTERVAL;
    executor.compact_at_boundary(vec![visible_path(), visible_path()], false);
    assert_eq!(executor.boundaries_since_compaction, 0);
    assert_eq!(executor.compaction_interval, MIN_COMPACTION_INTERVAL);
}

#[test]
fn delayed_partial_branch_scan_cannot_eliminate_hidden_history() {
    let mut executor = executor();
    executor.compaction_interval = MAX_COMPACTION_INTERVAL;
    let mut component = visible_path();
    let value = component.output.quantum.pop_first().unwrap().1;
    component
        .output
        .history
        .push(HistoryEntry::Discard { value });
    let mut components = vec![component.clone()];
    for _ in 0..MAX_COMPACTION_INTERVAL {
        components = executor.compact_at_boundary(components, false);
    }
    assert_eq!(components, vec![component]);
    // Final complete-set normalization does not depend on a pending
    // scheduling interval, and may perform the density-preserving rule.
    let result = simplify(HybridPathSum {
        input: HybridMemory::default(),
        components,
    });
    assert!(result.components[0].path_support.is_empty());
}
