use irene::{
    ablation::{self, Config, Group},
    equivalence::{self, EquivalenceConfig, Evidence, Verdict},
    frontend::openqasm3,
    ir::{Program, Qubit},
    symbolic::{ExecutionConfig, OutputSelection, execute},
};

fn parse(body: &str) -> Program {
    openqasm3::parse_str(
        &format!("OPENQASM 3.0; include \"stdgates.inc\"; {body}"),
        "ablation.qasm",
    )
    .unwrap()
}
fn analyze(
    left: &Program,
    right: &Program,
    disabled: impl IntoIterator<Item = Group>,
) -> (equivalence::Analysis, ablation::Report) {
    let config = EquivalenceConfig::positional(left, right).unwrap();
    let (answer, report) = ablation::run(Config::without(disabled), || {
        equivalence::analyze(left, right, &config)
    });
    (answer.unwrap(), report)
}

#[test]
fn default_scope_preserves_the_existing_pipeline() {
    let left = parse("qubit q; h q; h q;");
    let right = parse("qubit q;");
    let config = EquivalenceConfig::positional(&left, &right).unwrap();
    let normal = equivalence::analyze(&left, &right, &config).unwrap();
    let (scoped, report) = analyze(&left, &right, []);
    assert_eq!(normal.verdict, scoped.verdict);
    assert_eq!(normal.evidence, scoped.evidence);
    assert!(report.config.disabled().is_empty());
    assert!(report.counts(Group::GateRewrite).admitted > 0);
}

#[test]
fn disabling_optimizations_uses_original_hps_instead_of_unitary_trace() {
    let h = parse("qubit q; h q;");
    let (answer, report) = analyze(&h, &h, Group::ALL);
    assert_eq!(answer.verdict, Verdict::Equivalent);
    assert_eq!(answer.evidence, Evidence::ExactHps);
    assert!(report.counts(Group::GateRewrite).skipped > 0);
    let feedback = parse("qubit q; bit c; h q; c = measure q; if (c) { x q; } c = false;");
    let reset = parse("qubit q; bit c; reset q; c = false;");
    let (answer, report) = analyze(&feedback, &reset, Group::ALL);
    assert_ne!(answer.verdict, Verdict::NotEquivalent);
    for group in [Group::FeedbackSummary, Group::ExpressionSimplify] {
        assert!(report.counts(group).skipped > 0, "{group:?}: {report}");
        assert_eq!(report.counts(group).admitted, 0);
    }
}

#[test]
fn gate_ablation_bypasses_trace_but_retains_direct_eq_and_neq_proofs() {
    let h = parse("qubit q; h q;");
    let (normal, _) = analyze(&h, &h, []);
    assert_eq!(normal.evidence, Evidence::UnitaryTraceExact);
    let (direct, report) = analyze(&h, &h, [Group::GateRewrite]);
    assert_eq!(direct.verdict, Verdict::Equivalent);
    assert_eq!(direct.evidence, Evidence::ExactHps);
    assert_eq!(report.counts(Group::GateRewrite).admitted, 0);
    assert!(report.counts(Group::GateRewrite).skipped > 0);

    let x = parse("qubit q; x q;");
    let identity = parse("qubit q;");
    let (direct, _) = analyze(&x, &identity, [Group::GateRewrite]);
    assert_eq!(direct.verdict, Verdict::NotEquivalent);
    assert!(!matches!(
        direct.evidence,
        Evidence::UnitaryTraceExact
            | Evidence::UnitaryTraceMismatch { .. }
            | Evidence::UnitaryTraceCyclotomicMismatch { .. }
    ));
}

#[test]
fn disabled_optimizations_keep_fourier_and_guard_elimination() {
    let program = parse("qubit q; h q; h q;");
    let selection = OutputSelection::new(
        [Qubit {
            register: program.quantum_registers[0].id,
            index: 0,
        }],
        [],
    );
    let execute = || execute(&program, &ExecutionConfig::all_symbolic(), &selection).unwrap();
    let (normal, _) = ablation::run(Config::default(), execute);
    let (raw, report) = ablation::run(Config::without(Group::ALL), execute);
    let paths = |h: &irene::symbolic::HybridPathSum| {
        h.components
            .iter()
            .map(|c| c.path_support.len())
            .sum::<usize>()
    };
    assert_eq!(paths(&normal), 0);
    assert_eq!(paths(&raw), 0);
    assert!(report.counts(Group::ExpressionSimplify).skipped > 0);
}

#[test]
fn every_mask_preserves_small_eq_and_neq_soundness() {
    let pairs = [
        ("qubit q; h q; h q;", "qubit q;", Verdict::Equivalent),
        ("qubit q; h q;", "qubit q;", Verdict::NotEquivalent),
        ("qubit q; z q;", "qubit q;", Verdict::NotEquivalent),
        (
            "qubit q; bit c; h q; c = measure q; if (c) { x q; } c = false;",
            "qubit q; bit c; reset q; c = false;",
            Verdict::Equivalent,
        ),
    ];
    for (a, b, expected) in pairs {
        let (a, b) = (parse(a), parse(b));
        assert_eq!(analyze(&a, &b, []).0.verdict, expected);
        for mask in 0..(1 << Group::ALL.len()) {
            let disabled = Group::ALL
                .into_iter()
                .filter(|g| mask & (1 << *g as usize) != 0);
            let (answer, report) = analyze(&a, &b, disabled);
            assert!(
                answer.verdict == expected || answer.verdict == Verdict::Unknown,
                "mask={mask} {:?}, expected {expected:?}",
                answer
            );
            for group in report.config.disabled() {
                assert_eq!(report.counts(group).admitted, 0);
            }
        }
    }
}
