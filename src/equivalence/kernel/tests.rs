use super::*;
use crate::ir::{ClassicalBit, SymbolId};
use crate::symbolic::{Component, HybridMemory, PhaseCoefficient, PhasePolynomial};
use num_bigint::BigInt;

#[test]
fn graph_namespaces_round_trip_without_coupling_binders_or_free_indices() {
    let mut variables = vec![
        KernelVariable::InputKet(0),
        KernelVariable::InputBra(0),
        KernelVariable::QuantumOutputKet(0),
        KernelVariable::QuantumOutputBra(0),
        KernelVariable::ClassicalOutput(0),
    ];
    for term in 0..8 {
        for path in 0..4 {
            variables.push(KernelVariable::PathKet { term, path });
            variables.push(KernelVariable::PathBra { term, path });
        }
    }
    let names: BTreeSet<_> = variables
        .iter()
        .map(KernelVariable::graph_variable)
        .collect();
    assert_eq!(names.len(), variables.len());
    for v in variables {
        assert_eq!(KernelVariable::from_graph_variable(&v.graph_variable()), v);
    }
}

#[test]
fn weighted_graph_selectors_keep_exact_phase_under_substitution() {
    let v = |i| BooleanPolynomial::variable(KernelVariable::InputKet(i).graph_variable());
    let selectors = [
        v(0).xor(&v(1)),
        v(0).and(&v(1).xor(&v(2)))
            .xor(&v(3).and(&v(4).complement()))
            .xor(&v(5)),
    ];
    for selector in selectors {
        for denominator in [2, 4, 8, 7] {
            let coefficient = BigRational::new(1.into(), denominator.into());
            let mut phase = KernelPhasePolynomial::default();
            phase.add_selector(
                KernelBooleanPolynomial::from_graph(selector.clone()),
                PhaseCoefficient::rational(coefficient.clone()),
            );
            for bits in 0..64 {
                let bit = |i| bits & (1 << i) != 0;
                let expected = selector
                    .evaluate::<std::convert::Infallible>(|v| {
                        let KernelVariable::InputKet(i) = KernelVariable::from_graph_variable(v)
                        else {
                            unreachable!()
                        };
                        Ok(bit(i))
                    })
                    .unwrap();
                let mut actual = phase.clone();
                for i in 0..6 {
                    actual.substitute(
                        &KernelVariable::InputKet(i),
                        &KernelBooleanPolynomial::from(bit(i)),
                    );
                }
                let sum = actual
                    .selectors()
                    .map(|(p, c)| {
                        assert!(p.is_one());
                        c.as_rational().unwrap()
                    })
                    .fold(BigRational::from_integer(0.into()), |a, b| a + b);
                let target = if expected {
                    coefficient.clone()
                } else {
                    BigRational::from_integer(0.into())
                };
                assert!((sum - target).is_integer());
            }
        }
    }
}

#[test]
fn shared_boolean_lowering_preserves_exponential_anf_as_graph() {
    let inputs = BTreeMap::new();
    let paths = (0..25).collect::<BTreeSet<_>>();
    let renamer = Renamer::new(KernelBranch::Ket, 0, &inputs, &paths);
    let expression = (0..25).fold(BooleanPolynomial::one(), |p, i| {
        p.and(&BooleanPolynomial::variable(Variable::Path(i)).complement())
    });
    let original = expression.clone();
    let lowered = renamer.boolean(&expression).unwrap();
    assert!(!lowered.is_algebraic());
    assert_eq!(lowered.variables().len(), 25);
    assert!(lowered.as_graph().storage_size() < 300);
    assert_eq!(expression, original);
    assert!(expression.storage_size() < 300);
}

fn assert_phase_index(phase: &KernelPhasePolynomial) {
    let mut rebuilt = phase.clone();
    rebuilt.occurrences = None;
    rebuilt.index_occurrences();
    assert_eq!(phase.occurrences, rebuilt.occurrences);
    assert_eq!(phase, &rebuilt);
    assert_eq!(phase.cmp(&rebuilt), Ordering::Equal);
}

#[test]
fn monomial_collection_matches_repeated_xor_including_collisions() {
    let monomials = (0..8)
        .map(|bits| {
            KernelMonomial(
                (0..3)
                    .filter(|index| bits & (1 << index) != 0)
                    .map(KernelVariable::InputKet)
                    .collect(),
            )
        })
        .collect::<Vec<_>>();
    for mask in 0..256 {
        let terms = monomials
            .iter()
            .enumerate()
            .filter(|(i, _)| mask & (1 << i) != 0)
            .map(|(_, term)| term.clone())
            .chain(monomials.iter().cloned())
            .chain(monomials.iter().rev().take(4).cloned())
            .collect::<Vec<_>>();
        let reference = terms.iter().fold(KernelBooleanPolynomial::zero(), |p, m| {
            p.xor(&KernelBooleanPolynomial::from_monomial(m.clone()))
        });
        assert_eq!(KernelBooleanPolynomial::from_monomials(terms), reference);
    }
}

#[test]
fn indexed_phase_substitution_matches_full_scan_for_all_three_bit_anf_replacements() {
    let monomials = (0..8)
        .map(|bits| {
            KernelMonomial(
                (0..3)
                    .filter(|index| bits & (1 << index) != 0)
                    .map(KernelVariable::InputKet)
                    .collect(),
            )
        })
        .collect::<Vec<_>>();
    let mut source = KernelPhasePolynomial::default();
    for (index, monomial) in monomials.iter().enumerate() {
        source.add_term(
            monomial.clone(),
            PhaseCoefficient::rational(BigRational::new((index + 1).into(), 32.into())),
        );
    }
    let mut indexed = source.clone();
    indexed.index_occurrences();
    assert_eq!(source, indexed);
    assert_eq!(source.cmp(&indexed), Ordering::Equal);
    for bits in 0..256 {
        let replacement = KernelBooleanPolynomial {
            graph: None,
            terms: monomials
                .iter()
                .enumerate()
                .filter(|(index, _)| bits & (1 << index) != 0)
                .map(|(_, monomial)| monomial.clone())
                .collect(),
        };
        for index in 0..3 {
            let variable = KernelVariable::InputKet(index);
            // A separate full traversal reconstructs the complete
            // substituted phase, including every unaffected monomial.
            let mut scanned = KernelPhasePolynomial::default();
            for (monomial, coefficient) in source.terms() {
                if monomial.contains(&variable) {
                    scanned.add_boolean(
                        &KernelBooleanPolynomial::from_monomial(monomial.without(&variable))
                            .and(&replacement),
                        coefficient.clone(),
                    );
                } else {
                    scanned.add_term(monomial.clone(), coefficient.clone());
                }
            }
            let mut actual = indexed.clone();
            actual.substitute(&variable, &replacement);
            assert_eq!(actual, scanned);
            assert_phase_index(&actual);
            assert_eq!(
                actual.occurrence_count(&variable),
                actual
                    .terms()
                    .filter(|(monomial, _)| monomial.contains(&variable))
                    .count()
            );
        }
    }
}

#[test]
fn phase_index_tracks_cancellation_renaming_and_difference() {
    let x = KernelVariable::InputKet(0);
    let y = KernelVariable::InputBra(0);
    let z = KernelVariable::PathKet { term: 0, path: 0 };
    let eighth = PhaseCoefficient::rational(BigRational::new(1.into(), 8.into()));
    let mut phase = KernelPhasePolynomial::default();
    phase.index_occurrences();
    let xy = KernelMonomial::variable(x.clone()).multiply(&KernelMonomial::variable(y.clone()));
    phase.add_term(xy.clone(), eighth.clone());
    assert_phase_index(&phase);
    phase.add_term(xy, eighth.scaled((-1).into()));
    assert_eq!(phase.occurrence_count(&x), 0);
    assert!(phase.variables().is_empty());
    assert_phase_index(&phase);
    phase.add_boolean(
        &KernelBooleanPolynomial::variable(x.clone())
            .xor(&KernelBooleanPolynomial::variable(y.clone())),
        eighth.clone(),
    );
    phase.add_term(KernelMonomial::one(), eighth);
    assert_phase_index(&phase);
    phase.rename_variables(&BTreeMap::from([(x, z.clone()), (y, z)]));
    // The lift of x XOR y cancels when both names become z. The
    // constant phase remains, despite having no occurrence-index entry.
    assert_eq!(phase.term_count(), 1);
    assert!(phase.variables().is_empty());
    assert_phase_index(&phase);
    let mut unindexed = phase.clone();
    unindexed.occurrences = None;
    let difference = KernelPhasePolynomial::difference(&phase, &unindexed);
    assert_eq!(difference, KernelPhasePolynomial::default());
    assert_phase_index(&difference);
}

#[test]
fn phase_index_refuses_and_invalidates_oversized_metadata() {
    let mut phase = KernelPhasePolynomial::default();
    let coefficient = PhaseCoefficient::rational(BigRational::new(1.into(), 8.into()));
    let kept = KernelMonomial::variable(KernelVariable::InputKet(0));
    phase.add_term(kept.clone(), coefficient.clone());
    phase.index_occurrences();
    let wide = KernelMonomial(
        (0..MAX_PHASE_INDEX_CELLS)
            .map(KernelVariable::InputBra)
            .collect(),
    );
    phase.add_term(wide.clone(), coefficient.clone());
    assert!(phase.occurrences.is_none());
    assert_eq!(phase.term_count(), 2);
    assert_eq!(phase.coefficient(&wide), coefficient);
    phase.index_occurrences();
    assert!(phase.occurrences.is_none());
    assert_eq!(phase.occurrence_count(&KernelVariable::InputBra(0)), 1);
    phase.substitute(
        &KernelVariable::InputBra(0),
        &KernelBooleanPolynomial::zero(),
    );
    assert_eq!(phase.term_count(), 1);
    assert_eq!(phase.coefficient(&kept), coefficient);
    phase.index_occurrences();
    assert_phase_index(&phase);
}

fn component(path: usize, history: Vec<HistoryEntry>) -> Component {
    Component {
        guard: vec![BooleanPolynomial::variable(Variable::Path(path))],
        scalar: Scalar::select(
            BooleanPolynomial::variable(Variable::Path(path)),
            Scalar::one(),
            Scalar::zero(),
        ),
        path_support: BTreeSet::from([path]),
        phase: PhasePolynomial::zero(),
        output: HybridMemory {
            quantum: BTreeMap::new(),
            classical: BTreeMap::new(),
            history,
        },
    }
}

#[test]
fn phase_is_exactly_renamed_on_both_sides_of_the_difference() {
    let path = BooleanPolynomial::variable(Variable::Path(3));
    let mut value = component(3, Vec::new());
    value.phase.add_boolean(
        &path,
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(8))),
    );
    let hps = HybridPathSum {
        input: HybridMemory::default(),
        components: vec![value],
    };
    let kernel = build_kernel(&KernelInput::new(
        &hps,
        Vec::new(),
        vec![KernelTerminalInput::default()],
    ))
    .unwrap();
    let term = &kernel.terms[0];

    assert_eq!(
        term.phase
            .ket
            .coefficient(&KernelMonomial::variable(KernelVariable::PathKet {
                term: 0,
                path: 3
            })),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(8)))
    );
    assert_eq!(
        term.phase
            .bra
            .coefficient(&KernelMonomial::variable(KernelVariable::PathBra {
                term: 0,
                path: 3
            })),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(8)))
    );
}

#[test]
fn pairs_only_components_with_compatible_history_structure() {
    let discarded = BooleanPolynomial::variable(Variable::Path(0));
    let write_target = ClassicalBit {
        register: SymbolId(1),
        index: 0,
    };
    let hps = HybridPathSum {
        input: HybridMemory::default(),
        components: vec![
            component(
                0,
                vec![HistoryEntry::Discard {
                    value: discarded.clone(),
                }],
            ),
            component(
                0,
                vec![HistoryEntry::Write {
                    target: write_target,
                    value: discarded.clone(),
                }],
            ),
        ],
    };
    let terminals = vec![
        KernelTerminalInput {
            quantum: Vec::new(),
            classical: vec![discarded.clone()],
        },
        KernelTerminalInput {
            quantum: Vec::new(),
            classical: vec![discarded],
        },
    ];

    let kernel = build_kernel(&KernelInput::new(&hps, Vec::new(), terminals)).unwrap();

    // The two diagonal pairs remain; Discard and Write are different
    // environment structures, so their cross terms are absent.
    assert_eq!(kernel.terms.len(), 2);
}

#[test]
fn compatible_components_form_the_full_coherent_outer_product() {
    let y0 = BooleanPolynomial::variable(Variable::Path(0));
    let y1 = BooleanPolynomial::variable(Variable::Path(1));
    let hps = HybridPathSum {
        input: HybridMemory::default(),
        components: vec![
            component(0, vec![HistoryEntry::Discard { value: y0.clone() }]),
            component(1, vec![HistoryEntry::Discard { value: y1.clone() }]),
        ],
    };
    let terminals = vec![
        KernelTerminalInput {
            quantum: vec![y0],
            classical: Vec::new(),
        },
        KernelTerminalInput {
            quantum: vec![y1],
            classical: Vec::new(),
        },
    ];

    let kernel = build_kernel(&KernelInput::new(&hps, Vec::new(), terminals)).unwrap();

    // Two coherent amplitude summands produce all four ordered terms in
    // |A><A|.  Pairwise/diagonal-only comparison would lose interference.
    assert_eq!(kernel.terms.len(), 4);
}

#[test]
fn refuses_an_outer_product_beyond_the_preflight_budget() {
    let components = (0..257)
        .map(|_| component(0, Vec::new()))
        .collect::<Vec<_>>();
    let terminals = vec![KernelTerminalInput::default(); components.len()];
    let hps = HybridPathSum {
        input: HybridMemory::default(),
        components,
    };

    assert_eq!(
        build_kernel(&KernelInput::new(&hps, Vec::new(), terminals)),
        Err(KernelBuildError::ComponentPairBudget {
            components: 257,
            maximum_pairs: MAX_COMPONENT_PAIR_CANDIDATES,
        })
    );
}
