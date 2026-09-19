use super::*;
use crate::ir::{ClassicalBit, Qubit, SymbolId};
use crate::symbolic::{HybridMemory, PhasePolynomial, ScalarBindings, Variable};
use std::collections::BTreeMap;
use std::convert::Infallible;

fn rational(numerator: i64, denominator: i64) -> Scalar {
    Scalar::rational(BigRational::new(
        BigInt::from(numerator),
        BigInt::from(denominator),
    ))
}

fn component(scalar: Scalar, history: Vec<HistoryEntry>) -> Component {
    Component {
        guard: Vec::new(),
        scalar,
        path_support: Default::default(),
        phase: PhasePolynomial::zero(),
        output: HybridMemory {
            quantum: Default::default(),
            classical: Default::default(),
            history,
        },
    }
}

fn discard(value: bool) -> HistoryEntry {
    HistoryEntry::Discard {
        value: BooleanPolynomial::from(value),
    }
}

fn q(index: usize) -> Qubit {
    Qubit {
        register: SymbolId(0),
        index,
    }
}
fn x(index: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Input(q(index)))
}
type Density = BTreeMap<(usize, usize, Vec<bool>, Vec<bool>), (f64, f64)>;

// Test-only numerical contraction, including independent ket/bra inputs,
// coherent path sums, typed history labels and all output off-diagonals.
fn density(components: &[Component]) -> Density {
    let mut amplitudes = BTreeMap::<_, (f64, f64)>::new();
    for c in components {
        for input in 0..4 {
            for paths in 0..1usize << c.path_support.len() {
                let mut bindings = ScalarBindings::default();
                for i in 0..2 {
                    bindings
                        .booleans
                        .insert(Variable::Input(q(i)), input & (1 << i) != 0);
                }
                for wire in c.output.quantum.keys() {
                    bindings.booleans.insert(
                        Variable::Input(wire.clone()),
                        input & (1 << wire.index) != 0,
                    );
                }
                for (i, p) in c.path_support.iter().enumerate() {
                    bindings
                        .booleans
                        .insert(Variable::Path(*p), paths & (1 << i) != 0);
                }
                let eval = |p: &BooleanPolynomial| {
                    p.evaluate::<Infallible>(|v| Ok(bindings.booleans[v]))
                        .unwrap()
                };
                if c.guard.iter().any(&eval) {
                    continue;
                }
                let turns: f64 = c
                    .phase
                    .selectors()
                    .filter(|(p, _)| eval(p))
                    .map(|(_, c)| {
                        let r = c.as_rational().unwrap();
                        r.numer().to_string().parse::<f64>().unwrap()
                            / r.denom().to_string().parse::<f64>().unwrap()
                    })
                    .sum();
                let scale = c.scalar.evaluate(128, &bindings).unwrap().to_f64();
                let quantum: Vec<_> = c.output.quantum.values().map(eval).collect();
                let classical: Vec<_> = c.output.classical.values().map(eval).collect();
                let history: Vec<_> = c
                    .output
                    .history
                    .iter()
                    .map(|h| match h {
                        HistoryEntry::Write { target, value } => {
                            (Some(target.clone()), eval(value))
                        }
                        HistoryEntry::Discard { value } => (None, eval(value)),
                    })
                    .collect();
                let entry = amplitudes
                    .entry((input, quantum, classical, history))
                    .or_default();
                entry.0 += scale * (std::f64::consts::TAU * turns).cos();
                entry.1 += scale * (std::f64::consts::TAU * turns).sin();
            }
        }
    }
    let mut result = Density::new();
    for ((x, q, c, h), a) in &amplitudes {
        for ((xp, qp, cp, hp), b) in &amplitudes {
            if c != cp || h != hp {
                continue;
            }
            let ket = q.iter().chain(c).copied().collect();
            let bra = qp.iter().chain(cp).copied().collect();
            let entry = result.entry((*x, *xp, ket, bra)).or_default();
            entry.0 += a.0 * b.0 + a.1 * b.1;
            entry.1 += a.1 * b.0 - a.0 * b.1;
        }
    }
    result
}
pub(in crate::symbolic::optimize) fn assert_density(a: &[Component], b: &[Component]) {
    let a = density(a);
    let b = density(b);
    for key in a.keys().chain(b.keys()) {
        let left = a.get(key).copied().unwrap_or_default();
        let right = b.get(key).copied().unwrap_or_default();
        assert!(
            (left.0 - right.0).abs() < 1e-12 && (left.1 - right.1).abs() < 1e-12,
            "density mismatch at {key:?}: {left:?} vs {right:?}"
        );
    }
}
fn merge(components: Vec<Component>) -> Vec<Component> {
    let result = merge_components(components.clone());
    assert_density(&components, &result);
    result
}

#[test]
fn orthogonal_worlds_add_unequal_density_weights_and_ignore_global_phase() {
    let mut first = component(Scalar::sqrt(rational(3, 4)), Vec::new());
    let mut second = component(rational(1, 2), vec![discard(true)]);
    second.phase.add_boolean(
        &BooleanPolynomial::one(),
        PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(2))),
    );
    first.output.quantum.clear();

    let result = merge(vec![first, second]);

    assert_eq!(result.len(), 1);
    assert_eq!(result[0].scalar, Scalar::one());
    assert_eq!(result[0].phase, PhasePolynomial::zero());
    assert!(result[0].output.history.is_empty());
}

#[test]
fn density_merge_retains_history_shared_by_orthogonal_worlds() {
    let shared = BooleanPolynomial::variable(Variable::Path(0));
    let mut first = component(
        rational(1, 2),
        vec![
            HistoryEntry::Discard {
                value: shared.clone(),
            },
            discard(false),
        ],
    );
    let mut second = component(
        rational(1, 2),
        vec![
            HistoryEntry::Discard {
                value: shared.clone(),
            },
            discard(true),
        ],
    );
    first.path_support.insert(0);
    second.path_support.insert(0);

    let result = merge(vec![first, second]);

    assert_eq!(result.len(), 1);
    assert_eq!(
        result[0].output.history,
        vec![HistoryEntry::Discard { value: shared }]
    );
}

#[test]
fn density_merge_preserves_unequal_boolean_dependent_amplitudes() {
    let condition = BooleanPolynomial::variable(Variable::Path(0));
    let mut first = component(
        Scalar::select(condition.clone(), Scalar::one(), rational(-1, 1)),
        vec![discard(false)],
    );
    let mut second = component(
        Scalar::select(condition, rational(-1, 1), Scalar::one()),
        vec![discard(true)],
    );
    first.path_support.insert(0);
    second.path_support.insert(0);

    let result = merge(vec![first, second]);

    // sqrt(s_0(y)^2+s_1(y)^2) would erase the signed amplitude profiles and
    // introduce ket/bra coherence that the two histories do not possess.
    assert_eq!(result.len(), 2);
    assert!(result.iter().all(|value| value.output.history.len() == 1));
}

#[test]
fn density_merge_does_not_restore_coherence_between_visible_groups() {
    let output = Qubit {
        register: SymbolId(0),
        index: 0,
    };
    let mut components = Vec::new();
    for (value, histories) in [
        (false, [[false, false], [true, true]]),
        (true, [[false, true], [true, false]]),
    ] {
        for history in histories {
            let mut component =
                component(rational(1, 2), history.into_iter().map(discard).collect());
            component
                .output
                .quantum
                .insert(output.clone(), BooleanPolynomial::from(value));
            components.push(component);
        }
    }

    let result = merge(components);

    // Collapsing each output group independently would erase all histories;
    // the two representatives would then spuriously form |0><1| cross terms.
    assert_eq!(result.len(), 4);
    assert!(result.iter().all(|value| value.output.history.len() == 2));
}

#[test]
fn equal_input_dependent_scalars_keep_relative_signs() {
    let scalar = Scalar::select(x(0), rational(-1, 2), rational(1, 2));
    let mut a = component(scalar.clone(), vec![discard(false)]);
    a.output.quantum.insert(q(0), x(0));
    let mut b = a.clone();
    b.output.history = vec![discard(true)];
    let result = merge(vec![a, b]);
    assert_eq!(result.len(), 1);
    let rho = density(&result);
    // Losing the sign by taking an absolute value would flip this entry.
    assert!((rho[&(0, 1, vec![false], vec![true])].0 + 0.5).abs() < 1e-12);
}

#[test]
fn unequal_input_dependent_scalars_cannot_merge_pointwise() {
    let mut a = component(
        Scalar::select(x(0), rational(-1, 2), rational(1, 2)),
        vec![discard(false)],
    );
    a.output.quantum.insert(q(0), x(0));
    let mut b = a.clone();
    b.scalar = rational(1, 2);
    b.output.history = vec![discard(true)];
    let result = merge(vec![a, b]);
    assert_eq!(result.len(), 2);
    assert!(density(&result)[&(0, 1, vec![false], vec![true])].0.abs() < 1e-12);
}

#[test]
fn constant_shape_sectors_merge_under_the_environment_label_convention() {
    let bit = ClassicalBit {
        register: SymbolId(1),
        index: 0,
    };
    let variants = [
        vec![],
        vec![discard(true)],
        vec![HistoryEntry::Write {
            target: bit.clone(),
            value: BooleanPolynomial::zero(),
        }],
        vec![HistoryEntry::Write {
            target: ClassicalBit {
                register: SymbolId(1),
                index: 1,
            },
            value: BooleanPolynomial::zero(),
        }],
    ];
    let components: Vec<_> = variants
        .into_iter()
        .map(|history| {
            let mut c = component(rational(1, 2), history);
            c.output.quantum.insert(q(0), x(0));
            c
        })
        .collect();
    let result = merge(components);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0].scalar, Scalar::one());
}

#[test]
fn a_different_symbolic_coordinate_must_not_be_erased() {
    let mut a = component(
        rational(1, 2),
        vec![HistoryEntry::Discard { value: x(0) }, discard(false)],
    );
    a.output.quantum.insert(q(0), x(0));
    let mut b = a.clone();
    b.output.history = vec![HistoryEntry::Discard { value: x(1) }, discard(true)];
    assert_eq!(merge(vec![a, b]).len(), 2);
}

#[test]
fn relative_input_phase_blocks_density_merge() {
    let mut a = component(rational(1, 2), vec![discard(false)]);
    a.output.quantum.insert(q(0), x(0));
    let mut b = a.clone();
    b.output.history = vec![discard(true)];
    b.phase.add_boolean(
        &x(0),
        PhaseCoefficient::rational(BigRational::new(1.into(), 2.into())),
    );
    assert_eq!(merge(vec![a, b]).len(), 2);
}

#[test]
fn nested_branch_merges_preserve_outer_measurement_sectors() {
    use crate::symbolic::{ExecutionConfig, OutputSelection, execute};
    let prefix = "OPENQASM 3.0; include \"stdgates.inc\"; qubit[2] q; bit[2] c;";
    let nested = format!(
        "{prefix}
        h q[0]; c[0] = measure q[0];
        if (c[0]) {{
            reset q[1]; h q[1]; c[1] = measure q[1];
            if (c[1]) {{ reset q[1]; }} else {{ reset q[1]; }}
        }} else {{
            reset q[1]; h q[1]; c[1] = measure q[1];
            if (c[1]) {{ reset q[1]; }} else {{ reset q[1]; }}
        }}"
    );
    // Both inner branches reset q[1]. The outer measurement must still
    // dephase q[0], including when c[0] is no longer a selected output.
    let reference = format!("{prefix} h q[0]; c[0] = measure q[0]; reset q[1];");
    let run = |source: &str| {
        let program = crate::frontend::openqasm3::parse_str(source, "merge.qasm").unwrap();
        let register = program.quantum_registers[0].id;
        execute(
            &program,
            &ExecutionConfig::all_symbolic(),
            &OutputSelection::new((0..2).map(|index| Qubit { register, index }), []),
        )
        .unwrap()
    };
    let actual = run(&nested);
    let expected = run(&reference);
    assert_density(&actual.components, &expected.components);
    assert!(
        density(&actual.components)
            .iter()
            .all(|((_, _, q, qp), value)| {
                q == qp || (value.0.abs() < 1e-12 && value.1.abs() < 1e-12)
            })
    );
}
