use super::*;
use crate::ir::{AstIdGenerator, ClassicalBit, NumericExprKind};
use crate::symbolic::{Component, HybridMemory};

fn ratio(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

fn component() -> Component {
    Component {
        guard: vec![],
        scalar: Scalar::one(),
        path_support: BTreeSet::new(),
        phase: PhasePolynomial::zero(),
        output: HybridMemory::default(),
    }
}

fn path(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(i))
}

fn target(i: usize) -> KernelVariable {
    KernelVariable::PathKet { term: 0, path: i }
}

#[test]
fn conversion_preserves_unsquared_weight_and_unconjugated_phase() {
    let mut c = component();
    c.path_support = [2, 9].into(); // Path 9 is deliberately unused.
    c.scalar = Scalar::rational(ratio(3, 2));
    c.phase
        .add_boolean(&path(2), PhaseCoefficient::rational(ratio(1, 4)));
    let before = c.clone();
    let (paths, guards, weight, phase) = closed_scalar_parts(&c).unwrap();
    assert_eq!(paths, [target(2), target(9)].into());
    assert!(guards.is_empty());
    assert_eq!(weight, KernelScalar::Rational(ratio(3, 2)));
    let terms: Vec<_> = phase.selectors().collect();
    assert_eq!(terms.len(), 1);
    assert_eq!(terms[0].0.variables(), [target(2)].into());
    assert_eq!(terms[0].1.as_rational(), Some(ratio(1, 4)));
    assert_eq!(c, before);
}

#[test]
fn guard_phase_and_scalar_boolean_functions_are_preserved() {
    let mut c = component();
    c.path_support = [2, 9].into();
    let expression = path(2).xor(&path(2).and(&path(9)));
    c.guard.push(expression.clone());
    c.phase
        .add_boolean(&expression, PhaseCoefficient::rational(ratio(1, 4)));
    c.scalar = Scalar::select(
        expression.clone(),
        Scalar::rational(ratio(-2, 1)),
        Scalar::rational(ratio(3, 1)),
    );
    let (_, guards, weight, phase) = closed_scalar_parts(&c).unwrap();
    let KernelScalar::Select {
        condition,
        when_true,
        when_false,
    } = weight
    else {
        panic!("select required")
    };
    assert_eq!(*when_true, KernelScalar::Rational(ratio(-2, 1)));
    assert_eq!(*when_false, KernelScalar::Rational(ratio(3, 1)));
    for mask in 0..4 {
        let value = |i| match i {
            2 => mask & 1 != 0,
            9 => mask & 2 != 0,
            _ => panic!("unexpected path"),
        };
        let expected = expression
            .evaluate::<std::convert::Infallible>(|v| match v {
                Variable::Path(i) => Ok(value(*i)),
                _ => panic!("free input"),
            })
            .unwrap();
        let eval = |p: &KernelBooleanPolynomial| {
            p.as_graph()
                .evaluate::<std::convert::Infallible>(
                    |v| match KernelVariable::from_graph_variable(v) {
                        KernelVariable::PathKet { term: 0, path } => Ok(value(path)),
                        _ => panic!("unexpected namespace"),
                    },
                )
                .unwrap()
        };
        assert_eq!(eval(&guards[0]), expected);
        assert_eq!(eval(&condition), expected);
        let actual: BigRational = phase
            .selectors()
            .filter(|(p, _)| eval(p))
            .map(|(_, c)| c.as_rational().unwrap())
            .sum();
        // Phase coefficients are canonical modulo a full turn. Expanding a
        // Boolean selector can change the real sum by an integer, not its phase.
        let expected_turns = if expected { ratio(1, 4) } else { ratio(0, 1) };
        assert!((actual - expected_turns).is_integer());
    }
}

#[test]
fn rejects_free_inputs_and_undeclared_paths_in_every_boolean_position() {
    for v in [
        Variable::Path(7),
        Variable::Input(Qubit {
            register: SymbolId(0),
            index: 0,
        }),
    ] {
        for position in 0..3 {
            let mut c = component();
            c.path_support.insert(2);
            let p = BooleanPolynomial::variable(v.clone());
            match position {
                0 => c.guard.push(p),
                1 => c
                    .phase
                    .add_boolean(&p, PhaseCoefficient::rational(ratio(1, 4))),
                2 => c.scalar = Scalar::select(p, Scalar::rational(ratio(2, 1)), Scalar::one()),
                _ => unreachable!(),
            }
            assert!(
                closed_scalar_parts(&c).is_none(),
                "{v:?} position {position}"
            );
        }
    }
}

#[test]
fn outputs_and_history_cannot_be_silently_discarded() {
    for position in 0..3 {
        let mut c = component();
        match position {
            0 => {
                c.output.quantum.insert(
                    Qubit {
                        register: SymbolId(0),
                        index: 0,
                    },
                    BooleanPolynomial::zero(),
                );
            }
            1 => {
                c.output.classical.insert(
                    ClassicalBit {
                        register: SymbolId(1),
                        index: 0,
                    },
                    BooleanPolynomial::zero(),
                );
            }
            2 => c.output.history.push(HistoryEntry::Discard {
                value: BooleanPolynomial::zero(),
            }),
            _ => unreachable!(),
        }
        assert!(closed_scalar_parts(&c).is_none());
    }
}

#[test]
fn numeric_expression_admission_is_left_to_the_consumer() {
    let mut ids = AstIdGenerator::default();
    let angle = ids.node(NumericExprKind::Input(SymbolId(3)));
    let mut c = component();
    c.scalar = Scalar::sin(angle.clone());
    let (_, _, weight, _) = closed_scalar_parts(&c).unwrap();
    assert_eq!(weight, KernelScalar::Sin(angle));
}

#[test]
fn constant_and_empty_sums_keep_their_amplitudes() {
    for r in [ratio(0, 1), ratio(-1, 1), ratio(1, 2)] {
        let mut c = component();
        c.scalar = Scalar::rational(r.clone());
        let (paths, guards, weight, phase) = closed_scalar_parts(&c).unwrap();
        assert!(paths.is_empty() && guards.is_empty());
        assert_eq!(phase.selectors().count(), 0);
        assert_eq!(weight, KernelScalar::Rational(r));
    }
}
