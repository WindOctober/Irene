use super::*;
use crate::ir::{Qubit, SymbolId};

fn path(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(i))
}

#[test]
fn truth_table_evaluates_factored_graphs() {
    let product = (0..8).fold(BooleanPolynomial::one(), |p, i| {
        p.and(&path(i).complement())
    });
    let inconsistent = TruthTableGuard::build(&[product.complement(), path(0).complement()])
        .expect("bounded support");
    assert!(inconsistent.satisfying.is_empty());
    let consistent =
        TruthTableGuard::build(&[product.complement(), path(0)]).expect("bounded support");
    assert_eq!(consistent.satisfying.len(), 1);
}

#[test]
fn oversized_guards_are_retained_not_declared_unsatisfiable() {
    let product = (0..20).fold(BooleanPolynomial::one(), |p, i| {
        p.and(&path(i).complement())
    });
    assert!(product.expanded_terms(1024).is_none());
    for guard in [
        vec![product.complement(), path(0).complement()],
        vec![product.complement(), path(0)],
    ] {
        assert!(TruthTableGuard::build(&guard).is_none());
        assert!(matches!(
            solve_nonlinear_guard(&guard, &(0..20).collect()),
            Inference::None
        ));
    }
}

#[test]
fn empty_support_distinguishes_true_and_false_guards() {
    assert_eq!(TruthTableGuard::build(&[]).unwrap().satisfying.len(), 1);
    assert!(matches!(
        solve_nonlinear_guard(&[BooleanPolynomial::one()], &BTreeSet::new()),
        Inference::Unsatisfiable
    ));
}

#[test]
fn support_limit_is_inclusive() {
    let guard: Vec<_> = (0..MAX_NONLINEAR_GUARD_VARIABLES).map(path).collect();
    let table = TruthTableGuard::build(&guard).expect("exactly at the bound");
    assert_eq!(table.satisfying.len(), 1);
}

#[test]
fn implications_preserve_every_three_variable_boolean_relation() {
    // Two free input bits and one owned bound path. Test every possible guard
    // function, not a particular normal form or replacement choice.
    let variables = [
        Variable::Input(Qubit {
            register: SymbolId(0),
            index: 0,
        }),
        Variable::Input(Qubit {
            register: SymbolId(0),
            index: 1,
        }),
        Variable::Path(0),
    ];
    let bits = variables.clone().map(BooleanPolynomial::variable);
    let eval = |p: &BooleanPolynomial, assignment: usize| {
        p.evaluate::<std::convert::Infallible>(|v| {
            let i = variables.iter().position(|x| x == v).unwrap();
            Ok(assignment & (1 << i) != 0)
        })
        .unwrap()
    };
    for function in 0usize..256 {
        let mut equation = BooleanPolynomial::zero();
        for assignment in 0..8 {
            if function & (1 << assignment) == 0 {
                continue;
            }
            let mut cube = BooleanPolynomial::one();
            for (i, bit) in bits.iter().enumerate() {
                cube = cube.and(&if assignment & (1 << i) == 0 {
                    bit.complement()
                } else {
                    bit.clone()
                });
            }
            equation = equation.xor(&cube);
        }
        let guard = [equation.clone()];
        let table = TruthTableGuard::build(&guard).unwrap();
        let accepted = (0..8).filter(|a| !eval(&equation, *a)).count();
        // Missing variables are not enumerated by the guard table.
        assert_eq!(
            table.satisfying.len() << (3 - table.positions.len()),
            accepted
        );
        match solve_nonlinear_guard(&guard, &[0].into()) {
            Inference::Unsatisfiable => assert_eq!(accepted, 0),
            Inference::Substitute(variable, replacement) => {
                assert_eq!(variable, Variable::Path(0));
                assert!(!replacement.variables().contains(&variable));
                let substituted = equation.substitute(&variable, &replacement);
                for assignment in 0..8 {
                    let original = !eval(&equation, assignment);
                    let reduced = !eval(&substituted, assignment)
                        && (eval(&bits[2], assignment) == eval(&replacement, assignment));
                    assert_eq!(
                        original, reduced,
                        "function={function}, assignment={assignment}"
                    );
                }
            }
            Inference::None => {}
        }
        assert!(!matches!(
            solve_nonlinear_guard(&guard, &BTreeSet::new()),
            Inference::Substitute(..)
        ));
    }
}

#[test]
fn path_substitutions_only_reference_earlier_paths() {
    for complement in [false, true] {
        let mut equation = path(1).xor(&path(0));
        if complement {
            equation = equation.complement();
        }
        let Inference::Substitute(variable, replacement) =
            solve_nonlinear_guard(&[equation], &[0, 1].into())
        else {
            panic!("expected an implied relation")
        };
        assert_eq!(variable, Variable::Path(1));
        assert_eq!(
            replacement,
            if complement {
                path(0).complement()
            } else {
                path(0)
            }
        );
    }
}
