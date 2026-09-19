use super::*;
use crate::ir::{ClassicalBit, Qubit, SymbolId};
use crate::symbolic::{HistoryEntry, HybridMemory, PhaseCoefficient, PhasePolynomial};

fn x(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Input(Qubit {
        register: SymbolId(0),
        index: i,
    }))
}
fn y() -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(0))
}
fn fixture() -> Component {
    Component {
        guard: vec![],
        scalar: Scalar::one(),
        path_support: [0].into(),
        phase: PhasePolynomial::zero(),
        output: HybridMemory::default(),
    }
}
fn hidden_xor(a: &BooleanPolynomial, b: &BooleanPolynomial) -> BooleanPolynomial {
    a.and(&b.complement()).xor(&a.complement().and(b))
}
fn check_density(before: &Component, after: &Component) {
    super::super::assert_density(std::slice::from_ref(before), std::slice::from_ref(after));
}

#[test]
fn recovered_affine_pivot_updates_every_semantic_field() {
    let mut c = fixture();
    c.guard.push(hidden_xor(&y(), &x(0)));
    let q = Qubit {
        register: SymbolId(0),
        index: 0,
    };
    let bit = ClassicalBit {
        register: SymbolId(1),
        index: 0,
    };
    c.output.quantum.insert(q.clone(), y());
    c.output.classical.insert(bit.clone(), y().xor(&x(1)));
    c.output.history.push(HistoryEntry::Write {
        target: bit,
        value: y(),
    });
    c.scalar = Scalar::select(
        y(),
        Scalar::one(),
        Scalar::rational(BigRational::from_integer(2.into())),
    );
    c.phase.add_boolean(
        &y(),
        PhaseCoefficient::rational(BigRational::new(1.into(), 8.into())),
    );
    let before = c.clone();
    assert!(simplify_component(&mut c));
    assert!(c.path_support.is_empty());
    assert!(c.guard.is_empty());
    assert_eq!(c.output.quantum[&q], x(0));
    check_density(&before, &c);
}

#[test]
fn free_input_relation_is_retained_and_not_repeatedly_appended() {
    let mut c = fixture();
    c.path_support.clear();
    let original = hidden_xor(&x(0), &x(1));
    c.guard.push(original.clone());
    let before = c.clone();
    assert!(simplify_component(&mut c));
    assert!(c.guard.contains(&original));
    assert!(c.guard.contains(&x(0).xor(&x(1))));
    assert!(!c.guard.is_empty());
    check_density(&before, &c);
    let count = c.guard.len();
    for _ in 0..3 {
        assert!(simplify_component(&mut c));
        assert_eq!(c.guard.len(), count);
    }
}

#[test]
fn original_product_columns_survive_factoring() {
    let a = x(0);
    let b = x(1);
    let d = x(2);
    let z = x(3);
    let w = x(4);
    let mut c = fixture();
    // The formal row XOR directly yields y = z XOR w, without expansion.
    c.guard = vec![
        a.and(&b).xor(&a.and(&d)).xor(&y()),
        a.and(&b).xor(&z),
        a.and(&d).xor(&w),
    ];
    let q = Qubit {
        register: SymbolId(0),
        index: 0,
    };
    c.output.quantum.insert(q.clone(), y());
    let before = c.clone();
    assert!(simplify_component(&mut c));
    assert!(!c.path_support.contains(&0));
    for input in 0..32 {
        let eval = |p: &BooleanPolynomial, path: bool| {
            p.evaluate::<std::convert::Infallible>(|v| {
                Ok(match v {
                    Variable::Input(q) => input & (1 << q.index) != 0,
                    Variable::Path(0) => path,
                    _ => panic!("unexpected variable"),
                })
            })
            .unwrap()
        };
        let witnesses: Vec<_> = [false, true]
            .into_iter()
            .filter(|value| before.guard.iter().all(|g| !eval(g, *value)))
            .collect();
        let reachable = c.guard.iter().all(|g| !eval(g, false));
        assert_eq!(reachable, !witnesses.is_empty());
        if reachable {
            assert_eq!(witnesses.len(), 1);
            assert_eq!(eval(&c.output.quantum[&q], false), witnesses[0]);
        }
    }
}

#[test]
fn contradictory_normalized_rows_reject_the_component() {
    let mut c = fixture();
    c.guard = vec![hidden_xor(&y(), &x(0)), y().xor(&x(0)).complement()];
    assert!(!simplify_component(&mut c));
}

#[test]
fn zero_rows_are_removed_without_eliminating_free_inputs() {
    let mut c = fixture();
    c.path_support.clear();
    let zero = hidden_xor(&x(0), &x(1)).xor(&x(0)).xor(&x(1));
    c.guard.push(zero);
    let before = c.clone();
    assert!(simplify_component(&mut c));
    assert!(c.guard.is_empty());
    check_density(&before, &c);
}

#[test]
fn factoring_live_values_preserves_density_and_history() {
    let mut c = fixture();
    let value = x(0).and(&x(1)).xor(&x(0).and(&x(1).complement()));
    let q = Qubit {
        register: SymbolId(0),
        index: 0,
    };
    c.output.quantum.insert(q, value.clone());
    c.output.classical.insert(
        ClassicalBit {
            register: SymbolId(1),
            index: 0,
        },
        value.clone(),
    );
    c.output.history.push(HistoryEntry::Discard { value });
    let before = c.clone();
    assert!(simplify_component(&mut c));
    check_density(&before, &c);
}
