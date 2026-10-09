use super::super::tests::{c, component, hps, q, x, y};
use super::*;

fn cycle(n: usize) -> Component {
    let mut value = component(&(0..n).collect::<Vec<_>>(), x(0));
    value.guard = (0..n).map(|i| y(i).xor(&y((i + 1) % n))).collect();
    value
}

#[test]
fn vf2_resolves_symmetric_cycles() {
    let source = cycle(12);
    for seed in 0..8 {
        let map = (0..12).map(|i| (i, 100 + (i * 5 + seed) % 12)).collect();
        let mut renamed = rename_component(&source, &map);
        renamed.guard.reverse();
        {
            let (common, left, right) = pair(&source, &renamed).unwrap();
            assert!(left.verify(&source, &common));
            assert!(right.verify(&renamed, &common));
        }
    }
}

#[test]
fn every_semantic_field_uses_one_mapping_and_exact_labels() {
    let mut source = component(&[3, 7, 10], y(3).and(&y(7).xor(&x(0))));
    source.guard = vec![y(7).xor(&y(10)), y(7).xor(&y(10))];
    source.scalar = Scalar::Select {
        condition: y(3),
        when_true: Box::new(Scalar::one()),
        when_false: Box::new(Scalar::zero()),
    };
    source.phase.add_boolean(
        &y(7),
        PhaseCoefficient::rational(BigRational::new(1.into(), 8.into())),
    );
    source.output.classical.insert(c(0), y(10));
    source.output.history = vec![
        HistoryEntry::Discard { value: y(3) },
        HistoryEntry::Write {
            target: c(1),
            value: y(7),
        },
    ];
    let mut changed = vec![];
    let mut add = |f: &dyn Fn(&mut Component)| {
        let mut s = source.clone();
        f(&mut s);
        changed.push(s);
    };
    add(&|s| s.guard.pop().map(|_| ()).unwrap());
    add(&|s| s.output.quantum.insert(q(0), x(1)).map(|_| ()).unwrap());
    add(&|s| s.output.classical.insert(c(0), y(3)).map(|_| ()).unwrap());
    add(&|s| s.output.history.reverse());
    add(&|s| {
        s.output.history[1] = HistoryEntry::Write {
            target: c(2),
            value: y(7),
        }
    });
    add(&|s| {
        s.scalar = Scalar::Select {
            condition: y(7),
            when_true: Box::new(Scalar::one()),
            when_false: Box::new(Scalar::zero()),
        }
    });
    add(&|s| {
        s.phase.add_boolean(
            &y(7),
            PhaseCoefficient::rational(BigRational::new(1.into(), 8.into())),
        )
    });
    let map = BTreeMap::from([(3, 81), (7, 21), (10, 42)]);
    {
        assert!(pair(&source, &rename_component(&source, &map)).is_some());
        for other in &changed {
            assert!(pair(&source, &rename_component(other, &map)).is_none());
        }
    }
}

#[test]
fn unused_paths_and_allocation_sharing_do_not_change_results() {
    let shared = y(2).and(&x(0));
    let mut source = component(&[2, 9], shared.clone());
    source.guard = vec![shared];
    let mut other = component(&[15, 90], y(15).and(&x(0)));
    other.guard = vec![y(15).and(&x(0))];
    {
        assert!(pair(&source, &other).is_some());
    }
}

#[test]
fn vf2_handles_graphs_above_the_old_pilot_cutoff() {
    let n = 1400;
    let mut source = component(&(0..n).collect::<Vec<_>>(), x(0));
    source.guard = (0..n)
        .map(|i| {
            let input = BooleanPolynomial::variable(Variable::Input(q(i)));
            y(i).xor(&input)
        })
        .collect();
    assert!(SyntaxGraph::build(&source).unwrap().graph.node_count() > 4000);
    let map = (0..n)
        .map(|i| (i, 10000 + if i < 2 { 1 - i } else { i }))
        .collect();
    let other = rename_component(&source, &map);
    assert!(direct_pair(&source, &other).is_none());
    let (common, a, b) = pair(&source, &other).unwrap();
    assert!(a.verify(&source, &common));
    assert!(b.verify(&other, &common));
}

#[test]
fn repeated_components_are_not_deduplicated() {
    let a = component(&[3], y(3));
    let b = component(&[8], y(8));
    assert!(matches!(
        exact_match(
            &hps(vec![a.clone(), a.clone()]),
            &hps(vec![b.clone(), b.clone()])
        ),
        ExactMatch::Match { .. }
    ));
    let different = component(&[8], y(8).xor(&x(0)));
    assert_eq!(
        exact_match(&hps(vec![a.clone(), a]), &hps(vec![b, different])),
        ExactMatch::NoMatch
    );
    assert!(matches!(
        exact_match(&hps(vec![]), &hps(vec![])),
        ExactMatch::Match { .. }
    ));
}

#[test]
fn certificate_rejects_a_non_bijection_and_field_tampering() {
    let source = component(&[3, 7], y(3).xor(&y(7)));
    let (value, mut certificate) = numbered(&source, BTreeMap::from([(3, 0), (7, 1)]));
    assert!(certificate.verify(&source, &value));
    let mut changed = value.clone();
    changed.scalar = Scalar::zero();
    assert!(!certificate.verify(&source, &changed));
    certificate.forward.insert(7, 0);
    assert!(!certificate.verify(&source, &value));
}

#[test]
fn malformed_paths_and_fixed_input_identities_are_never_certified() {
    {
        let value = hps(vec![component(&[0], y(1))]);
        assert!(!matches!(
            exact_match(&value, &value),
            ExactMatch::Match { .. }
        ));
        let mut a = hps(vec![component(&[0], y(0))]);
        a.input.quantum.insert(q(0), y(0));
        assert!(!matches!(exact_match(&a, &a), ExactMatch::Match { .. }));
        let a = hps(vec![component(&[0], y(0).xor(&x(0)))]);
        let b = hps(vec![component(&[8], y(8).xor(&x(1)))]);
        assert!(!matches!(exact_match(&a, &b), ExactMatch::Match { .. }));
    }
}
