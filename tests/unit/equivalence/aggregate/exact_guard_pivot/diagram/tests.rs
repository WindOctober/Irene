use super::*;
#[test]
fn distinct_streaming_export_keeps_the_expanded_term_cap() {
    let x = KernelMonomial::variable(KernelVariable::InputKet(0));
    let mut p = KernelBooleanPolynomial::zero();
    assert!(p.insert_distinct_monomial(x.clone()));
    assert!(!p.insert_distinct_monomial(x));
    assert_eq!(
        p,
        KernelBooleanPolynomial::variable(KernelVariable::InputKet(0))
    );

    // All monomials of degree <=3 on100 variables:166751 DISTINCT terms,
    // <750000 total literal cells, but over the100000 TERM limit. A compact
    // DAG and ample TEST work cannot authorize this expanded result.
    let mut arena = Arena::default();
    let mut work = 20_000_000;
    let mut sums = [1usize; 4];
    for i in (0..100).rev() {
        for degree in (1..4).rev() {
            sums[degree] = arena
                .make(
                    KernelVariable::InputKet(i),
                    sums[degree],
                    sums[degree - 1],
                    &mut work,
                )
                .unwrap();
        }
    }
    assert!(arena.export(sums[3], &mut work).is_none());
    assert!(work > 0); // Explicit output refusal, not exhausted test work.
}
#[test]
fn prefix_import_handles_reordering_omission_and_duplicate_cancellation() {
    let vars = [
        KernelVariable::InputKet(0),
        KernelVariable::InputBra(0),
        KernelVariable::PathKet { term: 2, path: 1 },
    ];
    for mask in 0..256 {
        let p = KernelBooleanPolynomial::from_monomials(
            (0..8).filter(|i| mask & (1 << i) != 0).map(|i| {
                KernelMonomial::from_variables(
                    vars.iter()
                        .enumerate()
                        .filter(|(j, _)| i & (1 << j) != 0)
                        .map(|(_, v)| v.clone()),
                )
            }),
        );
        let rows = p.terms().collect::<Vec<_>>();
        for omit in [None, Some(&vars[0]), Some(&vars[1]), Some(&vars[2])] {
            let mut arena = Arena::default();
            let mut work = 1_000_000;
            let root = arena
                .import(rows.iter().rev().copied(), omit, &mut work)
                .unwrap();
            let expected = omit.map_or_else(
                || p.clone(),
                |v| p.substitute(v, &KernelBooleanPolynomial::one()),
            );
            assert_eq!(arena.export(root, &mut work).unwrap(), expected);
            let duplicate = arena
                .import(rows.iter().chain(&rows).copied(), omit, &mut work)
                .unwrap();
            assert_eq!(duplicate, 0);
        }
    }
    let deep = KernelMonomial::from_variables((0..129).map(KernelVariable::InputKet));
    assert!(
        Arena::default()
            .import(std::iter::once(&deep), None, &mut 1_000_000)
            .is_none()
    );
}
#[test]
fn complete_anf_operations_match_all_boolean_entries() {
    let vars = [
        KernelVariable::InputKet(7),
        KernelVariable::ClassicalOutput(2),
        KernelVariable::PathBra { term: 5, path: 9 },
    ];
    let polynomial = |mask: usize| {
        KernelBooleanPolynomial::from_monomials((0..8).filter(|i| mask & (1 << i) != 0).map(
            |i| {
                KernelMonomial::from_variables(
                    vars.iter()
                        .enumerate()
                        .filter(|(j, _)| i & (1 << j) != 0)
                        .map(|(_, v)| v.clone()),
                )
            },
        ))
    };
    let eval = |p: &KernelBooleanPolynomial, bits: usize| {
        p.terms().fold(false, |r, m| {
            r ^ m
                .variables()
                .all(|v| bits & (1 << vars.iter().position(|w| w == v).unwrap()) != 0)
        })
    };
    for a in 0..256 {
        let pa = polynomial(a);
        let mut arena = Arena::default();
        let mut work = 1_000_000;
        let ia = arena.import(pa.terms(), None, &mut work).unwrap();
        assert_eq!(arena.export(ia, &mut work).unwrap(), pa);
        for b in (0..256).step_by(17) {
            let pb = polynomial(b);
            let ib = arena.import(pb.terms(), None, &mut work).unwrap();
            let product = arena.product(ia, ib, &mut work, 0).unwrap();
            let xor = arena.xor(ia, ib, &mut work, 0).unwrap();
            let out = arena.export(product, &mut work).unwrap();
            let sum = arena.export(xor, &mut work).unwrap();
            for bits in 0..8 {
                assert_eq!(eval(&out, bits), eval(&pa, bits) & eval(&pb, bits));
                assert_eq!(eval(&sum, bits), eval(&pa, bits) ^ eval(&pb, bits));
            }
            assert_eq!(out, pa.and(&pb));
            assert_eq!(sum, pa.xor(&pb));
        }
    }
}
#[test]
fn diagrams_bound_expanded_output_and_storage() {
    let mut arena = Arena::default();
    let mut work = 1_000_000;
    // 18 shared nodes represent 2^18 DISTINCT ANF terms; export must refuse.
    let mut large = 1;
    for i in (0..18).rev() {
        large = arena
            .make(KernelVariable::InputKet(i), large, large, &mut work)
            .unwrap();
    }
    assert_eq!(arena.product(large, large, &mut work, 0), Some(large));
    assert!(arena.export(large, &mut work).is_none());
    assert!(
        arena
            .make(KernelVariable::InputKet(0), large, 1, &mut work)
            .is_none()
    );
    let mut work = 1_000_000;
    let mut arena = Arena::default();
    for i in 0..MAX_NODES {
        assert!(
            arena
                .make(KernelVariable::InputKet(i), 0, 1, &mut work)
                .is_some()
        );
    }
    assert!(
        arena
            .make(KernelVariable::InputBra(0), 0, 1, &mut work)
            .is_none()
    );
    assert_eq!(arena.nodes.len(), MAX_NODES);
    assert!(arena.xor(1, 2, &mut 0, 0).is_none());
}
