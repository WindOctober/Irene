use super::*;
use std::convert::Infallible;

fn v(i: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(i))
}
fn value(p: &BooleanPolynomial, bits: u64) -> bool {
    p.evaluate::<Infallible>(|v| match v {
        Variable::Path(i) => Ok(bits & (1u64 << i) != 0),
        _ => unreachable!(),
    })
    .unwrap()
}

#[test]
fn graph_factoring_preserves_every_assignment() {
    let atoms = [v(0), v(1), v(2), v(0).xor(&v(1)), v(2).complement()];
    for a in &atoms {
        for b in &atoms {
            for c in &atoms {
                let source = a.and(b).xor(&a.and(c)).xor(b);
                let factored = source.factored();
                for bits in 0..8 {
                    assert_eq!(value(&source, bits), value(&factored, bits));
                }
            }
        }
    }
}

#[test]
fn graph_factoring_preserves_all_assignments_of_shared_boolean_circuits() {
    for seed in 1..=96_u64 {
        let mut state = seed;
        let mut pool: Vec<_> = (0..6).map(v).chain([BooleanPolynomial::one()]).collect();
        for _ in 0..32 {
            state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
            let a = &pool[(state as usize) % pool.len()];
            let b = &pool[((state >> 32) as usize) % pool.len()];
            let next = match (state >> 16) % 3 {
                0 => a.xor(b),
                1 => a.and(b),
                _ => a.xor(&a.and(b)).complement(),
            };
            pool.push(next);
        }
        for original in pool.iter().skip(7) {
            let reduced = original.factored();
            for bits in 0..64 {
                assert_eq!(
                    value(original, bits),
                    value(&reduced, bits),
                    "seed={seed}, bits={bits}"
                );
            }
        }
    }
}

#[test]
fn normalized_node_cache_reuses_results_without_retaining_the_source_root() {
    let original = v(0).and(&v(1).xor(&v(2))).xor(&v(0).and(&v(1).xor(&v(3))));
    let source = std::sync::Arc::downgrade(&original.0);
    let reduced = original.factored();
    assert!(std::sync::Arc::ptr_eq(&reduced.0, &original.factored().0));
    drop(original);
    assert!(source.upgrade().is_none());

    let stable = v(0).xor(&v(1));
    let source = std::sync::Arc::downgrade(&stable.0);
    assert!(std::sync::Arc::ptr_eq(&stable.0, &stable.factored().0));
    drop(stable);
    assert!(
        source.upgrade().is_none(),
        "normal-form markers must not retain self"
    );
}

#[test]
fn populating_normalization_caches_does_not_change_ordered_keys() {
    let keys = (0..32)
        .map(|i| {
            v(i).and(&v(40).xor(&v(41)))
                .xor(&v(i).and(&v(40).xor(&v(42))))
        })
        .collect::<Vec<_>>();
    let set = keys.iter().cloned().collect::<BTreeSet<_>>();
    let before = set.iter().cloned().collect::<Vec<_>>();
    for key in keys.iter().rev() {
        key.factored();
    }
    assert_eq!(set.iter().cloned().collect::<Vec<_>>(), before);
    assert!(keys.iter().all(|key| set.contains(key)));
}
