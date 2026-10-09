//! Incremental node/edge accounting, with the same per-root DAG semantics as
//! `BooleanPolynomial::storage_size`. Identity here is only for storage, not
//! a Boolean equivalence test.
use super::{BooleanPolynomial, Expression};
use std::collections::HashMap;

/// Incremental storage for one changing root (for example one modular bit).
#[derive(Default)]
pub(crate) struct RootStorage {
    // Own the root while address-keyed entries exist, preventing address reuse.
    root: Option<BooleanPolynomial>,
    references: HashMap<usize, usize>,
    size: usize,
}

impl RootStorage {
    pub(crate) fn update(&mut self, root: BooleanPolynomial) -> usize {
        // Add first: surviving subgraphs stay live and are never revisited.
        self.adjust(&root, true);
        if let Some(old) = self.root.take() {
            self.adjust(&old, false);
        }
        self.root = Some(root);
        self.size
    }

    fn adjust(&mut self, root: &BooleanPolynomial, add: bool) {
        let mut pending = vec![root];
        while let Some(node) = pending.pop() {
            let key = node.key();
            if add {
                let references = self.references.entry(key).or_default();
                *references += 1;
                if *references != 1 {
                    continue;
                }
            } else {
                let references = self.references.get_mut(&key).expect("live storage node");
                *references -= 1;
                if *references != 0 {
                    continue;
                }
                self.references.remove(&key);
            }
            let weight = match node.expression() {
                Expression::Xor(children) | Expression::And(children) => {
                    pending.extend(children);
                    1 + children.len()
                }
                _ => 1,
            };
            if add {
                self.size += weight;
            } else {
                self.size -= weight;
            }
        }
    }
}

/// Counts each root's reachable nodes and edges separately, even when roots
/// share subgraphs. Root multiplicity is preserved. Only changed roots update
/// their reachability counts; retired counters do not retain historical DAGs.
#[derive(Default)]
pub(crate) struct StorageCounter {
    roots: HashMap<usize, RootStorage>,
}

impl StorageCounter {
    pub(crate) fn update(&mut self, roots: impl IntoIterator<Item = BooleanPolynomial>) -> usize {
        let mut wanted = HashMap::new();
        for root in roots {
            let entry = wanted.entry(root.key()).or_insert((root, 0usize));
            entry.1 += 1;
        }
        let mut next = HashMap::with_capacity(wanted.len());
        let mut retired = Vec::new();
        let mut total = 0;
        for (key, counter) in self.roots.drain() {
            if let Some((_, multiplicity)) = wanted.remove(&key) {
                total += counter.size * multiplicity;
                next.insert(key, counter);
            } else {
                retired.push(counter);
            }
        }
        for (key, (root, multiplicity)) in wanted {
            let mut counter = retired.pop().unwrap_or_default();
            counter.update(root);
            total += counter.size * multiplicity;
            next.insert(key, counter);
        }
        self.roots = next;
        total
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symbolic::Variable;

    #[test]
    fn incremental_counts_match_full_walk_through_sharing_and_cancellation() {
        let variables: Vec<_> = (0..12)
            .map(|v| BooleanPolynomial::variable(Variable::Path(v)))
            .collect();
        let mut counter = StorageCounter::default();
        let mut single = RootStorage::default();
        let mut roots = vec![variables[0].clone(); 3];
        for step in 0..200 {
            let shared = roots[0].xor(&variables[step % variables.len()]);
            roots = vec![
                shared.and(&variables[(step + 1) % variables.len()]),
                shared.xor(&variables[(step + 2) % variables.len()]),
                shared.clone(),
                shared,
            ];
            if step % 7 == 0 {
                roots.truncate(1);
            }
            if step % 13 == 0 {
                roots = vec![variables[step % variables.len()].clone(); 2];
            }
            let expected: usize = roots.iter().map(BooleanPolynomial::storage_size).sum();
            assert_eq!(counter.update(roots.clone()), expected);
            assert_eq!(counter.update(roots.clone()), expected);
            assert_eq!(single.update(roots[0].clone()), roots[0].storage_size());
        }
        assert_eq!(counter.update([]), 0);
        assert_eq!(counter.update([BooleanPolynomial::zero()]), 1);
    }

    #[test]
    fn reconvergent_children_and_distinct_equal_roots_keep_original_accounting() {
        let a = BooleanPolynomial::variable(Variable::Path(0));
        let b = BooleanPolynomial::variable(Variable::Path(1));
        let shared = a.and(&b);
        let left = shared.xor(&BooleanPolynomial::variable(Variable::Path(2)));
        let right = shared.xor(&BooleanPolynomial::variable(Variable::Path(3)));
        let joined = left.and(&right);
        let mut counter = StorageCounter::default();
        for roots in [
            vec![joined.clone()],
            vec![left.clone(), right.clone(), joined.clone()],
            vec![left, right],
            vec![joined.clone(), joined],
            vec![BooleanPolynomial::zero(), BooleanPolynomial::zero()],
            vec![],
        ] {
            let expected: usize = roots.iter().map(BooleanPolynomial::storage_size).sum();
            assert_eq!(counter.update(roots), expected);
        }
    }
}
