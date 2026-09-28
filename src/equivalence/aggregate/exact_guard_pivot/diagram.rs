//! Ordered ANF coefficient DAG: (x,a,b) means a XOR x*b. Full tuple interning,
//! complete Boolean-ring operations and bounded expansion; never sampled EQ.
use super::*;
const MAX_NODES: usize = 16384;
const MAX_MEMO: usize = 32768;
const MAX_DEPTH: usize = 128;

struct Node {
    variable: KernelVariable,
    low: usize,
    high: usize,
}

#[derive(Default)]
struct Prefix<'a> {
    constant: bool,
    children: BTreeMap<&'a KernelVariable, usize>,
}

#[derive(Default)]
pub(super) struct Arena {
    nodes: Vec<Node>,
    unique: BTreeMap<(KernelVariable, usize, usize), usize>,
    xors: BTreeMap<(usize, usize), usize>,
    products: BTreeMap<(usize, usize), usize>,
}

impl Arena {
    fn node(&self, id: usize) -> Option<&Node> {
        id.checked_sub(2).map(|i| &self.nodes[i])
    }

    fn make(
        &mut self,
        v: KernelVariable,
        low: usize,
        high: usize,
        work: &mut usize,
    ) -> Option<usize> {
        charge(work, 1)?;
        if high == 0 {
            return Some(low);
        }
        if [low, high]
            .iter()
            .filter_map(|i| self.node(*i))
            .any(|n| n.variable <= v)
        {
            return None;
        }
        let key = (v, low, high);
        if let Some(id) = self.unique.get(&key) {
            return Some(*id);
        }
        if self.nodes.len() >= MAX_NODES {
            return None;
        }
        let id = self.nodes.len() + 2;
        self.nodes.push(Node {
            variable: key.0.clone(),
            low,
            high,
        });
        self.unique.insert(key, id);
        Some(id)
    }

    fn top(&self, a: usize, b: usize) -> KernelVariable {
        self.node(a)
            .into_iter()
            .chain(self.node(b))
            .map(|n| &n.variable)
            .min()
            .unwrap()
            .clone()
    }

    fn split(&self, a: usize, v: &KernelVariable) -> (usize, usize) {
        match self.node(a) {
            Some(n) if &n.variable == v => (n.low, n.high),
            _ => (a, 0),
        }
    }

    fn xor(&mut self, a: usize, b: usize, work: &mut usize, depth: usize) -> Option<usize> {
        charge(work, 1)?;
        if depth > MAX_DEPTH {
            return None;
        }
        if a == b {
            return Some(0);
        }
        if a == 0 {
            return Some(b);
        }
        if b == 0 {
            return Some(a);
        }
        let key = (a.min(b), a.max(b));
        if let Some(id) = self.xors.get(&key) {
            return Some(*id);
        }
        if self.xors.len() >= MAX_MEMO {
            return None;
        }
        let v = self.top(a, b);
        let (a0, a1) = self.split(a, &v);
        let (b0, b1) = self.split(b, &v);
        let low = self.xor(a0, b0, work, depth + 1)?;
        let high = self.xor(a1, b1, work, depth + 1)?;
        let result = self.make(v, low, high, work)?;
        // Recheck: recursive children may have filled the memo.
        if self.xors.len() >= MAX_MEMO {
            return None;
        }
        self.xors.insert(key, result);
        Some(result)
    }

    fn product(&mut self, a: usize, b: usize, work: &mut usize, depth: usize) -> Option<usize> {
        charge(work, 1)?;
        if depth > MAX_DEPTH {
            return None;
        }
        if a == 0 || b == 0 {
            return Some(0);
        }
        // All Boolean polynomials are idempotent, not just literal variables.
        if a == b || b == 1 {
            return Some(a);
        }
        if a == 1 {
            return Some(b);
        }
        let key = (a.min(b), a.max(b));
        if let Some(id) = self.products.get(&key) {
            return Some(*id);
        }
        if self.products.len() >= MAX_MEMO {
            return None;
        }
        let v = self.top(a, b);
        let (a0, a1) = self.split(a, &v);
        let (b0, b1) = self.split(b, &v);
        // COMPLETE cofactors at x=0,1; their XOR is the ANF x coefficient.
        let low = self.product(a0, b0, work, depth + 1)?;
        let one_a = self.xor(a0, a1, work, 0)?;
        let one_b = self.xor(b0, b1, work, 0)?;
        let one = self.product(one_a, one_b, work, depth + 1)?;
        let high = self.xor(low, one, work, 0)?;
        let result = self.make(v, low, high, work)?;
        if self.products.len() >= MAX_MEMO {
            return None;
        }
        self.products.insert(key, result);
        Some(result)
    }

    pub(super) fn import<'a>(
        &mut self,
        terms: impl Iterator<Item = &'a KernelMonomial>,
        omit: Option<&KernelVariable>,
        work: &mut usize,
    ) -> Option<usize> {
        // Build a sparse monomial-prefix trie in total source-cell work, without
        // repeatedly partitioning every absent row down long low-edge chains.
        // References are borrowed from the complete source; no hash identities.
        let mut trie = vec![Prefix::default()];
        for m in terms {
            let n = m.variables().count();
            charge(work, 1 + n)?;
            if n > MAX_DEPTH {
                return None;
            }
            let mut id = 0;
            for v in m.variables().filter(|v| Some(*v) != omit) {
                charge(work, 1)?;
                id = if let Some(child) = trie[id].children.get(v) {
                    *child
                } else {
                    if trie.len() >= SOURCE_CELLS {
                        return None;
                    }
                    let child = trie.len();
                    trie.push(Prefix::default());
                    trie[id].children.insert(v, child);
                    child
                };
            }
            trie[id].constant ^= true;
        }
        self.import_prefix(&trie, 0, work, 0)
    }

    fn import_prefix(
        &mut self,
        trie: &[Prefix<'_>],
        id: usize,
        work: &mut usize,
        depth: usize,
    ) -> Option<usize> {
        charge(work, 1)?;
        if depth > MAX_DEPTH {
            return None;
        }
        // P = constant XOR sum_v v*P_v. Descending siblings build ordered
        // N(v, already_complete_suffix, P_v), without intermediate XOR nodes.
        let mut root = usize::from(trie[id].constant);
        for (v, child) in trie[id].children.iter().rev() {
            let high = self.import_prefix(trie, *child, work, depth + 1)?;
            root = self.make((*v).clone(), root, high, work)?;
        }
        Some(root)
    }

    pub(super) fn export(&self, id: usize, work: &mut usize) -> Option<KernelBooleanPolynomial> {
        // Depth-first shared prefix: pending siblings save only its length.
        // Every full monomial is still copied, bounded and checked distinct.
        let mut stack = vec![(id, 0usize, None)];
        let mut prefix = Vec::<KernelVariable>::new();
        let mut output = KernelBooleanPolynomial::zero();
        let mut stored = 0usize;
        while let Some((id, keep, append)) = stack.pop() {
            charge(work, 1)?;
            if prefix.len() < keep {
                return None;
            }
            prefix.truncate(keep);
            if let Some(v) = append {
                charge(work, 1)?;
                prefix.push(v);
            }
            if prefix.len() > MAX_DEPTH {
                return None;
            }
            if id == 0 {
                continue;
            }
            if id == 1 {
                let size = 1 + prefix.len();
                charge(work, size)?;
                if output.term_count() >= MAX_BOOLEAN_TERMS
                    || stored.checked_add(size)? > SOURCE_CELLS
                {
                    return None;
                }
                stored += size;
                if !output.insert_distinct_monomial(KernelMonomial::from_variables(
                    prefix.iter().cloned(),
                )) {
                    return None;
                }
            } else {
                let n = self.node(id)?;
                // Bound simultaneous frames even along long low-edge chains.
                if stack.len() >= MAX_DEPTH {
                    return None;
                }
                charge(work, 2)?;
                stack.push((n.high, prefix.len(), Some(n.variable.clone())));
                stack.push((n.low, prefix.len(), None));
            }
        }
        // The complete canonical set is already constructed; no second
        // collector pass or cloning of intermediate prefix vectors remains.
        Some(output)
    }

    pub(super) fn image(
        &mut self,
        row: &KernelBooleanPolynomial,
        v: &KernelVariable,
        rhs: usize,
        work: &mut usize,
    ) -> Option<KernelBooleanPolynomial> {
        let h = self.import(row.terms().filter(|m| !m.contains(v)), None, work)?;
        let d = self.import(row.terms().filter(|m| m.contains(v)), Some(v), work)?;
        let p = self.product(d, rhs, work, 0)?;
        let result = self.xor(h, p, work, 0)?;
        self.export(result, work)
    }

    pub(super) fn geometry(&self) -> (usize, usize, usize) {
        (self.nodes.len(), self.xors.len(), self.products.len())
    }
}

#[cfg(test)]
mod tests {
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
}
