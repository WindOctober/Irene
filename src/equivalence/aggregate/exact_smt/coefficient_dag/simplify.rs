//! Bounded, exact coefficient rewrites. Never distribute products over sums.
//! Boolean predicates remain XAG functions, not independent numeric variables.
use super::*;
mod context;

impl Dag {
    fn sign(&self, id: Id) -> Option<KernelBooleanPolynomial> {
        let Node::Select(p, a, b) = &self.nodes[id] else {
            return None;
        };
        match (&self.nodes[*a], &self.nodes[*b]) {
            (Node::Constant(a), Node::Constant(b)) if *a == integer(-1) && *b == integer(1) => {
                Some(p.clone())
            }
            _ => None,
        }
    }
    fn sign_node(&mut self, p: KernelBooleanPolynomial) -> Option<Id> {
        if p.is_zero() {
            return Some(1);
        }
        let minus = self.constant(integer(-1))?;
        if p.is_one() {
            return Some(minus);
        }
        self.node(Node::Select(p, minus, 1))
    }
    pub(super) fn simplify_select(
        &mut self,
        p: &KernelBooleanPolynomial,
        a: Id,
        b: Id,
    ) -> Option<Id> {
        // Contextual equality applies only inside the matching branch.
        let aa = match &self.nodes[a] {
            Node::Select(q, x, _) if q == p => *x,
            _ => a,
        };
        let bb = match &self.nodes[b] {
            Node::Select(q, _, y) if q == p => *y,
            _ => b,
        };
        if aa != a || bb != b {
            return self.select(p.clone(), aa, bb);
        }
        let (ra, va) = self.scaled(a);
        let (rb, vb) = self.scaled(b);
        if a == 0 || b == 0 {
            // Pull all weights outside indicators, so indicator AND can fire.
            let (r, v, condition) = if b == 0 {
                (ra, va, p.clone())
            } else {
                (
                    rb,
                    vb,
                    KernelBooleanPolynomial::from_graph(p.as_graph().complement()),
                )
            };
            if v == 1 && r == integer(1) && b == 0 {
                return None;
            }
            let indicator = self.node(Node::Select(condition, 1, 0))?;
            let base = self.multiply(indicator, v)?;
            return self.scale(base, r);
        }
        if va == vb && ra == -&rb {
            // ite(p,-r*A,r*A) = r * (-1)^p * A.
            // Keep the normalized sign as a leaf, not a recursive rewrite.
            if va == 1 && rb == integer(1) {
                return None;
            }
            let sign = self.sign_node(p.clone())?;
            let base = self.multiply(sign, va)?;
            return self.scale(base, rb);
        }
        None
    }
    pub(super) fn simplify_multiply(&mut self, a: Id, b: Id) -> Option<Id> {
        let mut todo = vec![a, b];
        let mut factors = Vec::new();
        let mut weight = integer(1);
        let mut signs = KernelBooleanPolynomial::from(false);
        let mut guard = KernelBooleanPolynomial::from(true);
        let mut visits = 0;
        while let Some(id) = todo.pop() {
            visits += 1;
            if visits > 64 {
                return None;
            }
            match &self.nodes[id] {
                Node::Constant(r) => weight *= r,
                Node::Scale(r, x) => {
                    weight *= r;
                    todo.push(*x);
                }
                Node::Multiply(x, y) => todo.extend([*x, *y]),
                _ => {
                    if let Some(p) = self.sign(id) {
                        signs = signs.xor(&p)
                    } else if let Some(p) = self.indicator(id) {
                        guard = guard.and(&p)
                    } else {
                        factors.push(id)
                    }
                }
            }
        }
        if weight == integer(0) || guard.is_zero() {
            return Some(0);
        }
        if !guard.is_one() {
            if self.context_enabled {
                // [g] F = [g] F|g. Never replace the globally shared F itself.
                for factor in &mut factors {
                    *factor = self.conditioned(*factor, &guard);
                }
                if factors.contains(&0) {
                    return Some(0);
                }
            }
            if signs == guard {
                weight = -weight;
                signs = KernelBooleanPolynomial::from(false);
            } else if signs == KernelBooleanPolynomial::from_graph(guard.as_graph().complement()) {
                signs = KernelBooleanPolynomial::from(false);
            }
            factors.push(self.node(Node::Select(guard, 1, 0))?);
        }
        let sign = self.sign_node(signs)?;
        if sign != 1 {
            factors.push(sign)
        }
        // Specialization can expose constants/scales that were not present
        // during the initial factor collection. Normalize them as well.
        factors = factors
            .into_iter()
            .filter_map(|id| {
                let (r, base) = self.scaled(id);
                weight *= r;
                (base != 1).then_some(base)
            })
            .collect();
        if weight == integer(0) {
            return Some(0);
        }
        factors.sort_unstable();
        let mut result = 1;
        for f in factors {
            result = if result == 1 {
                f
            } else {
                self.node(Node::Multiply(result.min(f), result.max(f)))?
            };
        }
        self.scale(result, weight)
    }
    pub(super) fn simplify_add(&mut self, a: Id, b: Id) -> Option<Id> {
        let (ra, va) = self.scaled(a);
        let (rb, vb) = self.scaled(b);
        if va == vb {
            return self.scale(va, ra + rb);
        }
        // Align only equal predicates; never enumerate all combinations of guards.
        let arms = match (&self.nodes[va], &self.nodes[vb]) {
            (Node::Select(p, x, y), Node::Select(q, z, w)) if p == q => {
                Some((p.clone(), *x, *y, *z, *w))
            }
            (Node::Select(p, x, y), _) if vb == 1 => Some((p.clone(), *x, *y, 1, 1)),
            (_, Node::Select(p, z, w)) if va == 1 => Some((p.clone(), 1, 1, *z, *w)),
            _ => None,
        };
        if let Some((p, x, y, z, w)) = arms {
            let x = self.scale(x, ra.clone())?;
            let y = self.scale(y, ra)?;
            let z = self.scale(z, rb.clone())?;
            let w = self.scale(w, rb)?;
            let yes = self.add(x, z)?;
            let no = self.add(y, w)?;
            return self.select(p, yes, no);
        }
        if let (Node::Multiply(x, y), Node::Multiply(z, w)) = (&self.nodes[va], &self.nodes[vb]) {
            let common = if x == z {
                Some((*x, *y, *w))
            } else if x == w {
                Some((*x, *y, *z))
            } else if y == z {
                Some((*y, *x, *w))
            } else if y == w {
                Some((*y, *x, *z))
            } else {
                None
            };
            if let Some((f, x, y)) = common {
                let x = self.scale(x, ra)?;
                let y = self.scale(y, rb)?;
                let sum = self.add(x, y)?;
                return self.multiply(f, sum);
            }
        }
        // Bounded flattening: do not unfold an exponentially shared Add DAG.
        let mut todo = vec![(integer(1), a), (integer(1), b)];
        let mut terms: BTreeMap<Id, BigRational> = BTreeMap::new();
        let mut visits = 0;
        while let Some((r, id)) = todo.pop() {
            visits += 1;
            if visits > 64 {
                return None;
            }
            match &self.nodes[id] {
                Node::Constant(v) => *terms.entry(1).or_insert_with(|| integer(0)) += r * v,
                Node::Scale(v, x) => todo.push((r * v, *x)),
                Node::Add(x, y) => {
                    todo.push((r.clone(), *x));
                    todo.push((r, *y));
                }
                _ => *terms.entry(id).or_insert_with(|| integer(0)) += r,
            }
        }
        let mut ids = Vec::new();
        for (id, r) in terms {
            if r != integer(0) {
                ids.push(self.scale(id, r)?);
            }
        }
        ids.sort_unstable();
        // Balanced rebuild, retaining child references and never expanding Mul.
        while ids.len() > 1 {
            let mut next = Vec::new();
            for pair in ids.chunks(2) {
                next.push(if pair.len() == 1 {
                    pair[0]
                } else {
                    self.node(Node::Add(pair[0].min(pair[1]), pair[0].max(pair[1])))?
                });
            }
            ids = next;
        }
        Some(ids.first().copied().unwrap_or(0))
    }
    pub(super) fn live_ids(&self, roots: Value) -> BTreeSet<Id> {
        let mut live = BTreeSet::new();
        let mut todo = roots.to_vec();
        while let Some(id) = todo.pop() {
            if !live.insert(id) {
                continue;
            }
            match self.nodes[id] {
                Node::Add(a, b) | Node::Multiply(a, b) | Node::Select(_, a, b) => {
                    todo.extend([a, b])
                }
                Node::Scale(_, a) => todo.push(a),
                Node::Constant(_) => (),
            }
        }
        live
    }
    pub(super) fn simplified(&self, roots: Value) -> Option<(Dag, Value)> {
        self.rewritten(roots, self.context_enabled).or_else(|| {
            self.context_enabled
                .then(|| self.rewritten(roots, false))
                .flatten()
        })
    }
    fn rewritten(&self, roots: Value, context: bool) -> Option<(Dag, Value)> {
        let start = std::time::Instant::now();
        let live = self.live_ids(roots);
        let mut result = Dag::new();
        result.simplify = true;
        result.context_enabled = context;
        let mut ids = BTreeMap::new();
        for id in &live {
            let mapped = match &self.nodes[*id] {
                Node::Constant(r) => result.constant(r.clone())?,
                Node::Add(a, b) => result.add(ids[a], ids[b])?,
                Node::Multiply(a, b) => result.multiply(ids[a], ids[b])?,
                Node::Scale(r, a) => result.scale(ids[a], r.clone())?,
                Node::Select(p, a, b) => result.select(p.clone(), ids[a], ids[b])?,
            };
            ids.insert(*id, mapped);
        }
        let roots = roots.map(|id| ids[&id]);
        if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
            eprintln!(
                "coefficient light post: before={} after={} seconds={:.3} context={} context_work_left={}",
                live.len(),
                result.live_ids(roots).len(),
                start.elapsed().as_secs_f64(),
                context,
                result.context_work
            );
        }
        Some((result, roots))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn guarded_context_cancels_actual_add_shape_without_changing_shared_functions() {
        let mut d = Dag::new();
        d.simplify = false;
        let p: Vec<_> = (0..4)
            .map(|i| KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(i)))
            .collect();
        let abc = p[0].and(&p[1]).and(&p[2]);
        let ac = d
            .select(
                p[1].and(&p[2])
                    .complement()
                    .and(&p[0].and(&p[1]).complement()),
                1,
                0,
            )
            .unwrap();
        let abc = d.select(abc, 1, 0).unwrap();
        let minus = d.scale(abc, integer(-1)).unwrap();
        let a = d.add(ac, minus).unwrap();
        let b = d.select(p[1].and(&p[0].xor(&p[2])), 1, 0).unwrap();
        let b = d.scale(b, integer(-1)).unwrap();
        let bd = d.select(p[1].and(&p[3]), 1, 0).unwrap();
        let not_bd = d.select(p[1].and(&p[3]).complement(), 1, 0).unwrap();
        let not_b = d.select(p[1].complement(), 1, 0).unwrap();
        let x = d.multiply(bd, a).unwrap();
        let x = d.scale(x, integer(-1)).unwrap();
        let y = d.multiply(not_bd, b).unwrap();
        let sum = d.add(x, y).unwrap();
        let n = d.multiply(not_b, sum).unwrap();
        let x = d.multiply(not_bd, a).unwrap();
        let y = d.multiply(bd, b).unwrap();
        let sum = d.add(x, y).unwrap();
        let m = d.multiply(not_b, sum).unwrap();
        let roots = [n, m, a, b];
        let (out, rs) = d.simplified(roots).unwrap();
        assert_eq!(rs[0], 0);
        assert_eq!(out.indicator(rs[1]), Some(p[1].complement()));
        for bits in 0..16 {
            assert_eq!(eval(&d, roots, bits), eval(&out, rs, bits));
        }
        // These real local coefficients are also orthogonal/normalized.
        // Keep the semantic regression even before a rewrite recognizes it.
        let ab = d.multiply(a, b).unwrap();
        let aa = d.multiply(a, a).unwrap();
        let bb = d.multiply(b, b).unwrap();
        let norm = d.add(aa, bb).unwrap();
        let (out, rs) = d.simplified([ab, norm, 0, 0]).unwrap();
        eprintln!(
            "coefficient identities reduced: AB=0 {} A2+B2=1 {}",
            rs[0] == 0,
            rs[1] == 1
        );
        for bits in 0..16 {
            assert_eq!(
                eval(&out, rs, bits),
                vec![integer(0), integer(1), integer(0), integer(0)]
            );
        }
    }
    #[test]
    fn nonlinear_guard_does_not_supply_unproved_literal_assignments() {
        let mut d = Dag::new();
        d.simplify = true;
        let p = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(0));
        let q = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(1));
        let x = d.select(p.clone(), 1, 0).unwrap();
        let not_both = p.and(&q).complement();
        let r = d.conditioned(x, &not_both);
        // ! (p AND q) does NOT imply !p. For p=1,q=0 the value stays 1.
        assert_eq!(eval(&d, [r, 0, 0, 0], 1)[0], integer(1));
        let positive = d.conditioned(x, &p);
        let negative = d.conditioned(x, &p.complement());
        assert_eq!(positive, 1);
        assert_eq!(negative, 0);
        assert_eq!(eval(&d, [x, 0, 0, 0], 1)[0], integer(1));
        d.context_work = 0;
        assert_eq!(d.conditioned(x, &q), x);
        // A mid-traversal refusal must not return a partially specialized root.
        let y = d.select(q.clone(), 1, 0).unwrap();
        let sum = d.node(Node::Add(x, y)).unwrap();
        let both = p.and(&q);
        d.context_work = 1;
        assert_eq!(d.conditioned(sum, &both), sum);
        // A fresh context can still prove both literals of a conjunction.
        d.context_work = 100;
        let g = p.and(&q.complement());
        assert_eq!(d.conditioned(sum, &g), 1);
    }
    fn eval(d: &Dag, roots: Value, bits: usize) -> Vec<BigRational> {
        let mut values: Vec<BigRational> = Vec::new();
        for n in &d.nodes {
            values.push(match n {
                Node::Constant(r) => r.clone(),
                Node::Add(a, b) => &values[*a] + &values[*b],
                Node::Multiply(a, b) => &values[*a] * &values[*b],
                Node::Scale(r, a) => r * &values[*a],
                Node::Select(p, a, b) => {
                    let bit = p
                        .as_graph()
                        .evaluate::<std::convert::Infallible>(|v| {
                            let KernelVariable::QuantumOutputKet(i) =
                                KernelVariable::from_graph_variable(v)
                            else {
                                panic!("unexpected variable")
                            };
                            Ok(bits >> i & 1 != 0)
                        })
                        .unwrap();
                    values[if bit { *a } else { *b }].clone()
                }
            });
        }
        roots.iter().map(|id| values[*id].clone()).collect()
    }
    #[test]
    fn sign_indicator_and_nested_cancellation() {
        let mut d = Dag::new();
        d.simplify = true;
        let p = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(0));
        let q = KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(1));
        let a = d.sign_node(p.clone()).unwrap();
        let b = d.sign_node(q.clone()).unwrap();
        let ab = d.multiply(a, b).unwrap();
        assert_eq!(d.sign(ab), Some(p.xor(&q)));
        assert_eq!(d.multiply(a, a), Some(1));
        let i = d.select(p.clone(), 1, 0).unwrap();
        let product = d.multiply(i, a).unwrap();
        assert_eq!(product, d.scale(i, integer(-1)).unwrap());
        let sum = d.add(a, b).unwrap();
        let minus_a = d.scale(a, integer(-1)).unwrap();
        let residual = d.add(sum, minus_a).unwrap();
        for bits in 0..4 {
            assert_eq!(
                eval(&d, [residual, 0, 0, 0], bits),
                eval(&d, [b, 0, 0, 0], bits)
            );
        }
        let two = d.constant(integer(2)).unwrap();
        let three = d.constant(integer(3)).unwrap();
        let f = d.select(p.clone(), two, three).unwrap();
        let sum = d.add(f, b).unwrap();
        let minus_f = d.scale(f, integer(-1)).unwrap();
        assert_eq!(d.add(sum, minus_f), Some(b));
        let inner = d.select(p.clone(), a, b).unwrap();
        let outer = d.select(p.clone(), inner, 0).unwrap();
        assert_eq!(outer, d.select(p, a, 0).unwrap());
    }
    #[test]
    fn rewrites_preserve_every_assignment_of_generated_dags() {
        for seed in 0..8u64 {
            let mut state = seed + 31;
            let mut d = Dag::new();
            d.simplify = false;
            let ps: Vec<_> = (0..3)
                .map(|i| KernelBooleanPolynomial::variable(KernelVariable::QuantumOutputKet(i)))
                .collect();
            let minus = d.constant(integer(-1)).unwrap();
            let frac = d.constant(ratio(2, 3)).unwrap();
            let mut nodes = vec![0, 1, minus, frac];
            for p in &ps {
                nodes.push(d.select(p.clone(), minus, 1).unwrap());
                nodes.push(d.select(p.clone(), 1, 0).unwrap());
            }
            for step in 0..80 {
                state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
                let a = nodes[(state >> 24) as usize % nodes.len()];
                let b = nodes[(state >> 40) as usize % nodes.len()];
                let id = match step % 4 {
                    0 => d.add(a, b),
                    1 => d.multiply(a, b),
                    2 => d.select(ps[step % 3].clone(), a, b),
                    _ => d.scale(a, ratio((step % 5) as i64 - 2, 3)),
                }
                .unwrap();
                nodes.push(id);
            }
            let roots: Value = nodes[nodes.len() - 4..].try_into().unwrap();
            let (light, result) = d.simplified(roots).unwrap();
            for bits in 0..8 {
                assert_eq!(
                    eval(&d, roots, bits),
                    eval(&light, result, bits),
                    "seed={seed} bits={bits}"
                );
            }
        }
    }
}
