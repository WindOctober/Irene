//! Exact contextual specialization, not assignment enumeration or path removal.
//! The result equals F only under g; callers MUST retain the outer [g].
use super::*;

impl Dag {
    // Only specialize small coefficient cones. A large shared arithmetic tail
    // is not a useful target for repeated cloning under unrelated guards.
    fn local_support(&mut self, root: Id) -> Option<BTreeSet<KernelVariable>> {
        let mut pending = vec![(root, false)];
        let mut visits = 0;
        while let Some((id, exit)) = pending.pop() {
            if self.context_support.contains_key(&id) {
                continue;
            }
            let children = match &self.nodes[id] {
                Node::Add(a, b) | Node::Multiply(a, b) | Node::Select(_, a, b) => vec![*a, *b],
                Node::Scale(_, a) => vec![*a],
                Node::Constant(_) => vec![],
            };
            if !exit {
                visits += 1;
                if visits > 128 {
                    self.context_support.insert(root, None);
                    return None;
                }
                pending.push((id, true));
                pending.extend(children.into_iter().map(|id| (id, false)));
                continue;
            }
            let support = (|| {
                let mut vars = match &self.nodes[id] {
                    Node::Select(p, _, _) => p.variables(),
                    _ => BTreeSet::new(),
                };
                for c in children {
                    vars.extend(self.context_support[&c].as_ref()?.iter().cloned());
                    if vars.len() > 6 {
                        return None;
                    }
                }
                (vars.len() <= 6).then_some(vars)
            })();
            self.context_support.insert(id, support);
        }
        self.context_support.get(&root).cloned().flatten()
    }

    pub(super) fn conditioned(&mut self, root: Id, guard: &KernelBooleanPolynomial) -> Id {
        let key = (root, guard.clone());
        if let Some(id) = self.context_cache.get(&key) {
            return *id;
        }
        let vars = guard.variables();
        if vars.len() > 8 || self.context_work == 0 {
            return root;
        }
        let Some(support) = self.local_support(root) else {
            return root;
        };
        if support.is_disjoint(&vars) {
            return root;
        }
        // Structural cofactor-zero is a sufficient implication proof. Nonlinear
        // predicates remain exact XAGs; an inconclusive check supplies no fact.
        let assignments: Vec<_> = vars
            .into_iter()
            .filter_map(|v| {
                if guard
                    .substitute(&v, &KernelBooleanPolynomial::from(false))
                    .is_zero()
                {
                    Some((v, true))
                } else if guard
                    .substitute(&v, &KernelBooleanPolynomial::from(true))
                    .is_zero()
                {
                    Some((v, false))
                } else {
                    None
                }
            })
            .collect();
        let inverse = guard.complement();
        let mut mapped = BTreeMap::new();
        let mut pending = vec![(root, false)];
        let enabled = self.context_enabled;
        self.context_enabled = false;
        let mut visits = 0;
        let attempt = (|| -> Option<Id> {
            while let Some((id, exit)) = pending.pop() {
                if mapped.contains_key(&id) {
                    continue;
                }
                if let Some(v) = self.context_cache.get(&(id, guard.clone())) {
                    mapped.insert(id, *v);
                    continue;
                }
                if !exit {
                    visits += 1;
                    if visits > 128 || self.context_work == 0 {
                        return None;
                    }
                    self.context_work -= 1;
                    pending.push((id, true));
                    match &self.nodes[id] {
                        Node::Add(a, b) | Node::Multiply(a, b) | Node::Select(_, a, b) => {
                            pending.extend([(*a, false), (*b, false)])
                        }
                        Node::Scale(_, a) => pending.push((*a, false)),
                        Node::Constant(_) => (),
                    }
                    continue;
                }
                let before = self.nodes.len();
                let value = match self.nodes[id].clone() {
                    Node::Constant(_) => id,
                    Node::Add(a, b) => self.add(mapped[&a], mapped[&b])?,
                    Node::Multiply(a, b) => self.multiply(mapped[&a], mapped[&b])?,
                    Node::Scale(r, a) => self.scale(mapped[&a], r)?,
                    Node::Select(mut p, a, b) => {
                        p = if p == *guard {
                            KernelBooleanPolynomial::from(true)
                        } else if p == inverse {
                            KernelBooleanPolynomial::from(false)
                        } else {
                            for (v, value) in &assignments {
                                p = p.substitute(v, &KernelBooleanPolynomial::from(*value));
                            }
                            p
                        };
                        self.select(p, mapped[&a], mapped[&b])?
                    }
                };
                // Account for actual new nodes too, not just source visits.
                self.context_work = self.context_work.saturating_sub(self.nodes.len() - before);
                mapped.insert(id, value);
                self.context_cache.insert((id, guard.clone()), value);
            }
            mapped.get(&root).copied()
        })();
        self.context_enabled = enabled;
        // A failed attempt changes no root. Completed contextual cache entries
        // remain valid only with their own guard; never cache a global equality.
        let result = attempt.unwrap_or(root);
        self.context_cache.insert(key, result);
        result
    }
}
