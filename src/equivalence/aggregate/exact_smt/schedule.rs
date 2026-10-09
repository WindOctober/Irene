//! Bounded structure-driven Davio preparation for local coherent contraction.
use super::*;
use crate::symbolic::BooleanPolynomial;

fn cost(t: &WorkingTerm) -> (usize, usize, usize) {
    (t.paths.len(), t.constraints.len(), t.phase.term_count())
}

/// Keep every accepted improvement, including when the next probe refuses.
/// Strict descent in a tuple of natural numbers replaces wall-clock and round
/// cutoffs. Individual graph transformations retain their allocation budgets.
fn refine(
    mut current: WorkingTerm,
    mut step: impl FnMut(&WorkingTerm) -> Option<Reduction>,
) -> Reduction {
    loop {
        match step(&current) {
            Some(Reduction::Sum(next)) if cost(&next) < cost(&current) => {
                if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
                    eprintln!("scheduled davio {:?} -> {:?}", cost(&current), cost(&next));
                }
                current = *next;
            }
            Some(done @ (Reduction::Zero | Reduction::Exact(_))) => return done,
            _ => return Reduction::Sum(Box::new(current)),
        }
    }
}

pub(super) fn central_order(t: &WorkingTerm) -> Vec<KernelVariable> {
    let mut adjacent: BTreeMap<_, BTreeSet<_>> = t
        .paths
        .iter()
        .cloned()
        .map(|v| (v, BTreeSet::new()))
        .collect();
    // Use the original small factors, not the combined sign root (which can
    // span the entire circuit). Large scopes remain intact semantically; they
    // simply provide no useful local-order hint.
    for p in t
        .constraints
        .iter()
        .cloned()
        .chain(t.phase.selectors().map(|(p, _)| p))
    {
        let scope: Vec<_> = p.variables().intersection(&t.paths).cloned().collect();
        if scope.len() <= 8 {
            for a in &scope {
                adjacent
                    .get_mut(a)
                    .unwrap()
                    .extend(scope.iter().filter(|b| *b != a).cloned());
            }
        }
    }
    // Shared accumulator coordinates create hubs. Keep these separators late
    // in the Davio order; find a center in the low-degree backbone instead.
    let mut degrees: Vec<_> = adjacent.values().map(BTreeSet::len).collect();
    degrees.sort_unstable();
    let threshold = degrees.get(degrees.len() / 2).copied().unwrap_or(0) + 1;
    let backbone: BTreeSet<_> = adjacent
        .iter()
        .filter(|(_, n)| n.len() <= threshold)
        .map(|(v, _)| v.clone())
        .collect();
    let distances = |start: &KernelVariable| {
        let mut d = BTreeMap::from([(start.clone(), 0usize)]);
        let mut queue = std::collections::VecDeque::from([start.clone()]);
        while let Some(v) = queue.pop_front() {
            for w in &adjacent[&v] {
                if !backbone.is_empty() && !backbone.contains(w) {
                    continue;
                }
                if !d.contains_key(w) {
                    d.insert(w.clone(), d[&v] + 1);
                    queue.push_back(w.clone());
                }
            }
        }
        d
    };
    let Some(center) = backbone.iter().min_by_key(|v| {
        let d = distances(v);
        (t.paths.len() - d.len(), d.values().sum::<usize>())
    }) else {
        return Vec::new();
    };
    let d = distances(center);
    let mut order: Vec<_> = t.paths.iter().cloned().collect();
    order.sort_by_key(|v| (d.get(v).copied().unwrap_or(usize::MAX), adjacent[v].len()));
    if std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some() {
        eprintln!(
            "scheduled connectivity center={center:?} paths={}",
            order.len()
        );
    }
    order
}

pub(super) fn normalize(t: &WorkingTerm, preferred: &[KernelVariable]) -> Option<WorkingTerm> {
    let mut roots = t.constraints.clone();
    let mut coefficients = Vec::new();
    let mut sign = KernelBooleanPolynomial::zero();
    for (p, c) in t.phase.selectors() {
        if c.as_rational() == Some(ratio(1, 2)) {
            sign = sign.xor(&p);
        } else {
            roots.push(p);
            coefficients.push(c);
        }
    }
    roots.push(sign);
    coefficients.push(PhaseCoefficient::rational(ratio(1, 2)));
    let graphs: Vec<_> = roots
        .iter()
        .map(KernelBooleanPolynomial::as_graph)
        .collect();
    let (mut network, vars) = BooleanPolynomial::graph_network(&graphs);
    if network.nodes.len() > 50_000 {
        return None;
    }
    let mut order: Vec<_> = (0..vars.len()).rev().collect();
    order.sort_by_key(|&i| {
        preferred
            .iter()
            .position(|v| *v == KernelVariable::from_graph_variable(&vars[i]))
            .unwrap_or(usize::MAX)
    });
    let mut ranks = vec![0; vars.len()];
    for (rank, &i) in order.iter().enumerate() {
        ranks[i] = rank as u32;
    }
    for node in &mut network.nodes {
        if node[0] == 1 {
            node[1] = ranks[node[1] as usize];
        }
    }
    let network = crate::xag::davio::normalize(
        &network,
        crate::xag::davio::Order::Forward,
        1_000_000,
        50_000,
    )?;
    let mut values: Vec<BooleanPolynomial> = Vec::new();
    for &[op, a, b] in &network.nodes {
        values.push(match op {
            0 => BooleanPolynomial::from(a != 0),
            1 => BooleanPolynomial::variable(vars[order[a as usize]].clone()),
            2 => values[a as usize].xor(&values[b as usize]),
            3 => values[a as usize].and(&values[b as usize]),
            _ => return None,
        });
    }
    let roots: Vec<_> = network
        .outputs
        .iter()
        .map(|&r| KernelBooleanPolynomial::from_graph(values[r as usize].clone()))
        .collect();
    let mut result = t.clone();
    result.constraints = roots[..t.constraints.len()].to_vec();
    result.phase = KernelPhasePolynomial::default();
    for (p, c) in roots[t.constraints.len()..].iter().zip(coefficients) {
        result.phase.add_boolean(p, c);
    }
    Some(result)
}

impl Encoder {
    pub(super) fn scheduled_sum(&mut self, t: &WorkingTerm) -> Option<Polynomial> {
        if t.paths.is_empty() {
            return self.term(t);
        }
        let original: Vec<_> = t.paths.iter().cloned().collect();
        let mut orders = vec![
            central_order(t),
            original.iter().rev().cloned().collect(),
            original.clone(),
        ];
        // Path creation distance retains the spacing of symbolic execution
        // boundaries, unlike the position in a set of surviving paths. The
        // center is obtained from connectivity, never a supplied path number.
        let creation = |v: &KernelVariable| match v {
            KernelVariable::PathKet { path, .. } | KernelVariable::PathBra { path, .. } => *path,
            _ => 0,
        };
        if let Some(center) = orders[0].first() {
            let center = creation(center);
            let mut order = original.clone();
            order.sort_by_key(|v| creation(v).abs_diff(center));
            orders.push(order.clone());
            if order.len() > 16 {
                // A small late separator can control which guard pivots become
                // visible. Probe its permutations instead of freezing a tie
                // break; four variables cap this search at 24 candidates.
                fn permutations(
                    values: &mut [KernelVariable],
                    i: usize,
                    out: &mut Vec<Vec<KernelVariable>>,
                ) {
                    if i == values.len() {
                        out.push(values.to_vec());
                        return;
                    }
                    for j in i..values.len() {
                        values.swap(i, j);
                        permutations(values, i + 1, out);
                        values.swap(i, j);
                    }
                }
                let split = order.len() - 4;
                let mut suffixes = Vec::new();
                permutations(&mut order[split..], 0, &mut suffixes);
                for suffix in suffixes {
                    orders.push(order[..split].iter().cloned().chain(suffix).collect());
                }
            }
        }
        // A bounded set of breadth-first positions along the existing path
        // order complements graph centrality when large shared factors obscure
        // connectivity. Select by ACTUAL post-reduction cost, not the seed.
        for fraction in [1, 2, 3] {
            let center = (original.len() - 1) * fraction / 4;
            let mut indices: Vec<_> = (0..original.len()).collect();
            indices.sort_by_key(|i| i.abs_diff(center));
            orders.push(indices.into_iter().map(|i| original[i].clone()).collect());
        }
        let mut candidates = vec![(t.clone(), Vec::new())];
        let mut seen_orders = BTreeSet::new();
        for order in orders {
            if !seen_orders.insert(order.clone()) {
                continue;
            }
            let current = match refine(t.clone(), |current| {
                normalize(current, &order).map(reduce_working_term)
            }) {
                Reduction::Zero => return Some(Vec::new()),
                Reduction::Exact(t) => {
                    return self.term(&WorkingTerm {
                        paths: BTreeSet::new(),
                        constraints: t.constraints,
                        coefficient: t.coefficient,
                        phase: t.phase,
                    });
                }
                Reduction::Sum(t) => *t,
                Reduction::Residual => unreachable!("refine retains the last candidate"),
            };
            if !candidates.iter().any(|(old, _)| {
                old.paths == current.paths
                    && old.constraints == current.constraints
                    && old.phase == current.phase
                    && old.coefficient == current.coefficient
            }) {
                candidates.push((current, order));
            }
        }
        candidates.sort_by_key(|(t, _)| cost(t));
        for (candidate, order) in candidates {
            for hint in [None, Some(order.as_slice())] {
                let mut trial = self.clone();
                let budget =
                    self.probe_work_budget(crate::equivalence::tuning::limits().probe_work);
                trial.work = budget;
                let result = match hint {
                    None => trial.contract(&candidate),
                    Some(order) => trial.contract_ordered(&candidate, Some(order)),
                };
                self.charge(budget - trial.work)?;
                if let Some(result) = result {
                    // A complete exact answer must not be lost to a later
                    // optional probe. No three-candidate admission cutoff.
                    trial.work = self.work;
                    *self = trial;
                    return Some(result);
                }
            }
        }
        None
    }
}

#[cfg(test)]
#[path = "../../../../tests/unit/equivalence/aggregate/exact_smt/schedule/tests.rs"]
mod tests;
