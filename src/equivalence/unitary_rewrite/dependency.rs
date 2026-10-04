//! Live wire dependencies with shrinking, rechecked pair/triple rewrites.
//! Approximate removals have an explicit global diamond-distance ledger.
use super::*;
use petgraph::{Direction, graph::DiGraph};
use std::ops::Bound::{Excluded, Unbounded};

mod interval;

#[derive(Clone, Debug, Default)]
pub struct Statistics {
    pub before: usize,
    pub after: usize,
    pub removed_h: usize,
    pub exact_rewrites: usize,
    pub exact_identity_gates: usize,
    pub approximate_pairs: usize,
    pub approximate_single_gates: usize,
    pub approximate_blocks: usize,
    pub work: usize,
    pub elapsed_us: u128,
    pub eligible_angles: usize,
    pub diamond_error: BigRational,
}

fn costly(op: &Op, order: u64) -> bool {
    op.angle.as_ref().is_some_and(|a| match a.as_rational() {
        None => true,
        Some(r) => r
            .denom()
            .to_string()
            .parse::<u64>()
            .map_or(true, |d| !d.is_power_of_two() || d > order),
    })
}

/// Only cross gates with a checked exact commutation rule. All selected gates
/// have the same family and ordered wires, hence the same one-parameter
/// generator. Unsupported arithmetic or insufficient budget leaves them intact.
fn angle_block(
    i: usize,
    slots: &[Option<Op>],
    wires: &BTreeMap<Qubit, BTreeSet<usize>>,
    budget: &mut usize,
) -> Option<Vec<usize>> {
    let current = slots[i].as_ref()?;
    current.angle.as_ref()?;
    let mut previous = BTreeSet::new();
    for q in &current.wires {
        for &j in wires[q].range(..i).rev() {
            if !spend(budget) {
                return None;
            }
            previous.insert(j);
            if !commutes(current, slots[j].as_ref()?) {
                break;
            }
        }
    }
    let mut selected = vec![i];
    for j in previous.into_iter().rev() {
        if !spend(budget) {
            return None;
        }
        let other = slots[j].as_ref()?;
        if !commutes(current, other) {
            break;
        }
        if current.family() == other.family() && current.wires == other.wires {
            selected.push(j);
        }
    }
    (selected.len() >= 3).then_some(selected)
}

fn replace_selected(
    selected: &[usize],
    replacement: Option<(usize, Op)>,
    slots: &mut [Option<Op>],
    wires: &mut BTreeMap<Qubit, BTreeSet<usize>>,
    pending: &mut BTreeSet<usize>,
) {
    let mut touched = BTreeSet::new();
    for k in selected {
        if let Some(old) = slots[*k].take() {
            for q in old.wires {
                wires.get_mut(&q).unwrap().remove(k);
                touched.insert(q);
            }
        }
    }
    if let Some((kept, op)) = replacement {
        for q in &op.wires {
            wires.get_mut(q).unwrap().insert(kept);
        }
        slots[kept] = Some(op);
        pending.insert(kept);
    }
    for q in touched {
        for k in selected {
            if let Some(&p) = wires[&q].range(..*k).next_back() {
                pending.insert(p);
            }
            if let Some(&n) = wires[&q].range((Excluded(*k), Unbounded)).next() {
                pending.insert(n);
            }
        }
    }
}

/// Wire lists are the live adjacency representation of the circuit DAG.
/// Deletion immediately reconnects predecessor and successor on every wire.
pub(in crate::equivalence) fn reduce(
    source: &Program,
    order: u64,
    tolerance: Option<BigRational>,
    schedule: bool,
) -> Option<(Program, Statistics)> {
    unitary::validate(source).ok()?;
    numeric_domains(source).ok()?;
    if source
        .body
        .statements
        .iter()
        .any(|s| !matches!(s.kind, StatementKind::Apply { .. }))
    {
        return None;
    }
    let started = std::time::Instant::now();
    let before = source.body.statements.len();
    let mut slots: Vec<_> = source
        .body
        .statements
        .iter()
        .cloned()
        .map(Op::from)
        // A lone identity must not become a false noncommuting barrier.
        // This exact shrinking pass is independent of search/tolerance budgets.
        .filter(|op| !op.is_identity())
        .map(Some)
        .collect();
    let mut wires: BTreeMap<Qubit, BTreeSet<usize>> = BTreeMap::new();
    for (i, op) in slots.iter().enumerate() {
        for q in &op.as_ref()?.wires {
            wires.entry(q.clone()).or_default().insert(i);
        }
    }
    let eligible = slots.iter().flatten().filter(|o| costly(o, order)).count();
    let limit = tolerance.unwrap_or_else(|| rational(0, 1));
    // Sum over ALL removals, including disjoint wires. A longest-chain budget
    // alone does not bound the error of the tensor product of those wires.
    let per_pair = &limit / BigRational::from_integer(eligible.max(1).into());
    let mut stats = Statistics {
        before,
        exact_rewrites: before - slots.len(),
        exact_identity_gates: before - slots.len(),
        eligible_angles: eligible,
        diamond_error: rational(0, 1),
        ..Default::default()
    };
    let h_before = slots.iter().flatten().filter(|o| o.gate == Gate::H).count();
    let mut ids = AstIdGenerator::starting_at(source.ast_id_bound());
    let mut pending: BTreeSet<_> = (0..slots.len()).collect();
    let mut budget = MAX_WORK;
    loop {
        while let Some(i) = pending.pop_first() {
            if !spend(&mut budget) {
                break;
            }
            let Some(current) = slots[i].clone() else {
                continue;
            };
            if eligible > 0
                && limit > rational(0, 1)
                && let Some(selected) = angle_block(i, &slots, &wires, &mut budget)
            {
                let ops: Vec<_> = selected
                    .iter()
                    .map(|k| slots[*k].as_ref().unwrap())
                    .collect();
                let eligible_count = ops.iter().filter(|op| costly(op, order)).count();
                // Allocate the block the shares of its expensive source angles;
                // the global ledger is still authoritative across all wires.
                let allowance = &per_pair * BigRational::from_integer(eligible_count.into());
                if eligible_count > 0
                    && let Some(error) = interval::block_error(&ops)
                    && error <= allowance
                    && &stats.diamond_error + &error <= limit
                {
                    replace_selected(&selected, None, &mut slots, &mut wires, &mut pending);
                    if error > rational(0, 1) {
                        stats.approximate_blocks += 1;
                        stats.diamond_error += error;
                    } else {
                        stats.exact_rewrites += 1;
                    }
                    continue;
                }
            }
            let mut previous = BTreeSet::new();
            for q in &current.wires {
                let mut barriers = 0;
                for &j in wires[q].range(..i).rev() {
                    if !spend(&mut budget) {
                        break;
                    }
                    previous.insert(j);
                    if !commutes(&current, slots[j].as_ref()?) {
                        barriers += 1;
                        if barriers == 2 {
                            break;
                        }
                    }
                }
            }
            let mut middle = None;
            for j in previous.into_iter().rev() {
                if !spend(&mut budget) {
                    break;
                }
                let a = slots[j].as_ref()?;
                let b = slots[i].as_ref()?;
                let crossing = commutes(a, b);
                let selected = if let Some(k) = middle {
                    vec![j, k, i]
                } else {
                    vec![j, i]
                };
                let mut replacement = None;
                let mut error = rational(0, 1);
                let same = a.wires == b.wires;
                if same && selected.len() == 2 {
                    replacement = fuse(a, b, &mut ids).map(|r| (j, r));
                    if !matches!(replacement, Some((_, None)))
                        && per_pair > rational(0, 1)
                        && (costly(a, order) || costly(b, order))
                        && let Some(e) = interval::pair_error(a, b)
                        && e <= per_pair
                        && &stats.diamond_error + &e <= limit
                    {
                        replacement = Some((j, None));
                        error = e;
                    }
                } else if same && let Some(k) = middle {
                    replacement =
                        conjugate(a, slots[k].as_ref()?, b, &mut ids).map(|r| (k, Some(r)));
                }
                if let Some((kept, op)) = replacement {
                    let mut crossed = BTreeSet::new();
                    for q in &a.wires {
                        crossed.extend(wires[q].range((Excluded(j), Excluded(i))).copied());
                    }
                    let legal = crossed
                        .into_iter()
                        .filter(|k| !selected.contains(k))
                        .all(|k| {
                            spend(&mut budget)
                                && commutes(a, slots[k].as_ref().unwrap())
                                && commutes(b, slots[k].as_ref().unwrap())
                        });
                    if legal {
                        replace_selected(
                            &selected,
                            op.map(|op| (kept, op)),
                            &mut slots,
                            &mut wires,
                            &mut pending,
                        );
                        if error > rational(0, 1) {
                            stats.approximate_pairs += 1;
                            stats.diamond_error += error;
                        } else {
                            stats.exact_rewrites += 1;
                        }
                        break;
                    }
                }
                if !crossing {
                    if middle.is_some() || current.gate != Gate::H {
                        break;
                    }
                    middle = Some(j);
                }
            }
        }
        // Only try tolerant singletons after the pair/block queue reaches a fixed
        // point. Otherwise a tiny gate may be approximated before its exact inverse
        // gets visited, needlessly weakening an exact proof to a tolerance proof.
        let mut singleton = None;
        if per_pair > rational(0, 1) {
            for (i, op) in slots.iter().enumerate() {
                if !spend(&mut budget) {
                    break;
                }
                if let Some(op) = op
                    && costly(op, order)
                    && let Some(error) = interval::block_error(&[op])
                    && error <= per_pair
                    && &stats.diamond_error + &error <= limit
                {
                    singleton = Some((i, error));
                    break;
                }
            }
        }
        let Some((i, error)) = singleton else {
            break;
        };
        // This also preserves cancellations formerly paired with a zero gate.
        replace_selected(&[i], None, &mut slots, &mut wires, &mut pending);
        if error > rational(0, 1) {
            stats.approximate_single_gates += 1;
            stats.diamond_error += error;
        } else {
            stats.exact_rewrites += 1;
        }
    }
    let live: Vec<_> = slots.into_iter().flatten().collect();
    stats.after = live.len();
    stats.removed_h = h_before - live.iter().filter(|o| o.gate == Gate::H).count();
    stats.work = MAX_WORK - budget;
    let statements = if schedule {
        topological(live)?
    } else {
        live.into_iter().map(|o| o.statement).collect()
    };
    let mut result = source.clone();
    result.body.statements = statements;
    stats.elapsed_us = started.elapsed().as_micros();
    Some((result, stats))
}

fn topological(ops: Vec<Op>) -> Option<Vec<Statement>> {
    let mut graph = DiGraph::<usize, ()>::new();
    let nodes: Vec<_> = (0..ops.len()).map(|i| graph.add_node(i)).collect();
    let mut last = BTreeMap::new();
    for (i, op) in ops.iter().enumerate() {
        let mut parents = BTreeSet::new();
        for q in &op.wires {
            if let Some(p) = last.insert(q.clone(), i) {
                parents.insert(p);
            }
        }
        for p in parents {
            graph.add_edge(nodes[p], nodes[i], ());
        }
    }
    let cost = |i: usize| {
        u8::from(matches!(
            ops[i].gate,
            Gate::H | Gate::Rx | Gate::Ry | Gate::Crx | Gate::Cry
        ))
    };
    let mut incoming: Vec<_> = nodes
        .iter()
        .map(|n| graph.neighbors_directed(*n, Direction::Incoming).count())
        .collect();
    let mut ready: BTreeSet<_> = (0..ops.len())
        .filter(|i| incoming[*i] == 0)
        .map(|i| (cost(i), i))
        .collect();
    let mut out = Vec::new();
    while let Some((_, i)) = ready.pop_first() {
        out.push(ops[i].statement.clone());
        for n in graph.neighbors_directed(nodes[i], Direction::Outgoing) {
            let j = graph[n];
            incoming[j] -= 1;
            if incoming[j] == 0 {
                ready.insert((cost(j), j));
            }
        }
    }
    (out.len() == ops.len()).then_some(out)
}
