//! Optional positive-Davio normalization, directly from the shared XAG.
//!
//! Reference: https://github.com/lsils/mockturtle/blob/master/include/mockturtle/algorithms/decomposition.hpp
//! Its truth-table input
//! is unsuitable for wide miters. Here (v, low, delta) denotes low XOR v*delta
//! in a shared ordered DAG. No truth table or expanded monomial list is built.
//! XOR/AND apply recursively use the same identity, including v*v=v. These
//! are exact rewrites of arbitrary Boolean functions, not low-degree guesses.
use super::{Builder, Network};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug)]
pub(crate) enum Order {
    Forward,
    Reverse,
}

#[derive(Clone, Copy)]
struct Node {
    variable: u32,
    low: u32,
    delta: u32,
}

struct Dag {
    nodes: Vec<Node>,
    unique: BTreeMap<(u32, u32, u32), u32>,
    cache: BTreeMap<(u32, u32, u32), u32>,
    work: usize,
    limit: usize,
}

impl Dag {
    // Explicit postorder evaluation bounds actual work without a recursion or
    // variable-count limit. Existing normalization callers retain their policy.
    fn apply_iterative(&mut self, op: u32, a: u32, b: u32) -> Option<u32> {
        enum Task {
            Apply(u32, u32, u32),
            Finish(u32, (u32, u32, u32)),
            Product(u32, (u32, u32, u32)),
            JoinProduct(u32, u32, (u32, u32, u32)),
        }
        let mut tasks = vec![Task::Apply(op, a, b)];
        let mut values = Vec::new();
        while let Some(task) = tasks.pop() {
            self.work = self.work.checked_sub(1)?;
            match task {
                Task::Apply(op, mut a, mut b) => {
                    if a > b {
                        std::mem::swap(&mut a, &mut b);
                    }
                    let simple = match op {
                        2 if a == 0 => Some(b),
                        2 if a == b => Some(0),
                        3 if a == 0 => Some(0),
                        3 if a == 1 || a == b => Some(b),
                        2 | 3 => None,
                        _ => return None,
                    };
                    let key = (op, a, b);
                    if let Some(value) = simple.or_else(|| self.cache.get(&key).copied()) {
                        values.push(value);
                        continue;
                    }
                    if self.cache.len() >= self.limit.saturating_mul(4) {
                        return None;
                    }
                    let v = self.nodes[a as usize]
                        .variable
                        .min(self.nodes[b as usize].variable);
                    let (a0, ad) = self.split(a, v);
                    let (b0, bd) = self.split(b, v);
                    if op == 2 {
                        tasks.push(Task::Finish(v, key));
                        tasks.push(Task::Apply(2, ad, bd));
                    } else {
                        tasks.push(Task::Product(v, key));
                        tasks.push(Task::Apply(3, ad, bd));
                        tasks.push(Task::Apply(3, ad, b0));
                        tasks.push(Task::Apply(3, a0, bd));
                    }
                    tasks.push(Task::Apply(op, a0, b0));
                }
                Task::Product(v, key) => {
                    let z = values.pop()?;
                    let y = values.pop()?;
                    let x = values.pop()?;
                    tasks.push(Task::JoinProduct(v, z, key));
                    tasks.push(Task::Apply(2, x, y));
                }
                Task::JoinProduct(v, z, key) => {
                    let xy = values.pop()?;
                    tasks.push(Task::Finish(v, key));
                    tasks.push(Task::Apply(2, xy, z));
                }
                Task::Finish(v, key) => {
                    let delta = values.pop()?;
                    let low = values.pop()?;
                    let result = self.node(v, low, delta)?;
                    if self.cache.len() >= self.limit.saturating_mul(4) {
                        return None;
                    }
                    self.cache.insert(key, result);
                    values.push(result);
                }
            }
        }
        (values.len() == 1).then(|| values[0])
    }

    fn new(work: usize, limit: usize) -> Self {
        Self {
            nodes: vec![
                Node {
                    variable: u32::MAX,
                    low: 0,
                    delta: 0
                };
                2
            ],
            unique: BTreeMap::new(),
            cache: BTreeMap::new(),
            work,
            limit,
        }
    }

    fn node(&mut self, variable: u32, low: u32, delta: u32) -> Option<u32> {
        if delta == 0 {
            return Some(low);
        }
        debug_assert!(self.nodes[low as usize].variable > variable);
        debug_assert!(self.nodes[delta as usize].variable > variable);
        let key = (variable, low, delta);
        if let Some(&id) = self.unique.get(&key) {
            return Some(id);
        }
        if self.nodes.len() >= self.limit {
            return None;
        }
        let id = u32::try_from(self.nodes.len()).ok()?;
        self.nodes.push(Node {
            variable,
            low,
            delta,
        });
        self.unique.insert(key, id);
        Some(id)
    }

    fn split(&self, id: u32, variable: u32) -> (u32, u32) {
        let n = self.nodes[id as usize];
        if n.variable == variable {
            (n.low, n.delta)
        } else {
            (id, 0)
        }
    }

    fn apply(&mut self, op: u32, mut a: u32, mut b: u32) -> Option<u32> {
        self.work = self.work.checked_sub(1)?;
        if a > b {
            std::mem::swap(&mut a, &mut b);
        }
        match op {
            2 if a == 0 => return Some(b),
            2 if a == b => return Some(0),
            3 if a == 0 => return Some(0),
            3 if a == 1 || a == b => return Some(b),
            2 | 3 => (),
            _ => return None,
        }
        let key = (op, a, b);
        if let Some(&value) = self.cache.get(&key) {
            return Some(value);
        }
        if self.cache.len() >= self.limit.saturating_mul(4) {
            return None;
        }
        let variable = self.nodes[a as usize]
            .variable
            .min(self.nodes[b as usize].variable);
        let (a0, ad) = self.split(a, variable);
        let (b0, bd) = self.split(b, variable);
        let low = self.apply(op, a0, b0)?;
        let delta = if op == 2 {
            self.apply(2, ad, bd)?
        } else {
            // (a0+v*ad)(b0+v*bd) = a0*b0 + v*(a0*bd+ad*b0+ad*bd).
            let x = self.apply(3, a0, bd)?;
            let y = self.apply(3, ad, b0)?;
            let z = self.apply(3, ad, bd)?;
            let xy = self.apply(2, x, y)?;
            self.apply(2, xy, z)?
        };
        let result = self.node(variable, low, delta)?;
        self.cache.insert(key, result);
        Some(result)
    }

    fn export(
        &self,
        id: u32,
        variables: &[u32],
        b: &mut Builder,
        memo: &mut BTreeMap<u32, u32>,
    ) -> u32 {
        if let Some(&n) = memo.get(&id) {
            return n;
        }
        let result = if id <= 1 {
            b.node(0, id, 0)
        } else {
            let n = self.nodes[id as usize];
            let variable = variables[n.variable as usize];
            let delta = if n.delta == 1 {
                variable
            } else {
                let d = self.export(n.delta, variables, b, memo);
                b.node(3, variable, d)
            };
            if n.low == 0 {
                delta
            } else {
                let low = self.export(n.low, variables, b, memo);
                b.node(2, low, delta)
            }
        };
        memo.insert(id, result);
        result
    }
}

/// Recognize a single affine output without exporting a general normalized
/// graph. `Some(None)` is a completed nonlinear query; `None` is resource refusal.
/// Bounds graph/apply work; a resource refusal consumes the attempt's allowance.
pub(crate) fn affine(
    source: &Network,
    work: &mut usize,
    nodes: usize,
) -> Option<Option<(bool, Vec<u32>)>> {
    if source.nodes.len() > *work || source.outputs.len() != 1 || !source.validate() {
        *work = 0;
        return None;
    }
    let mut dag = Dag::new(*work, nodes);
    let result = (|| {
        let mut ids = Vec::with_capacity(source.nodes.len());
        for &[op, a, b] in &source.nodes {
            dag.work = dag.work.checked_sub(1)?;
            let id = match op {
                0 => a,
                1 => dag.node(source.inputs - 1 - a, 0, 1)?,
                2 | 3 => dag.apply_iterative(op, ids[a as usize], ids[b as usize])?,
                _ => return None,
            };
            ids.push(id);
        }
        let mut root = ids[source.outputs[0] as usize];
        let mut variables = Vec::new();
        while root > 1 {
            dag.work = dag.work.checked_sub(1)?;
            let n = dag.nodes[root as usize];
            // In a reduced ordered positive-Davio graph an affine function
            // has only constant-one derivatives along its low chain.
            if n.delta != 1 {
                return Some(None);
            }
            variables.push(source.inputs - 1 - n.variable);
            root = n.low;
        }
        Some(Some((root == 1, variables)))
    })();
    *work = if result.is_none() { 0 } else { dag.work };
    result
}

/// Resource refusal returns no transformed graph, never a partial certificate.
pub(crate) fn normalize(
    source: &Network,
    order: Order,
    work: usize,
    nodes: usize,
) -> Option<Network> {
    if !source.validate() || source.inputs > 128 || source.nodes.len() > work {
        return None;
    }
    let mut dag = Dag::new(work, nodes);
    let rank = |v| match order {
        Order::Forward => v,
        Order::Reverse => source.inputs - 1 - v,
    };
    let mut ids = Vec::with_capacity(source.nodes.len());
    for &[op, a, b] in &source.nodes {
        dag.work = dag.work.checked_sub(1)?;
        let id = match op {
            0 => a,
            1 => dag.node(rank(a), 0, 1)?,
            2 | 3 => dag.apply(op, ids[a as usize], ids[b as usize])?,
            _ => return None,
        };
        ids.push(id);
    }
    let mut builder = Builder::default();
    builder.network.inputs = source.inputs;
    let mut variables = vec![0; source.inputs as usize];
    for i in 0..source.inputs {
        variables[rank(i) as usize] = builder.node(1, i, 0);
    }
    let mut memo = BTreeMap::new();
    for &root in &source.outputs {
        let root = dag.export(ids[root as usize], &variables, &mut builder, &mut memo);
        builder.network.outputs.push(root);
    }
    debug_assert!(builder.network.validate());
    Some(builder.network)
}

/// Exact preprocessing at the deterministic-output miter only. Other kernel
/// obligations and the stored HPS representation are deliberately unchanged.
pub(crate) fn preprocess(source: Network) -> Network {
    let mode = std::env::var("IRENE_XAG_DAVIO").unwrap_or_else(|_| "reverse".into());
    let order = match mode.as_str() {
        "forward" => Order::Forward,
        "reverse" => Order::Reverse,
        _ => return source,
    };
    let start = std::time::Instant::now();
    let result = normalize(&source, order, 1_000_000, 50_000);
    let accepted = result
        .as_ref()
        .is_some_and(|n| n.nodes.len() <= source.nodes.len());
    let zero_outputs = result.as_ref().map(|n| {
        n.outputs
            .iter()
            .filter(|&&id| n.nodes[id as usize] == [0, 0, 0])
            .count()
    });
    eprintln!(
        "xag-davio order={order:?} old={} new={:?} accepted={accepted} zero_outputs={zero_outputs:?}/{} elapsed_ms={:.3}",
        source.nodes.len(),
        result.as_ref().map(|n| n.nodes.len()),
        source.outputs.len(),
        start.elapsed().as_secs_f64() * 1000.0
    );
    match result {
        Some(n) if accepted => n,
        _ => source,
    }
}

#[cfg(test)]
mod tests;
