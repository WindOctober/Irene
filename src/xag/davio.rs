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

/// Resource refusal returns no transformed graph, never a partial certificate.
pub(crate) fn normalize(
    source: &Network,
    order: Order,
    work: usize,
    nodes: usize,
) -> Option<Network> {
    if !crate::ablation::permit(crate::ablation::Group::ExpressionSimplify) {
        return None;
    }
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
mod tests {
    use super::*;
    #[test]
    fn invalid_graphs_and_exhausted_budgets_return_no_rewrite() {
        let malformed = Network {
            inputs: 0,
            nodes: vec![[2, 0, 0]],
            outputs: vec![0],
        };
        assert!(normalize(&malformed, Order::Forward, 100, 100).is_none());
        let original = Network {
            inputs: 2,
            nodes: vec![[1, 0, 0], [1, 1, 0], [3, 0, 1]],
            outputs: vec![2],
        };
        assert!(normalize(&original, Order::Forward, 100, 4).is_none());
        assert!(normalize(&original, Order::Forward, 3, 100).is_none());
        let n = normalize(&original, Order::Forward, 100, 100).unwrap();
        assert_eq!(evaluate(&n, 0), vec![false]);
        assert_eq!(evaluate(&n, 3), vec![true]);
    }
    fn evaluate(n: &Network, assignment: u64) -> Vec<bool> {
        let mut v = vec![];
        for &[op, a, b] in &n.nodes {
            v.push(match op {
                0 => a != 0,
                1 => assignment & (1 << a) != 0,
                2 => v[a as usize] ^ v[b as usize],
                3 => v[a as usize] & v[b as usize],
                _ => unreachable!(),
            });
        }
        n.outputs.iter().map(|&i| v[i as usize]).collect()
    }
    #[test]
    fn exhaustive_small_graphs_preserve_all_outputs_and_orders() {
        let mut seed = 73u64;
        for _ in 0..100 {
            let mut b = Builder::default();
            b.network.inputs = 5;
            for i in 0..5 {
                b.node(1, i, 0);
            }
            b.node(0, 0, 0);
            b.node(0, 1, 0);
            for _ in 0..60 {
                seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
                let len = b.network.nodes.len() as u64;
                let a = (seed % len) as u32;
                let c = ((seed >> 17) % len) as u32;
                let root = b.node(2 + ((seed >> 41) & 1) as u32, a, c);
                b.network.outputs.push(root);
            }
            for order in [Order::Forward, Order::Reverse] {
                let normalized = normalize(&b.network, order, 1_000_000, 50_000).unwrap();
                for assignment in 0..32 {
                    assert_eq!(
                        evaluate(&b.network, assignment),
                        evaluate(&normalized, assignment)
                    );
                }
            }
            assert!(normalize(&b.network, Order::Forward, 0, 0).is_none());
        }
    }
    #[test]
    fn wide_distributivity_and_idempotence_cancel_without_truth_tables() {
        let mut b = Builder::default();
        b.network.inputs = 64;
        let inputs: Vec<_> = (0..64).map(|i| b.node(1, i, 0)).collect();
        let mut left = b.node(0, 0, 0);
        let mut right = left;
        for i in 1..63 {
            let xy = b.node(2, inputs[i], inputs[i + 1]);
            let xy = b.node(3, inputs[0], xy);
            left = b.node(2, left, xy);
            let x = b.node(3, inputs[0], inputs[i]);
            let y = b.node(3, inputs[0], inputs[i + 1]);
            let xy = b.node(2, x, y);
            right = b.node(2, right, xy);
        }
        let square = b.node(3, left, left);
        let difference = b.node(2, square, right);
        b.network.outputs = vec![difference, inputs[63]];
        for order in [Order::Forward, Order::Reverse] {
            let n = normalize(&b.network, order, 1_000_000, 50_000).unwrap();
            assert_eq!(n.nodes[n.outputs[0] as usize], [0, 0, 0]);
            assert_eq!(n.nodes[n.outputs[1] as usize], [1, 63, 0]);
        }
    }
}
