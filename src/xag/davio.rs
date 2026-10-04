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

#[cfg(test)]
mod tests;
