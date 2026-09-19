use super::*;
use crate::xag::{Builder, Network};

impl BooleanPolynomial {
    /// Exact local semantic normalization in a temporary ordered Davio DAG.
    /// The stored representation remains XAG. Refusal never yields a partial
    /// function or a claim that a variable is independent.
    pub(crate) fn normalize_local(roots: &[Self]) -> Option<Vec<Self>> {
        let (network, variables) = Self::graph_network(roots);
        let normalized = crate::xag::davio::normalize(
            &network,
            crate::xag::davio::Order::Reverse,
            200_000,
            20_000,
        )?;
        let mut values: Vec<Self> = Vec::with_capacity(normalized.nodes.len());
        for [op, a, b] in normalized.nodes {
            let value = match op {
                0 => {
                    if a == 0 {
                        Self::zero()
                    } else {
                        Self::one()
                    }
                }
                1 => Self::variable(variables.get(a as usize)?.clone()),
                2 => values.get(a as usize)?.xor(values.get(b as usize)?),
                3 => values.get(a as usize)?.and(values.get(b as usize)?),
                _ => return None,
            };
            values.push(value);
        }
        normalized
            .outputs
            .iter()
            .map(|i| values.get(*i as usize).cloned())
            .collect()
    }

    /// All roots share one network and one exact variable map.
    pub(crate) fn graph_network(roots: &[Self]) -> (Network, Vec<Variable>) {
        let vars: Vec<_> = roots
            .iter()
            .flat_map(Self::variables)
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let positions: std::collections::BTreeMap<_, _> = vars
            .iter()
            .cloned()
            .enumerate()
            .map(|(i, v)| (v, i as u32))
            .collect();
        let mut b = Builder::default();
        b.network.inputs = vars.len().try_into().expect("too many graph inputs");
        // Use one stable input map for all roots.
        for i in 0..b.network.inputs {
            b.node(1, i, 0);
        }
        let mut memo = HashMap::new();
        for root in roots {
            let mut pending = vec![(root, false)];
            while let Some((p, ready)) = pending.pop() {
                if memo.contains_key(&p.key()) {
                    continue;
                }
                if !ready {
                    pending.push((p, true));
                    if let Expression::Xor(xs) | Expression::And(xs) = p.expression() {
                        pending.extend(xs.iter().rev().map(|x| (x, false)));
                    }
                    continue;
                }
                let id = match p.expression() {
                    Expression::Constant(v) => b.node(0, u32::from(*v), 0),
                    Expression::Variable(v) => b.node(1, positions[v], 0),
                    Expression::Xor(xs) | Expression::And(xs) => {
                        let xor = matches!(p.expression(), Expression::Xor(_));
                        let mut ids = xs.iter().map(|x| memo[&x.key()]);
                        let first = ids.next().unwrap();
                        ids.fold(first, |a, c| b.node(if xor { 2 } else { 3 }, a, c))
                    }
                };
                memo.insert(p.key(), id);
            }
            b.network.outputs.push(memo[&root.key()]);
        }
        (b.network, vars)
    }
}
