//! Experimental portmatching candidate discovery; all proposals are checked
//! against the current IR by the same rule checker as the native schedulers.
use super::*;
use portgraph::{LinkMut, NodeIndex, PortGraph, PortMut, PortOffset, UnmanagedDenseMap};
use portmatching::{ManyMatcher, PortMatcher, WeightedGraphRef, WeightedPattern};

type Matcher = ManyMatcher<NodeIndex, u8, (PortOffset, PortOffset)>;

fn matcher() -> &'static Matcher {
    static MATCHER: std::sync::OnceLock<Matcher> = std::sync::OnceLock::new();
    MATCHER.get_or_init(|| {
        let mut patterns = Vec::new();
        for &gate in rules::PAIRS {
            let n = crate::ir::gate_shape(gate).0;
            let mut graph = PortGraph::new();
            let a = graph.add_node(n, n);
            let b = graph.add_node(n, n);
            for port in 0..n {
                graph.link_nodes(a, port, b, port).unwrap();
            }
            let mut weights = UnmanagedDenseMap::new();
            weights[a] = gate as u8;
            weights[b] = gate as u8;
            patterns.push(WeightedPattern::from_weighted_portgraph(&graph, weights));
        }
        for &(first, gate, last) in rules::TRIPLES {
            let n = crate::ir::gate_shape(gate).0;
            let mut graph = PortGraph::new();
            let a = graph.add_node(1, 1);
            let b = graph.add_node(n, n);
            let c = graph.add_node(1, 1);
            graph.link_nodes(a, 0, b, n - 1).unwrap();
            graph.link_nodes(b, n - 1, c, 0).unwrap();
            let mut weights = UnmanagedDenseMap::new();
            weights[a] = first as u8;
            weights[b] = gate as u8;
            weights[c] = last as u8;
            patterns.push(WeightedPattern::from_weighted_portgraph(&graph, weights));
        }
        ManyMatcher::from_patterns(patterns)
    })
}

pub(super) fn candidates(slots: &[Option<Op>]) -> Vec<Vec<usize>> {
    let mut graph = PortGraph::new();
    let mut weights = UnmanagedDenseMap::new();
    let mut positions = BTreeMap::new();
    let mut last = BTreeMap::new();
    for (i, op) in slots.iter().enumerate() {
        let Some(op) = op else {
            continue;
        };
        let n = graph.add_node(op.wires.len(), op.wires.len());
        weights[n] = op.family() as u8;
        positions.insert(n, i);
        for (port, q) in op.wires.iter().enumerate() {
            if let Some((p, offset)) = last.insert(q.clone(), (n, port)) {
                graph.link_nodes(p, offset, n, port).unwrap();
            }
        }
    }
    let weighted = WeightedGraphRef::new(&graph, &weights);
    let matcher = matcher();
    let mut candidates = Vec::new();
    for found in matcher.find_matches(weighted) {
        type Weighted<'a> = WeightedGraphRef<&'a PortGraph, &'a UnmanagedDenseMap<NodeIndex, u8>>;
        let Some(pattern) =
            <Matcher as PortMatcher<Weighted<'_>, NodeIndex, NodeIndex>>::get_pattern(
                matcher,
                found.pattern,
            )
        else {
            continue;
        };
        let found = portmatching::matcher::PatternMatch::new(pattern, found.root);
        if let Some(map) = found.to_match_map(&graph) {
            let mut selected = map.values().map(|n| positions[n]).collect::<Vec<_>>();
            selected.sort_unstable();
            candidates.push(selected);
        }
    }
    candidates.sort_by_key(|c| (*c.last().unwrap(), c.len(), c[0]));
    candidates.dedup();
    candidates
}
