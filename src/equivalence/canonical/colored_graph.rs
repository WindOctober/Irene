//! Colored syntax graphs propose bound-path bijections, never semantic verdicts.
//! The existing full HPS reconstruction checker remains the proof boundary.
//! Incidental allocation sharing is erased by structural interning; n-ary
//! Boolean fanins are unordered, while scalar operands and memory slots retain
//! their order. No ANF expansion or independent renaming of fields is allowed.

use super::*;
use crate::ir::{ClassicalBit, NumericExpr, Qubit};
use crate::symbolic::{BooleanExpression, PhaseCoefficient};
use num_rational::BigRational;
use petgraph::graph::{DiGraph, NodeIndex};

const MAX_NODES: usize = 50_000;
const MAX_EDGES: usize = 200_000;
const MAX_VF2_CHECKS: usize = 100_000;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Color {
    Path,
    Input(Qubit),
    Constant(bool),
    Xor,
    And,
    Rational(BigRational),
    Sin(NumericExpr),
    Cos(NumericExpr),
    Sqrt,
    Add,
    Mul,
    Neg,
    Inverse,
    Select,
    Guard,
    Phase(PhaseCoefficient),
    Scalar,
    Quantum(Qubit),
    Classical(ClassicalBit),
    Write(usize, ClassicalBit),
    Discard(usize),
}

/// `path` is transported through the library as witness data, NOT a color.
#[derive(Clone, Debug)]
struct Vertex {
    color: Color,
    path: Option<usize>,
}
impl PartialEq for Vertex {
    fn eq(&self, other: &Self) -> bool {
        self.color == other.color
    }
}
impl Eq for Vertex {}

#[derive(Default)]
struct SyntaxGraph {
    graph: DiGraph<Vertex, u8>,
    paths: BTreeMap<usize, NodeIndex>,
    booleans: BTreeMap<BooleanPolynomial, NodeIndex>,
}

impl SyntaxGraph {
    fn node(&mut self, color: Color) -> Option<NodeIndex> {
        (self.graph.node_count() < MAX_NODES)
            .then(|| self.graph.add_node(Vertex { color, path: None }))
    }
    fn edge(&mut self, from: NodeIndex, to: NodeIndex, port: u8) -> Option<()> {
        if self.graph.edge_count() >= MAX_EDGES {
            return None;
        }
        self.graph.add_edge(from, to, port);
        Some(())
    }
    fn field(&mut self, color: Color, value: NodeIndex) -> Option<()> {
        let field = self.node(color)?;
        self.edge(field, value, 0)
    }
    fn boolean(&mut self, root: &BooleanPolynomial) -> Option<NodeIndex> {
        let mut pending = vec![(root, false)];
        while let Some((value, ready)) = pending.pop() {
            if self.booleans.contains_key(value) {
                continue;
            }
            if !ready {
                pending.push((value, true));
                if let BooleanExpression::Xor(xs) | BooleanExpression::And(xs) = value.expression()
                {
                    pending.extend(xs.iter().map(|x| (x, false)));
                }
                continue;
            }
            let node = match value.expression() {
                BooleanExpression::Constant(v) => self.node(Color::Constant(*v))?,
                BooleanExpression::Variable(Variable::Input(q)) => {
                    self.node(Color::Input(q.clone()))?
                }
                BooleanExpression::Variable(Variable::Path(p)) => *self.paths.get(p)?,
                BooleanExpression::Xor(xs) | BooleanExpression::And(xs) => {
                    let color = if matches!(value.expression(), BooleanExpression::Xor(_)) {
                        Color::Xor
                    } else {
                        Color::And
                    };
                    let node = self.node(color)?;
                    for x in xs {
                        self.edge(node, self.booleans[x], 0)?;
                    }
                    node
                }
            };
            self.booleans.insert(value.clone(), node);
        }
        self.booleans.get(root).copied()
    }
    fn scalar(&mut self, value: &Scalar, depth: usize) -> Option<NodeIndex> {
        if depth > 512 {
            return None;
        }
        let color = match value {
            Scalar::Rational(v) => Color::Rational(v.clone()),
            Scalar::Sin(v) => Color::Sin(v.clone()),
            Scalar::Cos(v) => Color::Cos(v.clone()),
            Scalar::Sqrt(_) => Color::Sqrt,
            Scalar::Add(..) => Color::Add,
            Scalar::Mul(..) => Color::Mul,
            Scalar::Neg(_) => Color::Neg,
            Scalar::Inverse(_) => Color::Inverse,
            Scalar::Select { .. } => Color::Select,
        };
        let node = self.node(color)?;
        match value {
            Scalar::Sqrt(v) | Scalar::Neg(v) | Scalar::Inverse(v) => {
                let child = self.scalar(v, depth + 1)?;
                self.edge(node, child, 0)?;
            }
            Scalar::Add(a, b) | Scalar::Mul(a, b) => {
                for (port, child) in [(0, a), (1, b)] {
                    let child = self.scalar(child, depth + 1)?;
                    self.edge(node, child, port)?;
                }
            }
            Scalar::Select {
                condition,
                when_true,
                when_false,
            } => {
                let condition = self.boolean(condition)?;
                self.edge(node, condition, 0)?;
                for (port, child) in [(1, when_true), (2, when_false)] {
                    let child = self.scalar(child, depth + 1)?;
                    self.edge(node, child, port)?;
                }
            }
            _ => {}
        }
        Some(node)
    }
    fn build(source: &Component) -> Option<Self> {
        let mut result = Self::default();
        for path in &source.path_support {
            let node = result.node(Color::Path)?;
            result.graph[node].path = Some(*path);
            result.paths.insert(*path, node);
        }
        for guard in &source.guard {
            let value = result.boolean(guard)?;
            // Separate occurrences preserve guard multiplicity.
            result.field(Color::Guard, value)?;
        }
        let scalar = result.scalar(&source.scalar, 0)?;
        result.field(Color::Scalar, scalar)?;
        for (value, coefficient) in source.phase.selectors() {
            let value = result.boolean(&value)?;
            result.field(Color::Phase(coefficient.clone()), value)?;
        }
        for (q, value) in &source.output.quantum {
            let value = result.boolean(value)?;
            result.field(Color::Quantum(q.clone()), value)?;
        }
        for (c, value) in &source.output.classical {
            let value = result.boolean(value)?;
            result.field(Color::Classical(c.clone()), value)?;
        }
        for (i, entry) in source.output.history.iter().enumerate() {
            let color = match entry {
                HistoryEntry::Write { target, .. } => Color::Write(i, target.clone()),
                HistoryEntry::Discard { .. } => Color::Discard(i),
            };
            let value = result.boolean(entry.value())?;
            result.field(color, value)?;
        }
        Some(result)
    }
}

fn numbered(
    source: &Component,
    forward: BTreeMap<usize, usize>,
) -> (Component, ComponentAlphaRenaming) {
    let value = normalize_component(rename_component(source, &forward));
    let certificate = ComponentAlphaRenaming {
        source_component: 0,
        canonical_component: 0,
        reverse: forward.iter().map(|(a, b)| (*b, *a)).collect(),
        forward,
    };
    (value, certificate)
}

/// A cheap direct check is useful for identical snapshots and unique bijections.
/// It only verifies the supplied source-order map; it performs no role inference
/// or permutation search.
fn direct_pair(
    left: &Component,
    right: &Component,
) -> Option<(Component, ComponentAlphaRenaming, ComponentAlphaRenaming)> {
    let a = left
        .path_support
        .iter()
        .copied()
        .enumerate()
        .map(|(i, p)| (p, i))
        .collect();
    let b = right
        .path_support
        .iter()
        .copied()
        .enumerate()
        .map(|(i, p)| (p, i))
        .collect();
    checked_pair(left, right, a, b)
}

fn checked_pair(
    left: &Component,
    right: &Component,
    a: BTreeMap<usize, usize>,
    b: BTreeMap<usize, usize>,
) -> Option<(Component, ComponentAlphaRenaming, ComponentAlphaRenaming)> {
    let (value, l) = numbered(left, a);
    let (other, r) = numbered(right, b);
    // The library only proposes a map. Reconstruct every semantic field.
    (value == other && l.verify(left, &value) && r.verify(right, &value)).then_some((value, l, r))
}

fn pair(
    left: &Component,
    right: &Component,
) -> Option<(Component, ComponentAlphaRenaming, ComponentAlphaRenaming)> {
    if left.path_support.len() != right.path_support.len() {
        return None;
    }
    if let Some(result) = direct_pair(left, right) {
        return Some(result);
    }
    if left.path_support.len() <= 1 {
        return None;
    }
    let a = SyntaxGraph::build(left)?;
    let b = SyntaxGraph::build(right)?;
    if std::env::var_os("IRENE_ALPHA_STATS").is_some() {
        eprintln!(
            "alpha_graph nodes={}/{} edges={}/{}",
            a.graph.node_count(),
            b.graph.node_count(),
            a.graph.edge_count(),
            b.graph.edge_count()
        );
    }
    if a.graph.node_count() != b.graph.node_count() || a.graph.edge_count() != b.graph.edge_count()
    {
        return None;
    }
    let mut checks = 0;
    let mut nodes = |a: &Vertex, b: &Vertex| {
        checks += 1;
        checks <= MAX_VF2_CHECKS && a == b
    };
    let mut edges = |a: &u8, b: &u8| a == b;
    // Equal node/edge counts make this a whole-graph isomorphism. A rejected
    // candidate (including the resource cap) only makes this proof inconclusive.
    let mapping =
        petgraph::algo::subgraph_isomorphisms_iter(&&a.graph, &&b.graph, &mut nodes, &mut edges)?
            .next()?;
    let left_map: BTreeMap<_, _> = left
        .path_support
        .iter()
        .copied()
        .enumerate()
        .map(|(i, p)| (p, i))
        .collect();
    let mut right_map = BTreeMap::new();
    for (path, index) in &a.paths {
        let mapped = b
            .graph
            .node_weight(NodeIndex::new(*mapping.get(index.index())?))?
            .path?;
        right_map.insert(mapped, left_map[path]);
    }
    checked_pair(left, right, left_map, right_map)
}

pub(super) fn exact_match(left: &HybridPathSum, right: &HybridPathSum) -> ExactMatch {
    if left.input != right.input || component_path_counts(left) != component_path_counts(right) {
        return ExactMatch::NoMatch;
    }
    for (source, side) in [(left, CanonicalSide::Left), (right, CanonicalSide::Right)] {
        if let Err(error) = validate(source) {
            return ExactMatch::Unknown { side, error };
        }
    }
    // Components are a multiset of summands, never a set: each right component
    // must be consumed exactly once. A proven alpha-equivalent pair can be
    // removed greedily without changing the remaining multiset equality.
    let mut used = vec![false; right.components.len()];
    let mut pairs = Vec::with_capacity(left.components.len());
    for (i, component) in left.components.iter().enumerate() {
        let candidate = right
            .components
            .iter()
            .enumerate()
            .filter(|(j, _)| !used[*j])
            .find_map(|(j, other)| pair(component, other).map(|value| (j, value)));
        let Some((j, (value, mut a, mut b))) = candidate else {
            return ExactMatch::NoMatch;
        };
        used[j] = true;
        a.source_component = i;
        b.source_component = j;
        pairs.push((value, a, b));
    }
    // This is a common reconstructed snapshot, not a standalone graph
    // canonical form. Sorting keeps the certificate's existing ordering check.
    pairs.sort_by(|a, b| component_cmp(&a.0, &b.0));
    let mut canonical = HybridPathSum {
        input: left.input.clone(),
        components: vec![],
    };
    let mut a = CanonicalizationCertificate { components: vec![] };
    let mut b = CanonicalizationCertificate { components: vec![] };
    for (i, (value, mut l, mut r)) in pairs.into_iter().enumerate() {
        l.canonical_component = i;
        r.canonical_component = i;
        canonical.components.push(value);
        a.components.push(l);
        b.components.push(r);
    }
    if !a.verify(left, &canonical) || !b.verify(right, &canonical) {
        return ExactMatch::NoMatch;
    }
    ExactMatch::Match { left: a, right: b }
}

#[cfg(test)]
mod tests;
