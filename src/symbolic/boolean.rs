use crate::ir::Qubit;
use std::collections::{BTreeSet, HashMap};
use std::fmt;
use std::sync::{Arc, OnceLock};

mod graph;
pub mod statistics;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Variable {
    Input(Qubit),
    /// Owned coherent path coordinate, not an incoherent measurement history.
    Path(usize),
}

/// Temporary algebraic view. No XAG node stores a monomial or ANF table.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Monomial(BTreeSet<Variable>);
impl Monomial {
    pub fn one() -> Self {
        Self::default()
    }
    pub fn variable(v: Variable) -> Self {
        Self(BTreeSet::from([v]))
    }
    pub fn variables(&self) -> impl Iterator<Item = &Variable> {
        self.0.iter()
    }
    pub(crate) fn multiply(&self, other: &Self) -> Self {
        Self(self.0.union(&other.0).cloned().collect())
    }
}

/// Shared XOR/AND graph; historical name retained for API compatibility.
/// Associative fanins are canonical n-ary views of binary XAG gates. AND is
/// never distributed over XOR by constructors. Structural mismatch is not NEQ.
#[derive(Debug, Clone)]
pub struct BooleanPolynomial(Arc<Node>);
struct Node {
    expression: Expression,
    /// None marks an already normalized node; never store an Arc to self.
    /// Changed forms own only rebuilt nodes/subgraphs, not the source root.
    normalized: OnceLock<Option<BooleanPolynomial>>,
}
impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.expression.fmt(f)
    }
}
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Expression {
    Constant(bool),
    Variable(Variable),
    Xor(BTreeSet<BooleanPolynomial>),
    And(BTreeSet<BooleanPolynomial>),
}
impl PartialEq for BooleanPolynomial {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0) || self.0.expression == other.0.expression
    }
}
impl Eq for BooleanPolynomial {}
impl std::hash::Hash for BooleanPolynomial {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.0.expression.hash(state);
    }
}
impl PartialOrd for BooleanPolynomial {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for BooleanPolynomial {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        if Arc::ptr_eq(&self.0, &other.0) {
            std::cmp::Ordering::Equal
        } else {
            self.0.expression.cmp(&other.0.expression)
        }
    }
}
impl Default for BooleanPolynomial {
    fn default() -> Self {
        Self::zero()
    }
}

impl BooleanPolynomial {
    fn node(expression: Expression) -> Self {
        Self(Arc::new(Node {
            expression,
            normalized: OnceLock::new(),
        }))
    }
    pub(crate) fn expression(&self) -> &Expression {
        &self.0.expression
    }
    pub fn zero() -> Self {
        Self::node(Expression::Constant(false))
    }
    pub fn one() -> Self {
        Self::node(Expression::Constant(true))
    }
    pub fn variable(v: Variable) -> Self {
        Self::node(Expression::Variable(v))
    }
    pub fn is_zero(&self) -> bool {
        matches!(self.expression(), Expression::Constant(false))
    }
    pub fn is_one(&self) -> bool {
        matches!(self.expression(), Expression::Constant(true))
    }
    fn key(&self) -> usize {
        Arc::as_ptr(&self.0) as usize
    }
    fn xor_fanins(&self) -> BTreeSet<Self> {
        match self.expression() {
            Expression::Constant(false) => BTreeSet::new(),
            Expression::Xor(xs) => xs.clone(),
            _ => BTreeSet::from([self.clone()]),
        }
    }
    fn and_fanins(&self) -> BTreeSet<Self> {
        match self.expression() {
            Expression::Constant(true) => BTreeSet::new(),
            Expression::And(xs) => xs.clone(),
            _ => BTreeSet::from([self.clone()]),
        }
    }
    fn from_xor(xs: BTreeSet<Self>) -> Self {
        match xs.len() {
            0 => Self::zero(),
            1 => xs.into_iter().next().unwrap(),
            _ => Self::node(Expression::Xor(xs)),
        }
    }
    /// Bottom-up, non-distributing graph normalization. Memoization is only
    /// keyed by nodes of the live source DAG; temporary rewrite nodes are never
    /// entered by address (their allocations can otherwise be reused).
    pub(crate) fn factored(&self) -> Self {
        // Check before consulting normalized caches: a previous enabled scope
        // must not silently supply its rewrite to an ablated execution.
        if !crate::ablation::permit(crate::ablation::Group::ExpressionSimplify) {
            return self.clone();
        }
        fn root(p: BooleanPolynomial) -> BooleanPolynomial {
            if !matches!(p.expression(), Expression::Xor(_)) {
                return p;
            }
            let mut xs = p.xor_fanins();
            loop {
                let mut uses =
                    std::collections::BTreeMap::<BooleanPolynomial, Vec<BooleanPolynomial>>::new();
                for term in &xs {
                    for factor in term.and_fanins() {
                        uses.entry(factor).or_default().push(term.clone());
                    }
                }
                let Some((factor, terms)) = uses.into_iter().find(|(_, terms)| terms.len() > 1)
                else {
                    break;
                };
                let remainder = BooleanPolynomial::xor_all(terms.into_iter().map(|term| {
                    xs.remove(&term);
                    BooleanPolynomial::and_all(
                        term.and_fanins().into_iter().filter(|p| *p != factor),
                    )
                }));
                let term = factor.and(&root(remainder));
                for part in term.xor_fanins() {
                    if !xs.insert(part.clone()) {
                        xs.remove(&part);
                    }
                }
            }
            BooleanPolynomial::from_xor(xs)
        }
        fn visit(
            p: &BooleanPolynomial,
            memo: &mut HashMap<usize, BooleanPolynomial>,
        ) -> BooleanPolynomial {
            if let Some(cached) = p.0.normalized.get() {
                return cached.clone().unwrap_or_else(|| p.clone());
            }
            if let Some(value) = memo.get(&p.key()) {
                return value.clone();
            }
            let value = match p.expression() {
                Expression::Constant(_) | Expression::Variable(_) => p.clone(),
                Expression::Xor(xs) => root(BooleanPolynomial::xor_all(
                    xs.iter().map(|x| visit(x, memo)),
                )),
                Expression::And(xs) => {
                    BooleanPolynomial::and_all(xs.iter().map(|x| visit(x, memo)))
                }
            };
            let unchanged = value == *p;
            let value = if unchanged { p.clone() } else { value };
            let _ = p.0.normalized.set((!unchanged).then(|| value.clone()));
            memo.insert(p.key(), value.clone());
            value
        }
        visit(self, &mut HashMap::new())
    }
    /// Merge already materialized XOR fanins, with no size admission cap.
    /// Work is proportional to the supplied fanins (up to ordered-set costs);
    /// there is no product distribution or repeated cloning of growing prefixes.
    pub(crate) fn xor_all(values: impl IntoIterator<Item = Self>) -> Self {
        let mut xs = BTreeSet::new();
        for value in values {
            for term in value.xor_fanins() {
                if !xs.insert(term.clone()) {
                    xs.remove(&term);
                }
            }
        }
        Self::from_xor(xs)
    }
    pub(crate) fn and_all(values: impl IntoIterator<Item = Self>) -> Self {
        let mut xs = BTreeSet::new();
        for value in values {
            if value.is_zero() {
                return Self::zero();
            }
            xs.extend(value.and_fanins());
        }
        if xs.iter().any(|p| {
            let positive = p.complement();
            xs.contains(&positive)
                // AND flattening can hide the direct F & !F pair:
                // a & b & !(a & b) still equals zero. The children are
                // existing XAG factors, not expanded polynomial monomials.
                || matches!(positive.expression(), Expression::And(factors) if factors.is_subset(&xs))
        }) {
            return Self::zero();
        }
        match xs.len() {
            0 => Self::one(),
            1 => xs.into_iter().next().unwrap(),
            _ => Self::node(Expression::And(xs)),
        }
    }
    pub fn xor(&self, other: &Self) -> Self {
        if self == other {
            return Self::zero();
        }
        if self.is_zero() {
            return other.clone();
        }
        if other.is_zero() {
            return self.clone();
        }
        Self::xor_all([self.clone(), other.clone()])
    }
    pub fn and(&self, other: &Self) -> Self {
        if self.is_zero() || other.is_zero() {
            return Self::zero();
        }
        if self == other || other.is_one() {
            return self.clone();
        }
        if self.is_one() {
            return other.clone();
        }
        Self::and_all([self.clone(), other.clone()])
    }
    pub fn complement(&self) -> Self {
        self.xor(&Self::one())
    }
    /// Formal XOR columns keep AND-subgraph definitions; never fresh inputs.
    pub(crate) fn xor_terms(&self) -> BTreeSet<Self> {
        self.xor_fanins()
    }
    pub(crate) fn from_monomial(m: Monomial) -> Self {
        m.0.into_iter()
            .fold(Self::one(), |p, v| p.and(&Self::variable(v)))
    }
    pub(crate) fn as_variable(&self) -> Option<&Variable> {
        match self.expression() {
            Expression::Variable(v) => Some(v),
            _ => None,
        }
    }
    pub(crate) fn as_monomial(&self) -> Option<Monomial> {
        match self.expression() {
            Expression::Constant(true) => Some(Monomial::one()),
            Expression::Variable(v) => Some(Monomial::variable(v.clone())),
            Expression::And(xs) => xs
                .iter()
                .map(|x| x.as_variable().cloned())
                .collect::<Option<BTreeSet<_>>>()
                .map(Monomial),
            _ => None,
        }
    }
    pub(crate) fn is_affine(&self) -> bool {
        match self.expression() {
            Expression::Constant(_) | Expression::Variable(_) => true,
            Expression::Xor(xs) => xs.iter().all(|x| x.is_one() || x.as_variable().is_some()),
            Expression::And(_) => false,
        }
    }
    pub(crate) fn affine_coefficient(&self, m: &Monomial) -> Option<bool> {
        self.is_affine()
            .then(|| self.xor_fanins().contains(&Self::from_monomial(m.clone())))
    }
    fn walk(&self, mut f: impl FnMut(&Self)) {
        let mut seen = BTreeSet::new();
        let mut pending = vec![self];
        while let Some(p) = pending.pop() {
            if !seen.insert(p.key()) {
                continue;
            }
            f(p);
            if let Expression::Xor(xs) | Expression::And(xs) = p.expression() {
                pending.extend(xs);
            }
        }
    }
    pub(crate) fn variables(&self) -> BTreeSet<Variable> {
        let mut out = BTreeSet::new();
        self.walk(|p| {
            if let Expression::Variable(v) = p.expression() {
                out.insert(v.clone());
            }
        });
        out
    }
    /// Count stored nodes and edges, not expanded monomials.
    pub fn storage_size(&self) -> usize {
        let mut size = 0;
        self.walk(|p| {
            size += 1;
            if let Expression::Xor(xs) | Expression::And(xs) = p.expression() {
                size += xs.len();
            }
        });
        size
    }
    /// Simultaneous graph traversal: inserted replacements are not revisited.
    pub(crate) fn map_variables(&self, f: impl FnMut(&Variable) -> Self) -> Self {
        Self::map_roots(std::slice::from_ref(self), f)
            .pop()
            .unwrap()
    }
    /// One simultaneous substitution across shared roots. All source roots
    /// remain alive throughout the traversal, so address-keyed memo entries
    /// cannot alias newly allocated replacement nodes. Replacements are never
    /// traversed and the memo is discarded before any source root is dropped.
    pub(crate) fn map_roots(roots: &[Self], mut f: impl FnMut(&Variable) -> Self) -> Vec<Self> {
        fn visit(
            p: &BooleanPolynomial,
            f: &mut impl FnMut(&Variable) -> BooleanPolynomial,
            memo: &mut HashMap<usize, BooleanPolynomial>,
        ) -> BooleanPolynomial {
            if let Some(v) = memo.get(&p.key()) {
                return v.clone();
            }
            let r = match p.expression() {
                Expression::Constant(_) => p.clone(),
                Expression::Variable(v) => f(v),
                Expression::Xor(xs) => {
                    BooleanPolynomial::xor_all(xs.iter().map(|x| visit(x, f, memo)))
                }
                Expression::And(xs) => {
                    BooleanPolynomial::and_all(xs.iter().map(|x| visit(x, f, memo)))
                }
            };
            let r = if r == *p { p.clone() } else { r };
            memo.insert(p.key(), r.clone());
            r
        }
        let mut memo = HashMap::new();
        roots
            .iter()
            .map(|root| visit(root, &mut f, &mut memo))
            .collect()
    }
    pub(crate) fn substitute(&self, v: &Variable, replacement: &Self) -> Self {
        self.map_variables(|w| {
            if w == v {
                replacement.clone()
            } else {
                Self::variable(w.clone())
            }
        })
    }
    pub(crate) fn evaluate<E>(
        &self,
        mut f: impl FnMut(&Variable) -> Result<bool, E>,
    ) -> Result<bool, E> {
        fn visit<E>(
            p: &BooleanPolynomial,
            f: &mut impl FnMut(&Variable) -> Result<bool, E>,
            memo: &mut HashMap<usize, bool>,
        ) -> Result<bool, E> {
            if let Some(v) = memo.get(&p.key()) {
                return Ok(*v);
            }
            let r = match p.expression() {
                Expression::Constant(v) => *v,
                Expression::Variable(v) => f(v)?,
                Expression::Xor(xs) => {
                    let mut r = false;
                    for x in xs {
                        r ^= visit(x, f, memo)?;
                    }
                    r
                }
                Expression::And(xs) => {
                    let mut r = true;
                    for x in xs {
                        r &= visit(x, f, memo)?;
                    }
                    r
                }
            };
            memo.insert(p.key(), r);
            Ok(r)
        }
        visit(self, &mut f, &mut HashMap::new())
    }
    /// A scoped SMT-LIB graph expression: one binding per gate, no ANF or
    /// tree expansion. Missing variables fail closed. Already materialized
    /// graphs do not need an ANF-style node or output-text admission budget.
    pub(crate) fn smt_expression(
        &self,
        mut variable: impl FnMut(&Variable) -> Option<String>,
    ) -> Option<String> {
        let mut ids = HashMap::new();
        let mut nodes = Vec::new();
        let mut pending = vec![(self, false)];
        while let Some((p, ready)) = pending.pop() {
            if ids.contains_key(&p.key()) {
                continue;
            }
            if ready {
                ids.insert(p.key(), nodes.len());
                nodes.push(p);
            } else {
                pending.push((p, true));
                if let Expression::Xor(xs) | Expression::And(xs) = p.expression() {
                    pending.extend(xs.iter().rev().map(|x| (x, false)));
                }
            }
        }
        let names = nodes
            .iter()
            .map(|p| match p.expression() {
                Expression::Variable(v) => variable(v).map(Some),
                _ => Some(None),
            })
            .collect::<Option<Vec<_>>>()?;
        // Local graph bindings must not capture a caller's free names.
        let mut prefix = "irene_xag_".to_owned();
        while names.iter().flatten().any(|name| name.contains(&prefix)) {
            prefix.push('_');
        }
        let mut result = String::new();
        for (i, p) in nodes.iter().enumerate() {
            let value = match p.expression() {
                Expression::Constant(v) => v.to_string(),
                Expression::Variable(_) => names[i].as_ref()?.clone(),
                Expression::Xor(xs) | Expression::And(xs) => {
                    let op = if matches!(p.expression(), Expression::Xor(_)) {
                        "xor"
                    } else {
                        "and"
                    };
                    format!(
                        "({op} {})",
                        xs.iter()
                            .map(|x| format!("{prefix}{}", ids[&x.key()]))
                            .collect::<Vec<_>>()
                            .join(" ")
                    )
                }
            };
            result.push_str(&format!("(let (({prefix}{i} {value})) "));
        }
        result.push_str(&format!("{prefix}{}", nodes.len() - 1));
        result.extend(std::iter::repeat_n(')', nodes.len()));
        Some(result)
    }
    /// Explicit bounded algebraic view. It is not cached in the graph; budget
    /// failure is inconclusive and must never be treated as zero.
    pub fn expanded_terms(&self, limit: usize) -> Option<BTreeSet<Monomial>> {
        fn expand(
            p: &BooleanPolynomial,
            limit: usize,
            work: &mut usize,
            memo: &mut HashMap<usize, BTreeSet<Monomial>>,
        ) -> Option<BTreeSet<Monomial>> {
            *work = work.checked_sub(1)?;
            if let Some(v) = memo.get(&p.key()) {
                return Some(v.clone());
            }
            let r = match p.expression() {
                Expression::Constant(false) => BTreeSet::new(),
                Expression::Constant(true) => BTreeSet::from([Monomial::one()]),
                Expression::Variable(v) => BTreeSet::from([Monomial::variable(v.clone())]),
                Expression::Xor(xs) | Expression::And(xs) => {
                    let xor = matches!(p.expression(), Expression::Xor(_));
                    let mut r = if xor {
                        BTreeSet::new()
                    } else {
                        BTreeSet::from([Monomial::one()])
                    };
                    for x in xs {
                        let rhs = expand(x, limit, work, memo)?;
                        if xor {
                            *work = work.checked_sub(rhs.len())?;
                            for m in rhs {
                                if !r.insert(m.clone()) {
                                    r.remove(&m);
                                }
                            }
                        } else {
                            *work = work.checked_sub(r.len().checked_mul(rhs.len())?)?;
                            let mut product = BTreeSet::new();
                            for a in &r {
                                for b in &rhs {
                                    let m = a.multiply(b);
                                    if !product.insert(m.clone()) {
                                        product.remove(&m);
                                    }
                                    if product.len() > limit {
                                        return None;
                                    }
                                }
                            }
                            r = product;
                        }
                        if r.len() > limit {
                            return None;
                        }
                    }
                    r
                }
            };
            if r.len() > limit {
                return None;
            }
            memo.insert(p.key(), r.clone());
            Some(r)
        }
        expand(
            self,
            limit,
            &mut limit.saturating_mul(64),
            &mut HashMap::new(),
        )
    }
    #[cfg(test)]
    pub fn terms(&self) -> impl Iterator<Item = Monomial> {
        self.expanded_terms(65536)
            .expect("test algebraic view exceeded budget")
            .into_iter()
    }
}
impl From<bool> for BooleanPolynomial {
    fn from(v: bool) -> Self {
        if v { Self::one() } else { Self::zero() }
    }
}
impl fmt::Display for Variable {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Input(q) => write!(f, "x{}_{}", q.register.0, q.index),
            Self::Path(p) => write!(f, "y{p}"),
        }
    }
}
impl fmt::Display for Monomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return f.write_str("1");
        }
        for (i, v) in self.0.iter().enumerate() {
            if i > 0 {
                f.write_str("·")?;
            }
            write!(f, "{v}")?;
        }
        Ok(())
    }
}
impl fmt::Display for BooleanPolynomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_zero() {
            return f.write_str("0");
        }
        // Only print existing flat monomials; never distribute a gate.
        if let Some(terms) = self
            .xor_fanins()
            .iter()
            .map(Self::as_monomial)
            .collect::<Option<BTreeSet<_>>>()
        {
            for (i, m) in terms.iter().enumerate() {
                if i > 0 {
                    f.write_str(" ⊕ ")?;
                }
                write!(f, "{m}")?;
            }
            return Ok(());
        }
        let mut ids = HashMap::new();
        let mut nodes = Vec::new();
        let mut pending = vec![(self, false)];
        while let Some((p, ready)) = pending.pop() {
            if ids.contains_key(&p.key()) {
                continue;
            }
            if ready {
                ids.insert(p.key(), nodes.len());
                nodes.push(p);
            } else {
                pending.push((p, true));
                if let Expression::Xor(xs) | Expression::And(xs) = p.expression() {
                    pending.extend(xs.iter().rev().map(|x| (x, false)));
                }
            }
        }
        f.write_str("let ")?;
        for (i, p) in nodes.iter().enumerate() {
            if i > 0 {
                f.write_str("; ")?;
            }
            write!(f, "b{i}=")?;
            match p.expression() {
                Expression::Constant(v) => write!(f, "{}", u8::from(*v))?,
                Expression::Variable(v) => write!(f, "{v}")?,
                Expression::Xor(xs) | Expression::And(xs) => {
                    for (j, x) in xs.iter().enumerate() {
                        if j > 0 {
                            f.write_str(if matches!(p.expression(), Expression::Xor(_)) {
                                "⊕"
                            } else {
                                "·"
                            })?;
                        }
                        write!(f, "b{}", ids[&x.key()])?;
                    }
                }
            }
        }
        write!(f, " in b{}", nodes.len() - 1)
    }
}
#[cfg(test)]
mod tests;
