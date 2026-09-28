//! Exact lowering from one normalized HPS to a doubled density kernel.
//!
//! Lowering preserves XAG structure, including weighted phase selectors.
//! Already-flat monomial rows can still use the algebraic reducer, but kernel
//! admission never requests a distributed ANF. Graph summands are reduced and
//! encoded exactly; budgets apply to actual complete summation/SMT work.
//!
//! The result represents
//!
//! `K(c, q, q'; x, x') = sum_h A_h(c, q; x) * conj(A_h(c, q'; x'))`.
//!
//! Ket and bra inputs and paths have disjoint Boolean namespaces.  Components
//! are paired only inside the HPS passed to [`build_kernel`]; histories from
//! the two programs being compared must never be matched against each other.
//!
//! [`DensityKernel::terms`] is deliberately an *unaggregated* sum.  Several
//! terms can contribute to the same concrete kernel entry and must have their
//! complex weights added before that entry is compared.  In particular, an
//! equality verdict (or a counterexample) is never sound merely because two
//! individual [`KernelTerm`]s differ.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use num_bigint::BigInt;
use num_rational::BigRational;
use thiserror::Error;

use crate::ir::{NumericExpr, Qubit, SymbolId};
use crate::symbolic::{
    BooleanPolynomial, HistoryEntry, HybridPathSum, PhaseCoefficient, PhasePolynomial, Scalar,
    Variable,
};

/// Upper bound on the eager coherent outer-product candidates for one HPS.
/// Exceeding it is an incompleteness result, never a semantic approximation.
const MAX_COMPONENT_PAIR_CANDIDATES: usize = 65_536;

/// Optional lookup metadata only; exceeding it falls back to exact scans.
const MAX_PHASE_INDEX_CELLS: usize = 250_000;

/// A Boolean variable in the doubled kernel.
///
/// Input and output variables are canonical free indices of the channel
/// kernel. Path variables are summed independently on the ket and bra sides
/// of each term. They carry the term that owns their binder, so later
/// aggregation cannot accidentally couple equal HPS path numbers from
/// different outer-product terms.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KernelVariable {
    InputKet(usize),
    InputBra(usize),
    QuantumOutputKet(usize),
    QuantumOutputBra(usize),
    ClassicalOutput(usize),
    PathKet { term: usize, path: usize },
    PathBra { term: usize, path: usize },
}

impl KernelVariable {
    /// Private, injective graph namespace. These are NOT physical HPS inputs:
    /// the inverse mapping is used before any binder/free-coordinate decision.
    fn graph_variable(&self) -> Variable {
        let (tag, index) = match *self {
            Self::InputKet(i) => (0, i),
            Self::InputBra(i) => (1, i),
            Self::QuantumOutputKet(i) => (2, i),
            Self::QuantumOutputBra(i) => (3, i),
            Self::ClassicalOutput(i) => (4, i),
            Self::PathKet { term, path } => (
                term.checked_mul(2)
                    .and_then(|n| n.checked_add(6))
                    .expect("kernel term namespace overflow"),
                path,
            ),
            Self::PathBra { term, path } => (
                term.checked_mul(2)
                    .and_then(|n| n.checked_add(7))
                    .expect("kernel term namespace overflow"),
                path,
            ),
        };
        Variable::Input(Qubit {
            register: SymbolId(tag),
            index,
        })
    }
    pub(super) fn from_graph_variable(v: &Variable) -> Self {
        let Variable::Input(Qubit {
            register: SymbolId(tag),
            index,
        }) = *v
        else {
            unreachable!("private kernel graph namespace")
        };
        match tag {
            0 => Self::InputKet(index),
            1 => Self::InputBra(index),
            2 => Self::QuantumOutputKet(index),
            3 => Self::QuantumOutputBra(index),
            4 => Self::ClassicalOutput(index),
            n if n >= 6 && n % 2 == 0 => Self::PathKet {
                term: (n - 6) / 2,
                path: index,
            },
            n if n >= 7 => Self::PathBra {
                term: (n - 7) / 2,
                path: index,
            },
            _ => unreachable!("private kernel graph namespace"),
        }
    }
    /// Whether this variable is a locally bound summation index.
    pub(crate) fn is_bound_path(&self) -> bool {
        matches!(self, Self::PathKet { .. } | Self::PathBra { .. })
    }
}

/// A conjunction of kernel Boolean variables.  The empty monomial is one.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct KernelMonomial(BTreeSet<KernelVariable>);

impl KernelMonomial {
    pub(crate) fn from_variables(variables: impl IntoIterator<Item = KernelVariable>) -> Self {
        Self(variables.into_iter().collect())
    }

    pub fn one() -> Self {
        Self::default()
    }

    pub fn variable(variable: KernelVariable) -> Self {
        Self(BTreeSet::from([variable]))
    }

    pub fn variables(&self) -> impl Iterator<Item = &KernelVariable> {
        self.0.iter()
    }

    pub(crate) fn contains(&self, variable: &KernelVariable) -> bool {
        self.0.contains(variable)
    }

    pub(crate) fn without(&self, variable: &KernelVariable) -> Self {
        Self(
            self.0
                .iter()
                .filter(|current| *current != variable)
                .cloned()
                .collect(),
        )
    }

    pub(crate) fn multiply(&self, other: &Self) -> Self {
        Self(self.0.union(&other.0).cloned().collect())
    }

    fn rename_variables(&self, replacements: &BTreeMap<KernelVariable, KernelVariable>) -> Self {
        Self(
            self.0
                .iter()
                .map(|variable| replacements.get(variable).unwrap_or(variable).clone())
                .collect(),
        )
    }
}

/// A Boolean kernel expression. Non-flat expressions remain shared XAGs.
/// `terms` is used only when the graph is ALREADY a sum of monomials; obtaining
/// this view never distributes AND over XOR. Algebraic reducers must check
/// `is_algebraic` before inspecting monomials.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct KernelBooleanPolynomial {
    terms: BTreeSet<KernelMonomial>,
    graph: Option<BooleanPolynomial>,
}

impl KernelBooleanPolynomial {
    pub fn zero() -> Self {
        Self::default()
    }

    pub fn one() -> Self {
        Self {
            terms: BTreeSet::from([KernelMonomial::one()]),
            graph: None,
        }
    }

    pub fn variable(variable: KernelVariable) -> Self {
        Self {
            terms: BTreeSet::from([KernelMonomial::variable(variable)]),
            graph: None,
        }
    }

    pub fn is_zero(&self) -> bool {
        self.graph
            .as_ref()
            .map_or_else(|| self.terms.is_empty(), BooleanPolynomial::is_zero)
    }

    pub fn is_one(&self) -> bool {
        self.graph.as_ref().map_or_else(
            || self.terms.len() == 1 && self.terms.contains(&KernelMonomial::one()),
            BooleanPolynomial::is_one,
        )
    }

    pub fn terms(&self) -> impl Iterator<Item = &KernelMonomial> {
        assert!(
            self.is_algebraic(),
            "monomial view requires an already-flat graph"
        );
        self.terms.iter()
    }

    pub(crate) fn term_count(&self) -> usize {
        self.graph
            .as_ref()
            .map_or(self.terms.len(), BooleanPolynomial::storage_size)
    }

    pub(crate) fn has_term(&self, term: &KernelMonomial) -> bool {
        self.terms.contains(term)
    }

    pub(crate) fn from_monomial(term: KernelMonomial) -> Self {
        Self {
            terms: BTreeSet::from([term]),
            graph: None,
        }
    }

    /// Insert a term from a provably distinct enumeration directly. This is NOT
    /// XOR insertion: a caller expecting uniqueness must reject `false` rather
    /// than silently treating duplicate contributions as a single term.
    pub(super) fn insert_distinct_monomial(&mut self, term: KernelMonomial) -> bool {
        self.terms.insert(term)
    }

    /// XOR-collect monomials without repeatedly cloning a growing prefix.
    pub(crate) fn from_monomials(terms: impl IntoIterator<Item = KernelMonomial>) -> Self {
        let mut result = Self::zero();
        for term in terms {
            // Consume the supplied key; an XOR collision removes the old key.
            // No second owned copy of a newly constructed monomial is needed.
            if !result.terms.remove(&term) {
                result.terms.insert(term);
            }
        }
        result
    }

    pub fn variables(&self) -> BTreeSet<KernelVariable> {
        if let Some(graph) = &self.graph {
            return graph
                .variables()
                .iter()
                .map(KernelVariable::from_graph_variable)
                .collect();
        }
        self.terms
            .iter()
            .flat_map(|term| term.variables().cloned())
            .collect()
    }

    pub fn xor(&self, other: &Self) -> Self {
        if self.graph.is_some() || other.graph.is_some() {
            return Self::from_graph(self.as_graph().xor(&other.as_graph()));
        }
        let mut terms = self.terms.clone();
        for term in &other.terms {
            if !terms.insert(term.clone()) {
                terms.remove(term);
            }
        }
        Self { terms, graph: None }
    }

    pub fn and(&self, other: &Self) -> Self {
        if self.graph.is_some() || other.graph.is_some() {
            return Self::from_graph(self.as_graph().and(&other.as_graph()));
        }
        let mut result = Self::zero();
        for left in &self.terms {
            for right in &other.terms {
                let term = left.multiply(right);
                if !result.terms.insert(term.clone()) {
                    result.terms.remove(&term);
                }
            }
        }
        result
    }

    pub fn complement(&self) -> Self {
        self.xor(&Self::one())
    }

    /// Simultaneous literal substitution; duplicate Boolean monomials cancel.
    pub(crate) fn rename_variables(
        &self,
        replacements: &BTreeMap<KernelVariable, KernelVariable>,
    ) -> Self {
        if let Some(graph) = &self.graph {
            return Self::from_graph(graph.map_variables(|v| {
                let original = KernelVariable::from_graph_variable(v);
                BooleanPolynomial::variable(
                    replacements
                        .get(&original)
                        .unwrap_or(&original)
                        .graph_variable(),
                )
            }));
        }
        let mut terms = BTreeSet::new();
        for term in &self.terms {
            let renamed = term.rename_variables(replacements);
            if !terms.insert(renamed.clone()) {
                terms.remove(&renamed);
            }
        }
        Self { terms, graph: None }
    }

    /// Replaces one kernel variable by an ANF expression.
    ///
    /// For example, substituting `z = y xor x` into `z xor y` yields `x`.
    pub(crate) fn substitute(&self, variable: &KernelVariable, replacement: &Self) -> Self {
        if self.graph.is_some() || replacement.graph.is_some() {
            return Self::from_graph(
                self.as_graph()
                    .substitute(&variable.graph_variable(), &replacement.as_graph()),
            );
        }
        let mut result = Self::zero();
        for monomial in &self.terms {
            if monomial.contains(variable) {
                let rest = monomial.without(variable);
                for factor in &replacement.terms {
                    let product = rest.multiply(factor);
                    if !result.terms.insert(product.clone()) {
                        result.terms.remove(&product);
                    }
                }
            } else if !result.terms.insert(monomial.clone()) {
                result.terms.remove(monomial);
            }
        }
        result
    }

    pub(super) fn is_algebraic(&self) -> bool {
        self.graph.is_none()
    }
    pub(super) fn as_graph(&self) -> BooleanPolynomial {
        self.graph.clone().unwrap_or_else(|| {
            BooleanPolynomial::xor_all(self.terms.iter().map(|m| {
                BooleanPolynomial::and_all(
                    m.variables()
                        .map(|v| BooleanPolynomial::variable(v.graph_variable())),
                )
            }))
        })
    }
    pub(super) fn from_graph(graph: BooleanPolynomial) -> Self {
        // Recognize existing flat syntax only; NEVER expand a product.
        if let Some(terms) = graph
            .xor_terms()
            .iter()
            .map(BooleanPolynomial::as_monomial)
            .collect::<Option<Vec<_>>>()
        {
            return Self::from_monomials(terms.iter().map(|m| {
                KernelMonomial::from_variables(
                    m.variables().map(KernelVariable::from_graph_variable),
                )
            }));
        }
        Self {
            terms: BTreeSet::new(),
            graph: Some(graph),
        }
    }
}

impl From<bool> for KernelBooleanPolynomial {
    fn from(value: bool) -> Self {
        if value { Self::one() } else { Self::zero() }
    }
}

/// An exact equality between two Boolean expressions.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct KernelEquality {
    pub left: KernelBooleanPolynomial,
    pub right: KernelBooleanPolynomial,
}

impl KernelEquality {
    /// Returns the equation-to-zero form `left xor right = 0`.
    pub fn equation(&self) -> KernelBooleanPolynomial {
        self.left.xor(&self.right)
    }
}

/// One exact phase polynomial after renaming into a kernel namespace.
#[derive(Debug, Clone, Default)]
pub struct KernelPhasePolynomial {
    terms: BTreeMap<KernelMonomial, PhaseCoefficient>,
    selectors: BTreeMap<KernelBooleanPolynomial, PhaseCoefficient>,
    occurrences: Option<PhaseOccurrences>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct PhaseOccurrences {
    by_variable: BTreeMap<KernelVariable, BTreeSet<Arc<KernelMonomial>>>,
    cells: usize,
}

// The optional index is not part of the phase, its ordering, or a certificate.
impl PartialEq for KernelPhasePolynomial {
    fn eq(&self, other: &Self) -> bool {
        self.terms == other.terms && self.selectors == other.selectors
    }
}

impl Eq for KernelPhasePolynomial {}

impl PartialOrd for KernelPhasePolynomial {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for KernelPhasePolynomial {
    fn cmp(&self, other: &Self) -> Ordering {
        self.terms
            .cmp(&other.terms)
            .then_with(|| self.selectors.cmp(&other.selectors))
    }
}

impl KernelPhasePolynomial {
    /// The optional exact index has its own maintained incidence ceiling.
    /// This is scheduling metadata only, never a semantic certificate.
    #[cfg(test)]
    pub(crate) fn has_occurrence_index(&self) -> bool {
        self.occurrences.is_some()
    }

    /// Builds a bounded exact occurrence index. Shared immutable monomial
    /// keys avoid copying a degree-d monomial d times into the index.
    pub(crate) fn index_occurrences(&mut self) {
        if !self.selectors.is_empty() {
            return;
        }
        if self.occurrences.is_some() {
            return;
        }
        let mut cells = 0usize;
        for monomial in self.terms.keys() {
            cells = cells.saturating_add(monomial.0.len());
            if cells > MAX_PHASE_INDEX_CELLS {
                return;
            }
        }
        let mut index = PhaseOccurrences {
            cells,
            ..PhaseOccurrences::default()
        };
        for monomial in self.terms.keys() {
            let monomial = Arc::new(monomial.clone());
            for variable in monomial.variables() {
                index
                    .by_variable
                    .entry(variable.clone())
                    .or_default()
                    .insert(monomial.clone());
            }
        }
        self.occurrences = Some(index);
    }

    pub(crate) fn terms_containing<'a>(
        &'a self,
        variable: &'a KernelVariable,
    ) -> Box<dyn Iterator<Item = (&'a KernelMonomial, &'a PhaseCoefficient)> + 'a> {
        if let Some(index) = &self.occurrences {
            Box::new(
                index
                    .by_variable
                    .get(variable)
                    .into_iter()
                    .flat_map(BTreeSet::iter)
                    .map(|monomial| {
                        (
                            monomial.as_ref(),
                            self.terms
                                .get(monomial.as_ref())
                                .expect("phase occurrence keys are maintained with the polynomial"),
                        )
                    }),
            )
        } else {
            Box::new(
                self.terms()
                    .filter(move |(monomial, _)| monomial.contains(variable)),
            )
        }
    }

    pub(crate) fn occurrence_count(&self, variable: &KernelVariable) -> usize {
        if let Some(index) = &self.occurrences {
            index.by_variable.get(variable).map_or(0, BTreeSet::len)
        } else {
            self.terms_containing(variable).count()
        }
    }

    /// Literal renaming needs no XOR lift. Coincident phase monomials add
    /// their arithmetic coefficients (they do not Boolean-XOR cancel).
    pub(crate) fn rename_variables(
        &mut self,
        replacements: &BTreeMap<KernelVariable, KernelVariable>,
    ) {
        for (p, c) in std::mem::take(&mut self.selectors) {
            self.add_selector(p.rename_variables(replacements), c);
        }
        let indexed = self.occurrences.take().is_some();
        for (term, coefficient) in std::mem::take(&mut self.terms) {
            self.add_term(term.rename_variables(replacements), coefficient);
        }
        if indexed {
            self.index_occurrences();
        }
    }

    pub fn terms(&self) -> impl Iterator<Item = (&KernelMonomial, &PhaseCoefficient)> {
        assert!(
            self.is_algebraic(),
            "phase monomial view requires flat selectors"
        );
        self.terms.iter()
    }

    /// Consume exact semantic entries; optional metadata is dropped in full.
    pub(super) fn into_terms(self) -> impl Iterator<Item = (KernelMonomial, PhaseCoefficient)> {
        self.terms.into_iter()
    }

    pub fn coefficient(&self, monomial: &KernelMonomial) -> PhaseCoefficient {
        self.terms.get(monomial).cloned().unwrap_or_default()
    }

    pub(crate) fn term_count(&self) -> usize {
        self.terms.len()
            + self
                .selectors
                .keys()
                .map(KernelBooleanPolynomial::term_count)
                .sum::<usize>()
    }

    pub(crate) fn variables(&self) -> BTreeSet<KernelVariable> {
        if let Some(index) = &self.occurrences {
            return index.by_variable.keys().cloned().collect();
        }
        self.terms
            .keys()
            .flat_map(|term| term.variables().cloned())
            .chain(
                self.selectors
                    .keys()
                    .flat_map(KernelBooleanPolynomial::variables),
            )
            .collect()
    }

    /// Forms the exact density phase `ket - bra`.
    pub(crate) fn difference(ket: &Self, bra: &Self) -> Self {
        let mut result = ket.clone();
        for (monomial, coefficient) in &bra.terms {
            result.add_term(monomial.clone(), coefficient.scaled(BigInt::from(-1)));
        }
        for (p, c) in &bra.selectors {
            result.add_selector(p.clone(), c.scaled(BigInt::from(-1)));
        }
        result
    }

    /// Substitutes a Boolean equality into the arithmetic phase polynomial.
    ///
    /// ANF XOR is lifted arithmetically. In particular, replacing `z` by
    /// `x xor y` in `z/2` produces `(x + y - 2xy)/2`, not `(x+y)/2`.
    pub(crate) fn substitute(
        &mut self,
        variable: &KernelVariable,
        replacement: &KernelBooleanPolynomial,
    ) {
        if !self.is_algebraic() || !replacement.is_algebraic() {
            let old = std::mem::take(self);
            for (p, c) in old.selectors() {
                self.add_selector(p.substitute(variable, replacement), c);
            }
            return;
        }
        let affected = self
            .terms_containing(variable)
            .map(|(monomial, coefficient)| (monomial.clone(), coefficient.clone()))
            .collect::<Vec<_>>();
        for (monomial, _) in &affected {
            self.remove_term(monomial);
        }
        // Preserve unaffected entries in place, but remove all old affected
        // entries before adding lifted replacements. This also handles a
        // self-containing replacement and all exact coefficient collisions.
        for (monomial, coefficient) in affected {
            let substituted =
                KernelBooleanPolynomial::from_monomial(monomial.without(variable)).and(replacement);
            self.add_boolean(&substituted, coefficient);
        }
    }

    /// Exact restriction at zero without copying any surviving phase keys.
    /// Discard the optional occurrence index in full before filtering; future
    /// users either rebuild it or use the complete semantic map.
    pub(super) fn restrict_zero(&mut self, variable: &KernelVariable) {
        self.occurrences = None;
        self.terms
            .retain(|monomial, _| !monomial.contains(variable));
    }

    pub(crate) fn add_boolean(
        &mut self,
        polynomial: &KernelBooleanPolynomial,
        coefficient: PhaseCoefficient,
    ) {
        if !polynomial.is_algebraic() {
            self.add_selector(polynomial.clone(), coefficient);
            return;
        }
        let mut lifted = Self::default();
        for term in polynomial.terms() {
            let products = lifted
                .terms
                .iter()
                .map(|(current, value)| (current.multiply(term), value.scaled(BigInt::from(-2))))
                .collect::<Vec<_>>();
            lifted.add_term(term.clone(), coefficient.clone());
            for (product, value) in products {
                lifted.add_term(product, value);
            }
        }
        for (monomial, value) in lifted.terms {
            self.add_term(monomial, value);
        }
    }

    pub(super) fn add_term(&mut self, monomial: KernelMonomial, coefficient: PhaseCoefficient) {
        if let Some(current) = self.terms.get_mut(&monomial) {
            current.add_assign(coefficient);
            if current.is_zero() {
                self.remove_term(&monomial);
            }
        } else if !coefficient.is_zero() {
            if let Some(index) = &mut self.occurrences {
                let cells = index.cells.saturating_add(monomial.0.len());
                if cells > MAX_PHASE_INDEX_CELLS {
                    // Never expose an incomplete index after a growing rewrite.
                    self.occurrences = None;
                } else {
                    index.cells = cells;
                    let indexed_monomial = Arc::new(monomial.clone());
                    for variable in indexed_monomial.variables() {
                        index
                            .by_variable
                            .entry(variable.clone())
                            .or_default()
                            .insert(indexed_monomial.clone());
                    }
                }
            }
            self.terms.insert(monomial, coefficient);
        }
    }

    pub(super) fn remove_term(&mut self, monomial: &KernelMonomial) {
        if self.terms.remove(monomial).is_none() {
            return;
        }
        if let Some(index) = &mut self.occurrences {
            index.cells -= monomial.0.len();
            for variable in monomial.variables() {
                if let Some(entries) = index.by_variable.get_mut(variable) {
                    entries.remove(monomial);
                    if entries.is_empty() {
                        index.by_variable.remove(variable);
                    }
                }
            }
        }
    }

    pub(super) fn is_algebraic(&self) -> bool {
        self.selectors.is_empty()
    }
    pub(super) fn selectors(
        &self,
    ) -> impl Iterator<Item = (KernelBooleanPolynomial, PhaseCoefficient)> + '_ {
        self.terms
            .iter()
            .map(|(m, c)| (KernelBooleanPolynomial::from_monomial(m.clone()), c.clone()))
            .chain(self.selectors.iter().map(|(p, c)| (p.clone(), c.clone())))
    }
    fn add_selector(&mut self, p: KernelBooleanPolynomial, c: PhaseCoefficient) {
        if p.is_zero() || c.is_zero() {
            return;
        }
        // Half turns lift XOR additively modulo one; no distribution needed.
        if p.is_algebraic()
            && (p.term_count() <= 1
                || c.as_rational() == Some(BigRational::new(1.into(), 2.into())))
        {
            for m in p.terms() {
                self.add_term(m.clone(), c.clone());
            }
            return;
        }
        // Exact binary-XOR phase identity, with the product retained as a
        // graph: c*(a XOR b) = c*a + c*b - 2c*(a AND b). This exposes local
        // phase factors without distributing products or expanding an ANF.
        let parts = p.as_graph().xor_terms();
        if parts.len() > 1 && c.as_rational() == Some(BigRational::new(1.into(), 2.into())) {
            for part in parts {
                self.add_selector(Self::selector_graph(part), c.clone());
            }
            return;
        }
        if parts.len() == 2 {
            let mut parts = parts.into_iter();
            let a = parts.next().unwrap();
            let b = parts.next().unwrap();
            self.add_selector(Self::selector_graph(a.clone()), c.clone());
            self.add_selector(Self::selector_graph(b.clone()), c.clone());
            self.add_selector(Self::selector_graph(a.and(&b)), c.scaled(BigInt::from(-2)));
            return;
        }
        let mut value = self.selectors.remove(&p).unwrap_or_default();
        value.add_assign(c);
        if !value.is_zero() {
            self.selectors.insert(p, value);
        }
        self.occurrences = None;
    }
    fn selector_graph(p: BooleanPolynomial) -> KernelBooleanPolynomial {
        KernelBooleanPolynomial::from_graph(p)
    }
}

/// The exact phase `ket - bra` in a density-kernel term.
///
/// Keeping the two canonical phase polynomials separate avoids opening the
/// opaque symbolic-angle representation merely to negate its coefficients.
/// Its denotation is always `exp(2*pi*i*(ket - bra))`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct KernelPhaseDifference {
    pub ket: KernelPhasePolynomial,
    pub bra: KernelPhasePolynomial,
}

/// Exact scalar syntax with Boolean selections renamed into the kernel graph.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum KernelScalar {
    Rational(BigRational),
    Sqrt(Box<KernelScalar>),
    Sin(NumericExpr),
    Cos(NumericExpr),
    Add(Box<KernelScalar>, Box<KernelScalar>),
    Mul(Box<KernelScalar>, Box<KernelScalar>),
    Neg(Box<KernelScalar>),
    Inverse(Box<KernelScalar>),
    Select {
        condition: KernelBooleanPolynomial,
        when_true: Box<KernelScalar>,
        when_false: Box<KernelScalar>,
    },
}

impl KernelScalar {
    pub(crate) fn rename_variables(
        &self,
        replacements: &BTreeMap<KernelVariable, KernelVariable>,
    ) -> Self {
        match self {
            Self::Rational(_) | Self::Sin(_) | Self::Cos(_) => self.clone(),
            Self::Sqrt(value) => Self::Sqrt(Box::new(value.rename_variables(replacements))),
            Self::Add(left, right) => Self::Add(
                Box::new(left.rename_variables(replacements)),
                Box::new(right.rename_variables(replacements)),
            ),
            Self::Mul(left, right) => Self::Mul(
                Box::new(left.rename_variables(replacements)),
                Box::new(right.rename_variables(replacements)),
            ),
            Self::Neg(value) => Self::Neg(Box::new(value.rename_variables(replacements))),
            Self::Inverse(value) => Self::Inverse(Box::new(value.rename_variables(replacements))),
            Self::Select {
                condition,
                when_true,
                when_false,
            } => {
                let condition = condition.rename_variables(replacements);
                if condition.is_zero() {
                    when_false.rename_variables(replacements)
                } else if condition.is_one() {
                    when_true.rename_variables(replacements)
                } else {
                    Self::Select {
                        condition,
                        when_true: Box::new(when_true.rename_variables(replacements)),
                        when_false: Box::new(when_false.rename_variables(replacements)),
                    }
                }
            }
        }
    }

    pub fn is_zero(&self) -> bool {
        matches!(self, Self::Rational(value) if value == &BigRational::from_integer(0.into()))
    }

    /// Builds an exact product, applying only identity/zero and rational rules.
    pub fn multiply(self, other: Self) -> Self {
        match (self, other) {
            (Self::Rational(left), Self::Rational(right)) => Self::Rational(left * right),
            (left, right) if left.is_zero() || right.is_zero() => {
                Self::Rational(BigRational::from_integer(0.into()))
            }
            (Self::Rational(value), other) if value == BigRational::from_integer(1.into()) => other,
            (left, Self::Rational(value)) if value == BigRational::from_integer(1.into()) => left,
            (left, right) => Self::Mul(Box::new(left), Box::new(right)),
        }
    }

    pub(crate) fn substitute(
        &self,
        variable: &KernelVariable,
        replacement: &KernelBooleanPolynomial,
    ) -> Self {
        match self {
            Self::Rational(_) | Self::Sin(_) | Self::Cos(_) => self.clone(),
            Self::Sqrt(value) => Self::Sqrt(Box::new(value.substitute(variable, replacement))),
            Self::Add(left, right) => Self::Add(
                Box::new(left.substitute(variable, replacement)),
                Box::new(right.substitute(variable, replacement)),
            ),
            Self::Mul(left, right) => Self::Mul(
                Box::new(left.substitute(variable, replacement)),
                Box::new(right.substitute(variable, replacement)),
            ),
            Self::Neg(value) => Self::Neg(Box::new(value.substitute(variable, replacement))),
            Self::Inverse(value) => {
                Self::Inverse(Box::new(value.substitute(variable, replacement)))
            }
            Self::Select {
                condition,
                when_true,
                when_false,
            } => {
                let condition = condition.substitute(variable, replacement);
                if condition.is_zero() {
                    when_false.substitute(variable, replacement)
                } else if condition.is_one() {
                    when_true.substitute(variable, replacement)
                } else {
                    Self::Select {
                        condition,
                        when_true: Box::new(when_true.substitute(variable, replacement)),
                        when_false: Box::new(when_false.substitute(variable, replacement)),
                    }
                }
            }
        }
    }
}

/// The real scalar weight `ket * bra` of one density term.
///
/// HPS scalars are real; complex conjugation changes only the phase.  The
/// factors are retained separately as useful provenance, while [`Self::product`]
/// returns the exact product expression.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct KernelWeight {
    pub ket: KernelScalar,
    pub bra: KernelScalar,
}

impl KernelWeight {
    pub fn product(&self) -> KernelScalar {
        self.ket.clone().multiply(self.bra.clone())
    }
}

/// Canonical free input pair `(x_i, x'_i)`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct KernelInputPair {
    pub ket: KernelVariable,
    pub bra: KernelVariable,
}

/// Ket/bra values of one visible classical output.
///
/// The equality of these expressions is also part of the term constraints,
/// ensuring the density operator is block diagonal in the classical output.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct KernelClassicalOutput {
    pub ket: KernelBooleanPolynomial,
    pub bra: KernelBooleanPolynomial,
}

impl KernelClassicalOutput {
    pub fn equality(&self) -> KernelEquality {
        KernelEquality {
            left: self.ket.clone(),
            right: self.bra.clone(),
        }
    }
}

/// One unaggregated summand of the doubled channel/density kernel.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct KernelTerm {
    /// Equations to zero selecting the ket component.
    pub ket_guard: Vec<KernelBooleanPolynomial>,
    /// Equations to zero selecting the bra component.
    pub bra_guard: Vec<KernelBooleanPolynomial>,
    /// Equality constraints imposed by tracing the complete hidden history.
    pub history_equalities: Vec<KernelEquality>,
    /// Independent path variables summed on each side of this term.
    pub ket_paths: BTreeSet<KernelVariable>,
    pub bra_paths: BTreeSet<KernelVariable>,
    /// Computational-basis quantum output indices `q` and `q'`.
    pub quantum_outputs_ket: Vec<KernelBooleanPolynomial>,
    pub quantum_outputs_bra: Vec<KernelBooleanPolynomial>,
    /// The shared visible classical output index `c`.
    pub classical_outputs: Vec<KernelClassicalOutput>,
    /// Exact real factor `scalar_i * scalar_j`.
    pub weight: KernelWeight,
    /// Exact phase factor `exp(2*pi*i*(phase_i - phase_j))`.
    pub phase: KernelPhaseDifference,
}

impl KernelTerm {
    /// All Boolean constraints in uniform equation-to-zero form.
    pub fn constraint_equations(&self) -> Vec<KernelBooleanPolynomial> {
        self.ket_guard
            .iter()
            .chain(&self.bra_guard)
            .cloned()
            .chain(self.history_equalities.iter().map(KernelEquality::equation))
            .chain(
                self.classical_outputs
                    .iter()
                    .map(KernelClassicalOutput::equality)
                    .map(|equality| equality.equation()),
            )
            .collect()
    }
}

/// An exact, unaggregated density/channel kernel for one program.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DensityKernel {
    /// Explicit independent free inputs `(x, x')`, including unused inputs.
    pub input_pairs: Vec<KernelInputPair>,
    pub quantum_output_count: usize,
    pub classical_output_count: usize,
    /// Unaggregated sum; see the module-level soundness warning.
    pub terms: Vec<KernelTerm>,
}

/// Canonically ordered output expressions for one HPS component.
///
/// This small owned adapter keeps kernel lowering independent of the evolving
/// interface-normalization module.  A caller can partition each prepared
/// terminal into quantum and classical positions and clone its exact graphs here.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct KernelTerminalInput {
    pub quantum: Vec<BooleanPolynomial>,
    pub classical: Vec<BooleanPolynomial>,
}

/// Borrowed HPS plus the compact canonical data needed by [`build_kernel`].
#[derive(Debug, Clone)]
pub struct KernelInput<'a> {
    pub hps: &'a HybridPathSum,
    /// Source [`Variable::Input`] qubits in shared canonical position order.
    pub input_variables: Vec<Qubit>,
    /// One entry per HPS component, in the identical order.
    pub terminals: Vec<KernelTerminalInput>,
}

impl<'a> KernelInput<'a> {
    pub fn new(
        hps: &'a HybridPathSum,
        input_variables: Vec<Qubit>,
        terminals: Vec<KernelTerminalInput>,
    ) -> Self {
        Self {
            hps,
            input_variables,
            terminals,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum KernelBranch {
    Ket,
    Bra,
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum KernelBuildError {
    #[error("duplicate input variable {0:?} in the canonical kernel interface")]
    DuplicateInput(Qubit),
    #[error("HPS expression refers to input {0:?}, which is absent from the kernel interface")]
    UnknownInput(Qubit),
    #[error("the HPS input signature is not the canonical identity map")]
    NonCanonicalInputSignature,
    #[error(
        "{components} HPS components exceed the density-kernel candidate-pair budget of {maximum_pairs}"
    )]
    ComponentPairBudget {
        components: usize,
        maximum_pairs: usize,
    },
    #[error("{branch:?} component uses undeclared path variable y{path}")]
    UndeclaredPath { branch: KernelBranch, path: usize },
    #[error("expected {expected} terminal rows, found {actual}")]
    TerminalCount { expected: usize, actual: usize },
    #[error(
        "terminal row {component} has shape ({quantum} quantum, {classical} classical), expected ({expected_quantum}, {expected_classical})"
    )]
    TerminalShape {
        component: usize,
        quantum: usize,
        classical: usize,
        expected_quantum: usize,
        expected_classical: usize,
    },
    #[error("component {component} retains {count} quantum outputs outside its terminal row")]
    ResidualQuantumOutputs { component: usize, count: usize },
    #[error("component {component} retains {count} classical outputs outside its terminal row")]
    ResidualClassicalOutputs { component: usize, count: usize },
}

/// Lowers one already normalized HPS into its doubled density/channel kernel.
///
/// The construction performs the coherent component cross-product within each
/// compatible history shape.  Corresponding history values and visible
/// classical ket/bra outputs become exact Boolean equalities.  It intentionally
/// does not aggregate equal kernel entries; consumers must sum their weights.
pub fn build_kernel(input: &KernelInput<'_>) -> Result<DensityKernel, KernelBuildError> {
    validate_input(input)?;

    let components = input.hps.components.len();
    if components
        .checked_mul(components)
        .is_none_or(|pairs| pairs > MAX_COMPONENT_PAIR_CANDIDATES)
    {
        return Err(KernelBuildError::ComponentPairBudget {
            components,
            maximum_pairs: MAX_COMPONENT_PAIR_CANDIDATES,
        });
    }

    let input_positions = input
        .input_variables
        .iter()
        .cloned()
        .enumerate()
        .map(|(position, qubit)| (qubit, position))
        .collect::<BTreeMap<_, _>>();

    let input_pairs = (0..input.input_variables.len())
        .map(|position| KernelInputPair {
            ket: KernelVariable::InputKet(position),
            bra: KernelVariable::InputBra(position),
        })
        .collect();

    let quantum_output_count = input.terminals.first().map_or(0, |row| row.quantum.len());
    let classical_output_count = input.terminals.first().map_or(0, |row| row.classical.len());
    let mut terms = Vec::new();

    for (ket_index, ket) in input.hps.components.iter().enumerate() {
        for (bra_index, bra) in input.hps.components.iter().enumerate() {
            let Some(history_pairs) = compatible_history(&ket.output.history, &bra.output.history)
            else {
                continue;
            };

            let term = terms.len();
            let ket_renamer =
                Renamer::new(KernelBranch::Ket, term, &input_positions, &ket.path_support);
            let bra_renamer =
                Renamer::new(KernelBranch::Bra, term, &input_positions, &bra.path_support);
            let ket_terminal = &input.terminals[ket_index];
            let bra_terminal = &input.terminals[bra_index];

            let ket_guard = ket
                .guard
                .iter()
                .map(|guard| ket_renamer.boolean(guard))
                .collect::<Result<_, _>>()?;
            let bra_guard = bra
                .guard
                .iter()
                .map(|guard| bra_renamer.boolean(guard))
                .collect::<Result<_, _>>()?;
            let history_equalities = history_pairs
                .into_iter()
                .map(|(ket_value, bra_value)| {
                    Ok(KernelEquality {
                        left: ket_renamer.boolean(ket_value)?,
                        right: bra_renamer.boolean(bra_value)?,
                    })
                })
                .collect::<Result<_, KernelBuildError>>()?;
            let quantum_outputs_ket = lower_values(&ket_terminal.quantum, &ket_renamer)?;
            let quantum_outputs_bra = lower_values(&bra_terminal.quantum, &bra_renamer)?;
            let classical_outputs = ket_terminal
                .classical
                .iter()
                .zip(&bra_terminal.classical)
                .map(|(ket_value, bra_value)| {
                    Ok(KernelClassicalOutput {
                        ket: ket_renamer.boolean(ket_value)?,
                        bra: bra_renamer.boolean(bra_value)?,
                    })
                })
                .collect::<Result<_, KernelBuildError>>()?;

            terms.push(KernelTerm {
                ket_guard,
                bra_guard,
                history_equalities,
                ket_paths: ket
                    .path_support
                    .iter()
                    .copied()
                    .map(|path| KernelVariable::PathKet { term, path })
                    .collect(),
                bra_paths: bra
                    .path_support
                    .iter()
                    .copied()
                    .map(|path| KernelVariable::PathBra { term, path })
                    .collect(),
                quantum_outputs_ket,
                quantum_outputs_bra,
                classical_outputs,
                weight: KernelWeight {
                    ket: ket_renamer.scalar(&ket.scalar)?,
                    bra: bra_renamer.scalar(&bra.scalar)?,
                },
                phase: KernelPhaseDifference {
                    ket: ket_renamer.phase(&ket.phase)?,
                    bra: bra_renamer.phase(&bra.phase)?,
                },
            });
        }
    }

    Ok(DensityKernel {
        input_pairs,
        quantum_output_count,
        classical_output_count,
        terms,
    })
}

fn validate_input(input: &KernelInput<'_>) -> Result<(), KernelBuildError> {
    let mut inputs = BTreeSet::new();
    for qubit in &input.input_variables {
        if !inputs.insert(qubit.clone()) {
            return Err(KernelBuildError::DuplicateInput(qubit.clone()));
        }
    }
    let canonical_signature = input.hps.input.quantum.len() == input.input_variables.len()
        && input.input_variables.iter().all(|qubit| {
            input.hps.input.quantum.get(qubit)
                == Some(&BooleanPolynomial::variable(Variable::Input(qubit.clone())))
        });
    if !canonical_signature
        || !input.hps.input.classical.is_empty()
        || !input.hps.input.history.is_empty()
    {
        return Err(KernelBuildError::NonCanonicalInputSignature);
    }
    if input.terminals.len() != input.hps.components.len() {
        return Err(KernelBuildError::TerminalCount {
            expected: input.hps.components.len(),
            actual: input.terminals.len(),
        });
    }
    for (component, value) in input.hps.components.iter().enumerate() {
        if !value.output.quantum.is_empty() {
            return Err(KernelBuildError::ResidualQuantumOutputs {
                component,
                count: value.output.quantum.len(),
            });
        }
        if !value.output.classical.is_empty() {
            return Err(KernelBuildError::ResidualClassicalOutputs {
                component,
                count: value.output.classical.len(),
            });
        }
    }
    let Some(first) = input.terminals.first() else {
        return Ok(());
    };
    for (component, terminal) in input.terminals.iter().enumerate() {
        if terminal.quantum.len() != first.quantum.len()
            || terminal.classical.len() != first.classical.len()
        {
            return Err(KernelBuildError::TerminalShape {
                component,
                quantum: terminal.quantum.len(),
                classical: terminal.classical.len(),
                expected_quantum: first.quantum.len(),
                expected_classical: first.classical.len(),
            });
        }
    }
    Ok(())
}

/// Lower a closed coherent scalar without forming its ket/bra outer product.
/// All remaining variables must belong to the explicitly declared sum.
pub(super) fn closed_scalar_parts(
    c: &crate::symbolic::Component,
) -> Option<(
    BTreeSet<KernelVariable>,
    Vec<KernelBooleanPolynomial>,
    KernelScalar,
    KernelPhasePolynomial,
)> {
    if !c.output.quantum.is_empty()
        || !c.output.classical.is_empty()
        || !c.output.history.is_empty()
    {
        return None;
    }
    let inputs = BTreeMap::new();
    let renamer = Renamer::new(KernelBranch::Ket, 0, &inputs, &c.path_support);
    Some((
        c.path_support
            .iter()
            .map(|&path| KernelVariable::PathKet { term: 0, path })
            .collect(),
        lower_values(&c.guard, &renamer).ok()?,
        renamer.scalar(&c.scalar).ok()?,
        renamer.phase(&c.phase).ok()?,
    ))
}

fn lower_values(
    values: &[BooleanPolynomial],
    renamer: &Renamer<'_>,
) -> Result<Vec<KernelBooleanPolynomial>, KernelBuildError> {
    values.iter().map(|value| renamer.boolean(value)).collect()
}

/// Returns corresponding history values only when the event structures match.
/// Value equality itself remains symbolic and is emitted into the kernel.
fn compatible_history<'a>(
    ket: &'a [HistoryEntry],
    bra: &'a [HistoryEntry],
) -> Option<Vec<(&'a BooleanPolynomial, &'a BooleanPolynomial)>> {
    if ket.len() != bra.len() {
        return None;
    }
    ket.iter()
        .zip(bra)
        .map(|(ket, bra)| match (ket, bra) {
            (
                HistoryEntry::Write {
                    target: ket_target,
                    value: ket_value,
                },
                HistoryEntry::Write {
                    target: bra_target,
                    value: bra_value,
                },
            ) if ket_target == bra_target => Some((ket_value, bra_value)),
            (
                HistoryEntry::Discard { value: ket_value },
                HistoryEntry::Discard { value: bra_value },
            ) => Some((ket_value, bra_value)),
            _ => None,
        })
        .collect()
}

struct Renamer<'a> {
    branch: KernelBranch,
    term: usize,
    input_positions: &'a BTreeMap<Qubit, usize>,
    path_support: &'a BTreeSet<usize>,
}

impl<'a> Renamer<'a> {
    fn new(
        branch: KernelBranch,
        term: usize,
        input_positions: &'a BTreeMap<Qubit, usize>,
        path_support: &'a BTreeSet<usize>,
    ) -> Self {
        Self {
            branch,
            term,
            input_positions,
            path_support,
        }
    }

    fn variable(&self, variable: &Variable) -> Result<KernelVariable, KernelBuildError> {
        match variable {
            Variable::Input(qubit) => {
                let position = self
                    .input_positions
                    .get(qubit)
                    .copied()
                    .ok_or_else(|| KernelBuildError::UnknownInput(qubit.clone()))?;
                Ok(match self.branch {
                    KernelBranch::Ket => KernelVariable::InputKet(position),
                    KernelBranch::Bra => KernelVariable::InputBra(position),
                })
            }
            Variable::Path(path) => {
                if !self.path_support.contains(path) {
                    return Err(KernelBuildError::UndeclaredPath {
                        branch: self.branch,
                        path: *path,
                    });
                }
                Ok(match self.branch {
                    KernelBranch::Ket => KernelVariable::PathKet {
                        term: self.term,
                        path: *path,
                    },
                    KernelBranch::Bra => KernelVariable::PathBra {
                        term: self.term,
                        path: *path,
                    },
                })
            }
        }
    }

    fn boolean(
        &self,
        polynomial: &BooleanPolynomial,
    ) -> Result<KernelBooleanPolynomial, KernelBuildError> {
        let replacements = polynomial
            .variables()
            .iter()
            .map(|v| Ok((v.clone(), self.variable(v)?.graph_variable())))
            .collect::<Result<BTreeMap<_, _>, KernelBuildError>>()?;
        Ok(KernelBooleanPolynomial::from_graph(
            polynomial.map_variables(|v| BooleanPolynomial::variable(replacements[v].clone())),
        ))
    }

    fn phase(&self, phase: &PhasePolynomial) -> Result<KernelPhasePolynomial, KernelBuildError> {
        let mut result = KernelPhasePolynomial::default();
        for (p, c) in phase.selectors() {
            result.add_selector(self.boolean(&p)?, c.clone());
        }
        Ok(result)
    }

    fn scalar(&self, scalar: &Scalar) -> Result<KernelScalar, KernelBuildError> {
        Ok(match scalar {
            Scalar::Rational(value) => KernelScalar::Rational(value.clone()),
            Scalar::Sqrt(value) => KernelScalar::Sqrt(Box::new(self.scalar(value)?)),
            Scalar::Sin(angle) => KernelScalar::Sin(angle.clone()),
            Scalar::Cos(angle) => KernelScalar::Cos(angle.clone()),
            Scalar::Add(left, right) => {
                KernelScalar::Add(Box::new(self.scalar(left)?), Box::new(self.scalar(right)?))
            }
            Scalar::Mul(left, right) => {
                KernelScalar::Mul(Box::new(self.scalar(left)?), Box::new(self.scalar(right)?))
            }
            Scalar::Neg(value) => KernelScalar::Neg(Box::new(self.scalar(value)?)),
            Scalar::Inverse(value) => KernelScalar::Inverse(Box::new(self.scalar(value)?)),
            Scalar::Select {
                condition,
                when_true,
                when_false,
            } => KernelScalar::Select {
                condition: self.boolean(condition)?,
                when_true: Box::new(self.scalar(when_true)?),
                when_false: Box::new(self.scalar(when_false)?),
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{ClassicalBit, SymbolId};
    use crate::symbolic::{Component, HybridMemory, PhaseCoefficient, PhasePolynomial};
    use num_bigint::BigInt;

    #[test]
    fn graph_namespaces_round_trip_without_coupling_binders_or_free_indices() {
        let mut variables = vec![
            KernelVariable::InputKet(0),
            KernelVariable::InputBra(0),
            KernelVariable::QuantumOutputKet(0),
            KernelVariable::QuantumOutputBra(0),
            KernelVariable::ClassicalOutput(0),
        ];
        for term in 0..8 {
            for path in 0..4 {
                variables.push(KernelVariable::PathKet { term, path });
                variables.push(KernelVariable::PathBra { term, path });
            }
        }
        let names: BTreeSet<_> = variables
            .iter()
            .map(KernelVariable::graph_variable)
            .collect();
        assert_eq!(names.len(), variables.len());
        for v in variables {
            assert_eq!(KernelVariable::from_graph_variable(&v.graph_variable()), v);
        }
    }

    #[test]
    fn weighted_graph_selectors_keep_exact_phase_under_substitution() {
        let v = |i| BooleanPolynomial::variable(KernelVariable::InputKet(i).graph_variable());
        let selectors = [
            v(0).xor(&v(1)),
            v(0).and(&v(1).xor(&v(2)))
                .xor(&v(3).and(&v(4).complement()))
                .xor(&v(5)),
        ];
        for selector in selectors {
            for denominator in [2, 4, 8, 7] {
                let coefficient = BigRational::new(1.into(), denominator.into());
                let mut phase = KernelPhasePolynomial::default();
                phase.add_selector(
                    KernelBooleanPolynomial::from_graph(selector.clone()),
                    PhaseCoefficient::rational(coefficient.clone()),
                );
                for bits in 0..64 {
                    let bit = |i| bits & (1 << i) != 0;
                    let expected = selector
                        .evaluate::<std::convert::Infallible>(|v| {
                            let KernelVariable::InputKet(i) =
                                KernelVariable::from_graph_variable(v)
                            else {
                                unreachable!()
                            };
                            Ok(bit(i))
                        })
                        .unwrap();
                    let mut actual = phase.clone();
                    for i in 0..6 {
                        actual.substitute(
                            &KernelVariable::InputKet(i),
                            &KernelBooleanPolynomial::from(bit(i)),
                        );
                    }
                    let sum = actual
                        .selectors()
                        .map(|(p, c)| {
                            assert!(p.is_one());
                            c.as_rational().unwrap()
                        })
                        .fold(BigRational::from_integer(0.into()), |a, b| a + b);
                    let target = if expected {
                        coefficient.clone()
                    } else {
                        BigRational::from_integer(0.into())
                    };
                    assert!((sum - target).is_integer());
                }
            }
        }
    }

    #[test]
    fn shared_boolean_lowering_preserves_exponential_anf_as_graph() {
        let inputs = BTreeMap::new();
        let paths = (0..25).collect::<BTreeSet<_>>();
        let renamer = Renamer::new(KernelBranch::Ket, 0, &inputs, &paths);
        let expression = (0..25).fold(BooleanPolynomial::one(), |p, i| {
            p.and(&BooleanPolynomial::variable(Variable::Path(i)).complement())
        });
        let original = expression.clone();
        let lowered = renamer.boolean(&expression).unwrap();
        assert!(!lowered.is_algebraic());
        assert_eq!(lowered.variables().len(), 25);
        assert!(lowered.as_graph().storage_size() < 300);
        assert_eq!(expression, original);
        assert!(expression.storage_size() < 300);
    }

    fn assert_phase_index(phase: &KernelPhasePolynomial) {
        let mut rebuilt = phase.clone();
        rebuilt.occurrences = None;
        rebuilt.index_occurrences();
        assert_eq!(phase.occurrences, rebuilt.occurrences);
        assert_eq!(phase, &rebuilt);
        assert_eq!(phase.cmp(&rebuilt), Ordering::Equal);
    }

    #[test]
    fn monomial_collection_matches_repeated_xor_including_collisions() {
        let monomials = (0..8)
            .map(|bits| {
                KernelMonomial(
                    (0..3)
                        .filter(|index| bits & (1 << index) != 0)
                        .map(KernelVariable::InputKet)
                        .collect(),
                )
            })
            .collect::<Vec<_>>();
        for mask in 0..256 {
            let terms = monomials
                .iter()
                .enumerate()
                .filter(|(i, _)| mask & (1 << i) != 0)
                .map(|(_, term)| term.clone())
                .chain(monomials.iter().cloned())
                .chain(monomials.iter().rev().take(4).cloned())
                .collect::<Vec<_>>();
            let reference = terms.iter().fold(KernelBooleanPolynomial::zero(), |p, m| {
                p.xor(&KernelBooleanPolynomial::from_monomial(m.clone()))
            });
            assert_eq!(KernelBooleanPolynomial::from_monomials(terms), reference);
        }
    }

    #[test]
    fn indexed_phase_substitution_matches_full_scan_for_all_three_bit_anf_replacements() {
        let monomials = (0..8)
            .map(|bits| {
                KernelMonomial(
                    (0..3)
                        .filter(|index| bits & (1 << index) != 0)
                        .map(KernelVariable::InputKet)
                        .collect(),
                )
            })
            .collect::<Vec<_>>();
        let mut source = KernelPhasePolynomial::default();
        for (index, monomial) in monomials.iter().enumerate() {
            source.add_term(
                monomial.clone(),
                PhaseCoefficient::rational(BigRational::new((index + 1).into(), 32.into())),
            );
        }
        let mut indexed = source.clone();
        indexed.index_occurrences();
        assert_eq!(source, indexed);
        assert_eq!(source.cmp(&indexed), Ordering::Equal);
        for bits in 0..256 {
            let replacement = KernelBooleanPolynomial {
                graph: None,
                terms: monomials
                    .iter()
                    .enumerate()
                    .filter(|(index, _)| bits & (1 << index) != 0)
                    .map(|(_, monomial)| monomial.clone())
                    .collect(),
            };
            for index in 0..3 {
                let variable = KernelVariable::InputKet(index);
                // A separate full traversal reconstructs the complete
                // substituted phase, including every unaffected monomial.
                let mut scanned = KernelPhasePolynomial::default();
                for (monomial, coefficient) in source.terms() {
                    if monomial.contains(&variable) {
                        scanned.add_boolean(
                            &KernelBooleanPolynomial::from_monomial(monomial.without(&variable))
                                .and(&replacement),
                            coefficient.clone(),
                        );
                    } else {
                        scanned.add_term(monomial.clone(), coefficient.clone());
                    }
                }
                let mut actual = indexed.clone();
                actual.substitute(&variable, &replacement);
                assert_eq!(actual, scanned);
                assert_phase_index(&actual);
                assert_eq!(
                    actual.occurrence_count(&variable),
                    actual
                        .terms()
                        .filter(|(monomial, _)| monomial.contains(&variable))
                        .count()
                );
            }
        }
    }

    #[test]
    fn phase_index_tracks_cancellation_renaming_and_difference() {
        let x = KernelVariable::InputKet(0);
        let y = KernelVariable::InputBra(0);
        let z = KernelVariable::PathKet { term: 0, path: 0 };
        let eighth = PhaseCoefficient::rational(BigRational::new(1.into(), 8.into()));
        let mut phase = KernelPhasePolynomial::default();
        phase.index_occurrences();
        let xy = KernelMonomial::variable(x.clone()).multiply(&KernelMonomial::variable(y.clone()));
        phase.add_term(xy.clone(), eighth.clone());
        assert_phase_index(&phase);
        phase.add_term(xy, eighth.scaled((-1).into()));
        assert_eq!(phase.occurrence_count(&x), 0);
        assert!(phase.variables().is_empty());
        assert_phase_index(&phase);
        phase.add_boolean(
            &KernelBooleanPolynomial::variable(x.clone())
                .xor(&KernelBooleanPolynomial::variable(y.clone())),
            eighth.clone(),
        );
        phase.add_term(KernelMonomial::one(), eighth);
        assert_phase_index(&phase);
        phase.rename_variables(&BTreeMap::from([(x, z.clone()), (y, z)]));
        // The lift of x XOR y cancels when both names become z. The
        // constant phase remains, despite having no occurrence-index entry.
        assert_eq!(phase.term_count(), 1);
        assert!(phase.variables().is_empty());
        assert_phase_index(&phase);
        let mut unindexed = phase.clone();
        unindexed.occurrences = None;
        let difference = KernelPhasePolynomial::difference(&phase, &unindexed);
        assert_eq!(difference, KernelPhasePolynomial::default());
        assert_phase_index(&difference);
    }

    #[test]
    fn phase_index_refuses_and_invalidates_oversized_metadata() {
        let mut phase = KernelPhasePolynomial::default();
        let coefficient = PhaseCoefficient::rational(BigRational::new(1.into(), 8.into()));
        let kept = KernelMonomial::variable(KernelVariable::InputKet(0));
        phase.add_term(kept.clone(), coefficient.clone());
        phase.index_occurrences();
        let wide = KernelMonomial(
            (0..MAX_PHASE_INDEX_CELLS)
                .map(KernelVariable::InputBra)
                .collect(),
        );
        phase.add_term(wide.clone(), coefficient.clone());
        assert!(phase.occurrences.is_none());
        assert_eq!(phase.term_count(), 2);
        assert_eq!(phase.coefficient(&wide), coefficient);
        phase.index_occurrences();
        assert!(phase.occurrences.is_none());
        assert_eq!(phase.occurrence_count(&KernelVariable::InputBra(0)), 1);
        phase.substitute(
            &KernelVariable::InputBra(0),
            &KernelBooleanPolynomial::zero(),
        );
        assert_eq!(phase.term_count(), 1);
        assert_eq!(phase.coefficient(&kept), coefficient);
        phase.index_occurrences();
        assert_phase_index(&phase);
    }

    fn component(path: usize, history: Vec<HistoryEntry>) -> Component {
        Component {
            guard: vec![BooleanPolynomial::variable(Variable::Path(path))],
            scalar: Scalar::select(
                BooleanPolynomial::variable(Variable::Path(path)),
                Scalar::one(),
                Scalar::zero(),
            ),
            path_support: BTreeSet::from([path]),
            phase: PhasePolynomial::zero(),
            output: HybridMemory {
                quantum: BTreeMap::new(),
                classical: BTreeMap::new(),
                history,
            },
        }
    }

    #[test]
    fn phase_is_exactly_renamed_on_both_sides_of_the_difference() {
        let path = BooleanPolynomial::variable(Variable::Path(3));
        let mut value = component(3, Vec::new());
        value.phase.add_boolean(
            &path,
            PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(8))),
        );
        let hps = HybridPathSum {
            input: HybridMemory::default(),
            components: vec![value],
        };
        let kernel = build_kernel(&KernelInput::new(
            &hps,
            Vec::new(),
            vec![KernelTerminalInput::default()],
        ))
        .unwrap();
        let term = &kernel.terms[0];

        assert_eq!(
            term.phase
                .ket
                .coefficient(&KernelMonomial::variable(KernelVariable::PathKet {
                    term: 0,
                    path: 3
                })),
            PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(8)))
        );
        assert_eq!(
            term.phase
                .bra
                .coefficient(&KernelMonomial::variable(KernelVariable::PathBra {
                    term: 0,
                    path: 3
                })),
            PhaseCoefficient::rational(BigRational::new(BigInt::from(1), BigInt::from(8)))
        );
    }

    #[test]
    fn pairs_only_components_with_compatible_history_structure() {
        let discarded = BooleanPolynomial::variable(Variable::Path(0));
        let write_target = ClassicalBit {
            register: SymbolId(1),
            index: 0,
        };
        let hps = HybridPathSum {
            input: HybridMemory::default(),
            components: vec![
                component(
                    0,
                    vec![HistoryEntry::Discard {
                        value: discarded.clone(),
                    }],
                ),
                component(
                    0,
                    vec![HistoryEntry::Write {
                        target: write_target,
                        value: discarded.clone(),
                    }],
                ),
            ],
        };
        let terminals = vec![
            KernelTerminalInput {
                quantum: Vec::new(),
                classical: vec![discarded.clone()],
            },
            KernelTerminalInput {
                quantum: Vec::new(),
                classical: vec![discarded],
            },
        ];

        let kernel = build_kernel(&KernelInput::new(&hps, Vec::new(), terminals)).unwrap();

        // The two diagonal pairs remain; Discard and Write are different
        // environment structures, so their cross terms are absent.
        assert_eq!(kernel.terms.len(), 2);
    }

    #[test]
    fn compatible_components_form_the_full_coherent_outer_product() {
        let y0 = BooleanPolynomial::variable(Variable::Path(0));
        let y1 = BooleanPolynomial::variable(Variable::Path(1));
        let hps = HybridPathSum {
            input: HybridMemory::default(),
            components: vec![
                component(0, vec![HistoryEntry::Discard { value: y0.clone() }]),
                component(1, vec![HistoryEntry::Discard { value: y1.clone() }]),
            ],
        };
        let terminals = vec![
            KernelTerminalInput {
                quantum: vec![y0],
                classical: Vec::new(),
            },
            KernelTerminalInput {
                quantum: vec![y1],
                classical: Vec::new(),
            },
        ];

        let kernel = build_kernel(&KernelInput::new(&hps, Vec::new(), terminals)).unwrap();

        // Two coherent amplitude summands produce all four ordered terms in
        // |A><A|.  Pairwise/diagonal-only comparison would lose interference.
        assert_eq!(kernel.terms.len(), 4);
    }

    #[test]
    fn refuses_an_outer_product_beyond_the_preflight_budget() {
        let components = (0..257)
            .map(|_| component(0, Vec::new()))
            .collect::<Vec<_>>();
        let terminals = vec![KernelTerminalInput::default(); components.len()];
        let hps = HybridPathSum {
            input: HybridMemory::default(),
            components,
        };

        assert_eq!(
            build_kernel(&KernelInput::new(&hps, Vec::new(), terminals)),
            Err(KernelBuildError::ComponentPairBudget {
                components: 257,
                maximum_pairs: MAX_COMPONENT_PAIR_CANDIDATES,
            })
        );
    }
}
