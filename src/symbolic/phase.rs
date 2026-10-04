use std::collections::BTreeMap;
use std::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::ir::{NumericConstant, NumericExpr, NumericExprKind, SymbolId};

use super::{BooleanPolynomial, Monomial, Variable};

#[cfg(test)]
mod rewrite_tests;

/// One basis element in a normalized symbolic angle.
///
/// Linear expressions use dedicated atoms, so `theta / 2 + theta / 2`
/// becomes one `Input(theta)` term. Products and symbolic denominators remain
/// exact normalized expressions instead of being approximated.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum AngleBasis {
    /// One radian. Thus the source literal `0.1` contributes `1/10 · rad / τ`.
    Radian,
    /// Euler's number as an exact named constant.
    Euler,
    /// One symbolic numeric input.
    Input(SymbolId),
    /// An expression outside the supported linear fragment.
    Nonlinear(NumericForm),
}

/// ID-free canonical syntax for a nonlinear numeric angle expression.
///
/// Addition and multiplication are flattened and sorted, subtraction becomes
/// addition of a negative term, and division becomes multiplication by an
/// inverse. This proves common syntactic algebraic equalities without making
/// assumptions such as algebraic independence of `π`, `ℇ`, and inputs.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
enum NumericForm {
    Rational(BigRational),
    Constant(NumericConstant),
    Input(SymbolId),
    Add(Vec<NumericForm>),
    Mul(Vec<NumericForm>),
    Inverse(Box<NumericForm>),
}

/// One coefficient in an HPS phase polynomial, measured in turns.
///
/// It represents `rational + Σ scale * angle / τ`. Finite decimals inside
/// angle expressions are exact rationals, while constants such as `π` and
/// symbolic inputs retain their expression structure.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct PhaseCoefficient {
    /// Exact phase already expressed in turns, where one turn is `2π`.
    rational_turns: BigRational,
    /// Canonical angle atoms and their exact multipliers in
    /// `multiplier * basis / τ`.
    angle_terms: BTreeMap<AngleBasis, BigRational>,
}

impl PhaseCoefficient {
    pub fn rational(value: BigRational) -> Self {
        Self {
            rational_turns: modulo_one(value),
            angle_terms: BTreeMap::new(),
        }
    }

    pub fn angle(angle: NumericExpr, scale: BigRational) -> Self {
        let mut result = Self {
            rational_turns: integer(0),
            angle_terms: BTreeMap::new(),
        };
        result.add_angle(&angle, scale);
        result.rational_turns = modulo_one(result.rational_turns);
        result
    }

    pub fn rational_part(&self) -> BigRational {
        self.rational_turns.clone()
    }

    /// Constant linear phase only: exact turns plus exact rational radians.
    /// Numeric inputs and other symbolic atoms are deliberately not approximated.
    pub(crate) fn constant_turns_radians(&self) -> Option<(BigRational, BigRational)> {
        let mut radians = integer(0);
        for (basis, coefficient) in &self.angle_terms {
            if !matches!(basis, AngleBasis::Radian) {
                return None;
            }
            radians += coefficient;
        }
        Some((self.rational_turns.clone(), radians))
    }

    /// Returns the exact coefficient when it contains no symbolic angle atom.
    pub(crate) fn as_rational(&self) -> Option<BigRational> {
        self.angle_terms
            .is_empty()
            .then(|| self.rational_turns.clone())
    }

    /// Decomposes the linear angle fragment into canonical basis coefficients.
    ///
    /// For example, `(theta + pi) / 2` becomes
    /// `1/4 turn + 1/2 · Input(theta) / τ`. A product such as `theta * phi`
    /// becomes one [`AngleBasis::Nonlinear`] term.
    fn add_angle(&mut self, angle: &NumericExpr, scale: BigRational) {
        if scale == integer(0) {
            return;
        }
        match &angle.kind {
            NumericExprKind::Rational(value) => {
                self.add_basis(AngleBasis::Radian, scale * value);
            }
            NumericExprKind::Constant(NumericConstant::Pi) => {
                self.rational_turns += scale * ratio(1, 2);
            }
            NumericExprKind::Constant(NumericConstant::Tau) => {
                self.rational_turns += scale;
            }
            NumericExprKind::Constant(NumericConstant::Euler) => {
                self.add_basis(AngleBasis::Euler, scale);
            }
            NumericExprKind::Input(id) => {
                self.add_basis(AngleBasis::Input(*id), scale);
            }
            NumericExprKind::Neg(inner) => self.add_angle(inner, -scale),
            NumericExprKind::Add(left, right) => {
                self.add_angle(left, scale.clone());
                self.add_angle(right, scale);
            }
            NumericExprKind::Sub(left, right) => {
                self.add_angle(left, scale.clone());
                self.add_angle(right, -scale);
            }
            NumericExprKind::Mul(left, right) => {
                if let Some(value) = exact_rational(left) {
                    self.add_angle(right, scale * value);
                } else if let Some(value) = exact_rational(right) {
                    self.add_angle(left, scale * value);
                } else {
                    self.add_basis(AngleBasis::Nonlinear(NumericForm::from(angle)), scale);
                }
            }
            NumericExprKind::Div(numerator, denominator) => {
                if let Some(value) =
                    exact_rational(denominator).filter(|value| value != &integer(0))
                {
                    self.add_angle(numerator, scale / value);
                } else {
                    self.add_basis(AngleBasis::Nonlinear(NumericForm::from(angle)), scale);
                }
            }
        }
    }

    fn add_basis(&mut self, basis: AngleBasis, coefficient: BigRational) {
        let coefficient = self
            .angle_terms
            .remove(&basis)
            .unwrap_or_else(|| integer(0))
            + coefficient;
        if coefficient != integer(0) {
            self.angle_terms.insert(basis, coefficient);
        }
    }

    pub(crate) fn is_zero(&self) -> bool {
        self.rational_turns == integer(0) && self.angle_terms.is_empty()
    }

    /// Multiplies both the rational and symbolic-angle parts by an exact integer.
    /// For example, scaling `1/4 + θ/τ` by `-2` gives `1/2 - 2θ/τ`
    /// after reducing the rational part modulo one.
    /// Fractional scaling is not well-defined after reduction modulo one:
    /// representatives 0 and 1 agree as phases, but their halves do not.
    pub(crate) fn scaled(&self, scale: BigInt) -> Self {
        let scale = BigRational::from_integer(scale);
        let rational_turns = modulo_one(self.rational_turns.clone() * scale.clone());
        let angle_terms = self
            .angle_terms
            .iter()
            .filter_map(|(angle, coefficient)| {
                let coefficient = coefficient * &scale;
                (coefficient != integer(0)).then(|| (angle.clone(), coefficient))
            })
            .collect();
        Self {
            rational_turns,
            angle_terms,
        }
    }

    /// Adds another coefficient and merges occurrences of the same angle expression.
    /// For example, `θ/τ + θ/τ` is stored as the single term `2θ/τ`.
    pub(crate) fn add_assign(&mut self, other: Self) {
        self.rational_turns = modulo_one(self.rational_turns.clone() + other.rational_turns);
        for (angle, coefficient) in other.angle_terms {
            let coefficient = self
                .angle_terms
                .remove(&angle)
                .unwrap_or_else(|| integer(0))
                + coefficient;
            if coefficient != integer(0) {
                self.angle_terms.insert(angle, coefficient);
            }
        }
    }
}

impl From<&NumericExpr> for NumericForm {
    fn from(expression: &NumericExpr) -> Self {
        match &expression.kind {
            NumericExprKind::Rational(value) => Self::Rational(value.clone()),
            NumericExprKind::Constant(NumericConstant::Tau) => normalize_mul(vec![
                Self::Rational(integer(2)),
                Self::Constant(NumericConstant::Pi),
            ]),
            NumericExprKind::Constant(constant) => Self::Constant(*constant),
            NumericExprKind::Input(id) => Self::Input(*id),
            NumericExprKind::Neg(inner) => normalize_mul(vec![
                Self::Rational(integer(-1)),
                Self::from(inner.as_ref()),
            ]),
            NumericExprKind::Add(left, right) => {
                normalize_add(vec![Self::from(left.as_ref()), Self::from(right.as_ref())])
            }
            NumericExprKind::Sub(left, right) => normalize_add(vec![
                Self::from(left.as_ref()),
                normalize_mul(vec![
                    Self::Rational(integer(-1)),
                    Self::from(right.as_ref()),
                ]),
            ]),
            NumericExprKind::Mul(left, right) => {
                normalize_mul(vec![Self::from(left.as_ref()), Self::from(right.as_ref())])
            }
            NumericExprKind::Div(left, right) => normalize_mul(vec![
                Self::from(left.as_ref()),
                normalize_inverse(Self::from(right.as_ref())),
            ]),
        }
    }
}

/// Evaluates the purely rational fragment used as a linear scale.
fn exact_rational(expression: &NumericExpr) -> Option<BigRational> {
    match &expression.kind {
        NumericExprKind::Rational(value) => Some(value.clone()),
        NumericExprKind::Neg(inner) => Some(-exact_rational(inner)?),
        NumericExprKind::Add(left, right) => Some(exact_rational(left)? + exact_rational(right)?),
        NumericExprKind::Sub(left, right) => Some(exact_rational(left)? - exact_rational(right)?),
        NumericExprKind::Mul(left, right) => Some(exact_rational(left)? * exact_rational(right)?),
        NumericExprKind::Div(left, right) => {
            let numerator = exact_rational(left)?;
            let denominator = exact_rational(right)?;
            (denominator != integer(0)).then(|| numerator / denominator)
        }
        NumericExprKind::Constant(_) | NumericExprKind::Input(_) => None,
    }
}

/// Canonicalizes a commutative sum by flattening, sorting, and combining
/// rational terms. For example, `x + (2 + 1)` becomes `3 + x`.
fn normalize_add(terms: Vec<NumericForm>) -> NumericForm {
    let mut flattened = Vec::new();
    let mut rational = integer(0);
    for term in terms {
        collect_addend(term, &mut flattened, &mut rational);
    }
    if rational != integer(0) {
        flattened.push(NumericForm::Rational(rational));
    }
    flattened.sort();
    match flattened.len() {
        0 => NumericForm::Rational(integer(0)),
        1 => flattened.pop().unwrap(),
        _ => NumericForm::Add(flattened),
    }
}

/// Flattens nested sums and accumulates their exact rational constant.
fn collect_addend(term: NumericForm, flattened: &mut Vec<NumericForm>, rational: &mut BigRational) {
    match term {
        NumericForm::Add(inner) => {
            for term in inner {
                collect_addend(term, flattened, rational);
            }
        }
        NumericForm::Rational(value) => *rational += value,
        term => flattened.push(term),
    }
}

/// Canonicalizes a commutative product by flattening, sorting, and multiplying
/// rational factors. For example, `2 * (x * 3)` becomes `6 * x`.
fn normalize_mul(factors: Vec<NumericForm>) -> NumericForm {
    let mut flattened = Vec::new();
    let mut rational = integer(1);
    for factor in factors {
        collect_factor(factor, &mut flattened, &mut rational);
    }
    if rational == integer(0) {
        return NumericForm::Rational(integer(0));
    }
    if rational != integer(1) {
        flattened.push(NumericForm::Rational(rational));
    }
    flattened.sort();
    match flattened.len() {
        0 => NumericForm::Rational(integer(1)),
        1 => flattened.pop().unwrap(),
        _ => NumericForm::Mul(flattened),
    }
}

/// Flattens nested products and accumulates their exact rational factor.
fn collect_factor(
    factor: NumericForm,
    flattened: &mut Vec<NumericForm>,
    rational: &mut BigRational,
) {
    match factor {
        NumericForm::Mul(inner) => {
            for factor in inner {
                collect_factor(factor, flattened, rational);
            }
        }
        NumericForm::Rational(value) => *rational *= value,
        factor => flattened.push(factor),
    }
}

/// Reduces exact rational and double inverses while retaining symbolic ones.
/// For example, `1/(1/x)` becomes `x`.
fn normalize_inverse(value: NumericForm) -> NumericForm {
    match value {
        NumericForm::Rational(value) if value != integer(0) => NumericForm::Rational(value.recip()),
        NumericForm::Inverse(inner) => *inner,
        value => NumericForm::Inverse(Box::new(value)),
    }
}

/// Exact phase as weighted XAG selectors. Boolean functions remain graph
/// values; there is no persistent monomial table or eager ANF lifting.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct PhasePolynomial {
    selectors: BTreeMap<BooleanPolynomial, PhaseCoefficient>,
}
impl PhasePolynomial {
    pub fn zero() -> Self {
        Self::default()
    }
    #[cfg(test)]
    pub fn terms(&self) -> impl Iterator<Item = (Monomial, PhaseCoefficient)> {
        self.expanded_terms(65536)
            .expect("test phase view exceeded budget")
            .into_iter()
    }
    #[cfg(test)]
    pub fn coefficient(&self, m: &Monomial) -> PhaseCoefficient {
        self.expanded_terms(65536)
            .expect("test phase view exceeded budget")
            .get(m)
            .cloned()
            .unwrap_or_default()
    }
    pub fn selectors(&self) -> impl Iterator<Item = (BooleanPolynomial, &PhaseCoefficient)> {
        self.selectors.iter().map(|(p, c)| (p.clone(), c))
    }
    pub fn storage_size(&self) -> usize {
        self.selectors
            .keys()
            .map(BooleanPolynomial::storage_size)
            .sum()
    }
    pub(crate) fn variables(&self) -> std::collections::BTreeSet<Variable> {
        self.selectors
            .keys()
            .flat_map(BooleanPolynomial::variables)
            .collect()
    }
    /// Subtract the phase at the all-zero assignment. This removes only a
    /// constant and is valid at a density boundary, never for coherent merging.
    pub(crate) fn remove_global_phase(&mut self) {
        let mut constant = PhaseCoefficient::default();
        for (p, c) in &self.selectors {
            if p.evaluate::<std::convert::Infallible>(|_| Ok(false))
                .unwrap()
            {
                constant.add_assign(c.clone());
            }
        }
        self.add_boolean(&BooleanPolynomial::one(), constant.scaled(BigInt::from(-1)));
    }
    pub(crate) fn add_boolean(&mut self, p: &BooleanPolynomial, c: PhaseCoefficient) {
        if p.is_zero() || c.is_zero() {
            return;
        }
        // Local weighted-XAG rewrite, not an ANF conversion: each fanin is an
        // arbitrary shared function. c*(a XOR b)=ca+cb-2c(a AND b).
        // This exposes phase cancellations in Clifford+T decompositions while
        // leaving larger parity arithmetic compact. Only this explicitly
        // expanding rewrite is bounded by a fanin limit (at most 255 subsets).
        if c.as_rational() != Some(ratio(1, 2))
            && let fanins = p.xor_terms()
            && fanins.len() <= 8
            && fanins.len() > 1
        {
            let mut lifted = BTreeMap::<BooleanPolynomial, PhaseCoefficient>::new();
            for term in fanins {
                let products: Vec<_> = lifted
                    .iter()
                    .map(|(value, coefficient)| (value.and(&term), coefficient.scaled((-2).into())))
                    .collect();
                for (value, coefficient) in std::iter::once((term, c.clone())).chain(products) {
                    if value.is_zero() || coefficient.is_zero() {
                        continue;
                    }
                    let mut coefficient_sum = lifted.remove(&value).unwrap_or_default();
                    coefficient_sum.add_assign(coefficient);
                    if !coefficient_sum.is_zero() {
                        lifted.insert(value, coefficient_sum);
                    }
                }
            }
            for (value, coefficient) in lifted {
                self.add_boolean(&value, coefficient);
            }
            return;
        }
        // Half-turn arithmetic is exactly Boolean XOR. Combine the parity
        // graph and factor shared children, retaining AND subgraphs unexpanded.
        if c.as_rational() == Some(ratio(1, 2)) {
            let mut parity = p.clone();
            let keys: Vec<_> = self
                .selectors
                .iter()
                .filter(|(_, c)| c.as_rational() == Some(ratio(1, 2)))
                .map(|(p, _)| p.clone())
                .collect();
            for key in keys {
                self.selectors.remove(&key);
                parity = parity.xor(&key);
            }
            if !parity.is_zero() {
                self.add_selector(parity.factored(), c);
            }
        } else {
            self.add_selector(p.clone(), c);
        }
    }
    /// Add selected half-turns, touching only the existing half-turn
    /// selectors and a possible collision at the new parity key. This is the
    /// same strict storage-size test as cloning the whole phase per candidate.
    /// The caller must prove each added phase is irrelevant at its boundary
    /// (for example, a common function of traced-out history). Arbitrary
    /// candidates do not preserve the phase or a coherent sum of components.
    pub(crate) fn shorten_half_turns(
        &mut self,
        values: impl IntoIterator<Item = BooleanPolynomial>,
    ) {
        let half = PhaseCoefficient::rational(ratio(1, 2));
        let mut keys = self
            .selectors
            .iter()
            .filter(|(_, c)| **c == half)
            .map(|(p, _)| p.clone())
            .collect::<std::collections::BTreeSet<_>>();
        let mut old_size: usize = keys.iter().map(BooleanPolynomial::storage_size).sum();
        for value in values {
            // Without a half-turn selector, adding a half-turn cannot remove
            // an existing selector or strictly reduce the representation.
            if keys.is_empty() {
                break;
            }
            if value.is_zero() {
                continue;
            }
            let parity =
                BooleanPolynomial::xor_all(std::iter::once(value).chain(keys.iter().cloned()))
                    .factored();
            let mut combined = half.clone();
            let mut before = old_size;
            if !keys.contains(&parity)
                && let Some(existing) = self.selectors.get(&parity)
            {
                before += parity.storage_size();
                combined.add_assign(existing.clone());
            }
            let after = if parity.is_zero() || combined.is_zero() {
                0
            } else {
                parity.storage_size()
            };
            if after >= before {
                continue;
            }
            for key in &keys {
                self.selectors.remove(key);
            }
            keys.clear();
            old_size = 0;
            if !parity.is_zero() {
                self.selectors.remove(&parity);
                if !combined.is_zero() {
                    if combined == half {
                        keys.insert(parity.clone());
                        old_size = after;
                    }
                    self.selectors.insert(parity, combined);
                }
            }
        }
    }

    fn add_selector(&mut self, p: BooleanPolynomial, c: PhaseCoefficient) {
        if p.is_zero() || c.is_zero() {
            return;
        }
        let mut combined = self.selectors.remove(&p).unwrap_or_default();
        combined.add_assign(c);
        if !combined.is_zero() {
            self.selectors.insert(p, combined);
        }
    }
    pub(crate) fn substitute(&mut self, v: &Variable, replacement: &BooleanPolynomial) {
        self.map_variables(|w| {
            if w == v {
                replacement.clone()
            } else {
                BooleanPolynomial::variable(w.clone())
            }
        });
    }
    /// Rebuild the entire phase with one shared simultaneous Boolean map.
    /// Coefficients are retained and colliding selectors merge exactly.
    pub(crate) fn map_variables(&mut self, f: impl FnMut(&Variable) -> BooleanPolynomial) {
        let old = std::mem::take(self);
        let (roots, coefficients): (Vec<_>, Vec<_>) = old.selectors.into_iter().unzip();
        for (p, c) in BooleanPolynomial::map_roots(&roots, f)
            .into_iter()
            .zip(coefficients)
        {
            self.add_boolean(&p, c);
        }
    }
    /// Temporary arithmetic-polynomial view for kernel algebra. Failure does
    /// not alter the graph or truncate terms. XOR lifting is ordinary integer
    /// arithmetic a XOR b = a+b-2ab, not Boolean addition for general phases.
    pub fn expanded_terms(&self, limit: usize) -> Option<BTreeMap<Monomial, PhaseCoefficient>> {
        fn add(out: &mut BTreeMap<Monomial, PhaseCoefficient>, m: Monomial, c: PhaseCoefficient) {
            let mut combined = out.remove(&m).unwrap_or_default();
            combined.add_assign(c);
            if !combined.is_zero() {
                out.insert(m, combined);
            }
        }
        let mut result = BTreeMap::new();
        let mut work = limit.saturating_mul(64);
        for (p, c) in &self.selectors {
            let terms = p.expanded_terms(limit)?;
            work = work.checked_sub(terms.len())?;
            let mut lifted = BTreeMap::<Monomial, PhaseCoefficient>::new();
            if c.as_rational() == Some(ratio(1, 2)) {
                lifted.extend(terms.into_iter().map(|m| (m, c.clone())));
            } else {
                for term in terms {
                    let mut products = Vec::new();
                    for (m, coefficient) in &lifted {
                        work = work.checked_sub(1)?;
                        let coefficient = coefficient.scaled(BigInt::from(-2));
                        if !coefficient.is_zero() {
                            products.push((m.multiply(&term), coefficient));
                        }
                    }
                    add(&mut lifted, term, c.clone());
                    for (m, c) in products {
                        add(&mut lifted, m, c);
                        if lifted.len() > limit {
                            return None;
                        }
                    }
                    if lifted.len() > limit {
                        return None;
                    }
                }
            }
            for (m, c) in lifted {
                add(&mut result, m, c);
                if result.len() > limit {
                    return None;
                }
            }
        }
        Some(result)
    }
}

/// Chooses the canonical representative in `[0, 1)` for a phase coefficient.
/// For example, `5/4` becomes `1/4` and `-1/4` becomes `3/4`.
fn modulo_one(value: BigRational) -> BigRational {
    let denominator = value.denom().clone();
    let mut numerator = value.numer() % &denominator;
    if numerator < BigInt::from(0) {
        numerator += &denominator;
    }
    BigRational::new(numerator, denominator)
}

/// Constructs a `BigRational` integer without repeating BigInt conversions.
fn integer(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn ratio(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

impl fmt::Display for AngleBasis {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Radian => formatter.write_str("rad"),
            Self::Euler => formatter.write_str("ℇ"),
            Self::Input(id) => write!(formatter, "input{}", id.0),
            Self::Nonlinear(expression) => write!(formatter, "{expression}"),
        }
    }
}

impl fmt::Display for NumericForm {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Rational(value) => write!(formatter, "{value}"),
            Self::Constant(NumericConstant::Pi) => formatter.write_str("π"),
            Self::Constant(NumericConstant::Tau) => formatter.write_str("τ"),
            Self::Constant(NumericConstant::Euler) => formatter.write_str("ℇ"),
            Self::Input(id) => write!(formatter, "input{}", id.0),
            Self::Add(terms) => display_joined(formatter, terms, " + "),
            Self::Mul(factors) => display_joined(formatter, factors, " · "),
            Self::Inverse(value) => write!(formatter, "1/({value})"),
        }
    }
}

fn display_joined(
    formatter: &mut fmt::Formatter<'_>,
    values: &[NumericForm],
    separator: &str,
) -> fmt::Result {
    formatter.write_str("(")?;
    for (index, value) in values.iter().enumerate() {
        if index > 0 {
            formatter.write_str(separator)?;
        }
        write!(formatter, "{value}")?;
    }
    formatter.write_str(")")
}

impl fmt::Display for PhasePolynomial {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.selectors.is_empty() {
            return formatter.write_str("0");
        }
        for (index, (term, coefficient)) in self.selectors().enumerate() {
            if index > 0 {
                formatter.write_str(" + ")?;
            }
            write!(formatter, "{coefficient}·{term}")?;
        }
        Ok(())
    }
}

impl fmt::Display for PhaseCoefficient {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut wrote_term = false;
        if self.rational_turns != integer(0) {
            write!(formatter, "{}", self.rational_turns)?;
            wrote_term = true;
        }
        for (angle, scale) in &self.angle_terms {
            if wrote_term {
                formatter.write_str(" + ")?;
            }
            write!(formatter, "{scale}·({angle})/τ")?;
            wrote_term = true;
        }
        if !wrote_term {
            formatter.write_str("0")?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod sparse_half_turn_tests {
    use super::*;

    #[test]
    fn shared_phase_substitution_matches_independent_roots_and_merges_collisions() {
        let v = |i| BooleanPolynomial::variable(Variable::Path(i));
        let shared = v(0).and(&v(1).xor(&v(2)));
        let mut original = PhasePolynomial::zero();
        for (p, numerator) in [
            (shared.clone(), 1),
            (shared.xor(&v(3)), 3),
            (v(1), 7),
            (v(2), 5),
        ] {
            original.add_boolean(&p, PhaseCoefficient::rational(ratio(numerator, 8)));
        }
        for replacement in [
            v(2),
            v(1).xor(&v(3)),
            BooleanPolynomial::zero(),
            BooleanPolynomial::one(),
        ] {
            let mut expected = PhasePolynomial::zero();
            for (p, c) in original.selectors() {
                expected.add_boolean(&p.substitute(&Variable::Path(1), &replacement), c.clone());
            }
            let mut actual = original.clone();
            actual.substitute(&Variable::Path(1), &replacement);
            assert_eq!(actual, expected);
        }
    }

    #[test]
    fn sparse_updates_match_full_clone_trials_including_coefficient_collisions() {
        let variable = |i| BooleanPolynomial::variable(Variable::Path(i));
        let half = PhaseCoefficient::rational(ratio(1, 2));
        for seed in 0..48 {
            let mut original = PhasePolynomial::zero();
            for i in 0..20 {
                let p = variable(i % 6).and(&variable((i + seed) % 6));
                // Direct insertion covers multiple half-turn keys and a new
                // parity colliding with a non-half-turn coefficient.
                original.add_selector(
                    p,
                    PhaseCoefficient::rational(ratio((i + seed) as i64 % 7 + 1, 8)),
                );
            }
            let values = (0..6)
                .map(variable)
                .chain((0..6).flat_map(|i| (0..6).map(move |j| variable(i).and(&variable(j)))))
                .chain([BooleanPolynomial::zero(), variable(0).xor(&variable(1))])
                .collect::<Vec<_>>();
            let mut expected = original.clone();
            let mut actual = original.clone();
            for p in &values {
                let mut candidate = expected.clone();
                candidate.add_boolean(p, half.clone());
                if candidate.storage_size() < expected.storage_size() {
                    expected = candidate;
                }
                actual.shorten_half_turns([p.clone()]);
                assert_eq!(actual, expected, "seed={seed}, p={p}");
            }
            original.shorten_half_turns(values);
            assert_eq!(original, expected, "batch seed={seed}");
        }
    }
}
