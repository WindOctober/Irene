use std::collections::BTreeMap;
use std::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::ir::{NumericConstant, NumericExpr, NumericExprKind, SymbolId};

use super::{BooleanPolynomial, Monomial, Variable};

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

    fn is_zero(&self) -> bool {
        self.rational_turns == integer(0) && self.angle_terms.is_empty()
    }

    /// Multiplies both the rational and symbolic-angle parts by an exact value.
    /// For example, scaling `1/4 + θ/τ` by `-2` gives `1/2 - 2θ/τ`
    /// after reducing the rational part modulo one.
    fn scaled(&self, scale: BigRational) -> Self {
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
    fn add_assign(&mut self, other: Self) {
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

/// The phase `p` in the HPS amplitude `exp(2πi p)`.
///
/// Rational parts are stored modulo one because adding an integer does not
/// change the complex phase. Monomials retain the Boolean relation `x² = x`.
/// For example, T on a wire containing `x` adds `x/8`, while Z adds `x/2`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct PhasePolynomial {
    terms: BTreeMap<Monomial, PhaseCoefficient>,
}

impl PhasePolynomial {
    pub fn zero() -> Self {
        Self::default()
    }

    /// Iterates over the non-zero phase terms in canonical order.
    pub fn terms(&self) -> impl Iterator<Item = (&Monomial, &PhaseCoefficient)> {
        self.terms.iter()
    }

    /// Returns the coefficient of a monomial, or zero when it is absent.
    pub fn coefficient(&self, monomial: &Monomial) -> PhaseCoefficient {
        self.terms.get(monomial).cloned().unwrap_or_default()
    }

    pub(crate) fn add_boolean(
        &mut self,
        polynomial: &BooleanPolynomial,
        coefficient: PhaseCoefficient,
    ) {
        // XOR is not ordinary integer addition. Lift the Boolean polynomial
        // before scaling it as a phase expression.
        for (monomial, lifted_coefficient) in lift_boolean(polynomial) {
            self.add_term(monomial, coefficient.scaled(lifted_coefficient));
        }
    }

    /// Substitutes a Boolean variable throughout the arithmetic phase.
    ///
    /// Boolean expressions are lifted before being reinserted. Thus replacing
    /// `y` by `1 ⊕ x` in the phase `y/2` yields `(1-x)/2`, rather than
    /// incorrectly treating XOR as ordinary addition.
    pub(crate) fn substitute(&mut self, variable: &Variable, replacement: &BooleanPolynomial) {
        let terms = std::mem::take(&mut self.terms);
        for (monomial, coefficient) in terms {
            let mut substituted = BooleanPolynomial::one();
            for current in monomial.variables() {
                let factor = if current == variable {
                    replacement.clone()
                } else {
                    BooleanPolynomial::variable(current.clone())
                };
                substituted = substituted.and(&factor);
            }
            self.add_boolean(&substituted, coefficient);
        }
    }

    /// Adds a coefficient to one phase monomial.
    /// For example, adding `x/8` twice leaves one `x` entry with coefficient `1/4`.
    fn add_term(&mut self, monomial: Monomial, coefficient: PhaseCoefficient) {
        let mut combined = self.terms.remove(&monomial).unwrap_or_default();
        combined.add_assign(coefficient);
        if !combined.is_zero() {
            self.terms.insert(monomial, combined);
        }
    }
}

/// An ordinary rational polynomial over idempotent Boolean variables.
type ArithmeticPolynomial = BTreeMap<Monomial, BigRational>;

/// Embeds an ANF Boolean expression into an arithmetic polynomial with the same
/// value on Boolean assignments.
///
/// For example, lifting `x ⊕ y` yields `x + y - 2xy`. Consequently, using
/// `x ⊕ y` as a T-gate phase adds `x/8 + y/8 - xy/4`; treating XOR as
/// ordinary addition would lose the final interaction term.
fn lift_boolean(polynomial: &BooleanPolynomial) -> ArithmeticPolynomial {
    let mut lifted = ArithmeticPolynomial::new();
    for term in polynomial.terms() {
        let term = BTreeMap::from([(term.clone(), integer(1))]);
        lifted = arithmetic_xor(lifted, term);
    }
    lifted
}

/// Combines two arithmetic encodings using the Boolean XOR identity.
/// For example, XORing `x` and `y` produces `x + y - 2xy`.
fn arithmetic_xor(left: ArithmeticPolynomial, right: ArithmeticPolynomial) -> ArithmeticPolynomial {
    let product = arithmetic_product(&left, &right);
    let mut result = left;
    add_arithmetic(&mut result, right, integer(1));
    add_arithmetic(&mut result, product, integer(-2));
    result
}

/// Multiplies two arithmetic polynomials with `x² = x` for Boolean variables.
/// For example, `x * (x + y)` produces `x + xy`.
fn arithmetic_product(
    left: &ArithmeticPolynomial,
    right: &ArithmeticPolynomial,
) -> ArithmeticPolynomial {
    let mut result = ArithmeticPolynomial::new();
    for (left_term, left_coefficient) in left {
        for (right_term, right_coefficient) in right {
            let term = left_term.multiply(right_term);
            *result.entry(term).or_insert_with(|| integer(0)) +=
                left_coefficient * right_coefficient;
        }
    }
    result.retain(|_, coefficient| coefficient != &integer(0));
    result
}

/// Adds a scaled polynomial into an accumulator and removes zero terms.
/// For example, adding `-2 * (xy)` to `x + y` produces `x + y - 2xy`.
fn add_arithmetic(
    target: &mut ArithmeticPolynomial,
    source: ArithmeticPolynomial,
    scale: BigRational,
) {
    for (term, coefficient) in source {
        *target.entry(term).or_insert_with(|| integer(0)) += coefficient * &scale;
    }
    target.retain(|_, coefficient| coefficient != &integer(0));
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
        if self.terms.is_empty() {
            return formatter.write_str("0");
        }
        for (index, (term, coefficient)) in self.terms.iter().enumerate() {
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
