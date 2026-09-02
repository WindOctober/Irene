use std::collections::BTreeMap;
use std::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::ir::NumericExpr;

use super::{BooleanPolynomial, Monomial};

/// One coefficient in an HPS phase polynomial, measured in turns.
///
/// It represents `rational + Σ scale * angle / τ`. Finite decimals inside
/// angle expressions are exact rationals, while constants such as `π` and
/// symbolic inputs retain their expression structure.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct PhaseCoefficient {
    /// Exact phase already expressed in turns, where one turn is `2π`.
    rational_turns: BigRational,
    /// Source-preserving angle expressions and their exact multipliers in
    /// `multiplier * angle / τ`.
    angle_terms: BTreeMap<NumericExpr, BigRational>,
}

impl PhaseCoefficient {
    pub fn rational(value: BigRational) -> Self {
        Self {
            rational_turns: modulo_one(value),
            angle_terms: BTreeMap::new(),
        }
    }

    pub fn angle(angle: NumericExpr, scale: BigRational) -> Self {
        let mut angle_terms = BTreeMap::new();
        if scale != integer(0) {
            angle_terms.insert(angle, scale);
        }
        Self {
            rational_turns: integer(0),
            angle_terms,
        }
    }

    pub fn rational_part(&self) -> BigRational {
        self.rational_turns.clone()
    }

    pub fn angle_terms(&self) -> impl Iterator<Item = (&NumericExpr, &BigRational)> {
        self.angle_terms.iter()
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

/// The phase `p` in the HPS amplitude `exp(2πi p)`.
///
/// Rational parts are stored modulo one because adding an integer does not
/// change the complex phase. Monomials retain the Boolean relation `x² = x`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
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
