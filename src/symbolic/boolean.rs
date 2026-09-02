use std::collections::BTreeSet;
use std::fmt;

use crate::ir::Qubit;

/// A Boolean variable occurring in an HPS input or output signature.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Variable {
    /// The computational-basis value carried by an input qubit.
    Input(Qubit),
    /// A fresh summation variable introduced by a path-splitting operation such as H.
    ///
    /// For example, applying H to a wire containing `x0` introduces `y0`,
    /// replaces the wire value with `y0`, and adds the phase `x0*y0/2`.
    Path(usize),
}

/// A conjunction of Boolean variables, such as `x0 * y1`.
///
/// The empty monomial is `1`. Variables are stored as a set because Boolean
/// multiplication is idempotent: `x * x = x`.
/// Thus multiplying `x0*y0` by `x0*y1` produces `x0*y0*y1`, not
/// `x0*x0*y0*y1`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Monomial(BTreeSet<Variable>);

impl Monomial {
    pub fn one() -> Self {
        Self::default()
    }

    pub fn variable(variable: Variable) -> Self {
        Self(BTreeSet::from([variable]))
    }

    pub fn variables(&self) -> impl Iterator<Item = &Variable> {
        self.0.iter()
    }

    /// Multiplies two monomials by taking the union of their variables.
    pub(crate) fn multiply(&self, other: &Self) -> Self {
        Self(self.0.union(&other.0).cloned().collect())
    }
}

/// A Boolean expression in algebraic normal form (ANF).
///
/// A polynomial is an XOR of monomials, for example `1 ⊕ x0 ⊕ x0*y1`.
/// This canonical form represents quantum-wire values, measurement outcomes,
/// classical conditions, and histories in the HPS.
///
/// For example, if a CX gate receives control `x0` and target `x1`, the target
/// becomes the polynomial `x1 ⊕ x0` while the control remains `x0`.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct BooleanPolynomial {
    terms: BTreeSet<Monomial>,
}

impl BooleanPolynomial {
    pub fn zero() -> Self {
        Self::default()
    }

    pub fn one() -> Self {
        Self {
            terms: BTreeSet::from([Monomial::one()]),
        }
    }

    pub fn variable(variable: Variable) -> Self {
        Self {
            terms: BTreeSet::from([Monomial::variable(variable)]),
        }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn is_one(&self) -> bool {
        self.terms.len() == 1 && self.terms.contains(&Monomial::one())
    }

    pub fn terms(&self) -> impl Iterator<Item = &Monomial> {
        self.terms.iter()
    }

    /// Adds two ANF polynomials over GF(2), cancelling duplicate monomials.
    /// For example, `(x ⊕ y) ⊕ y = x`.
    pub fn xor(&self, other: &Self) -> Self {
        let mut terms = self.terms.clone();
        for term in &other.terms {
            if !terms.insert(term.clone()) {
                terms.remove(term);
            }
        }
        Self { terms }
    }

    /// Multiplies two ANF polynomials using distributivity and Boolean idempotence.
    /// For example, `(1 ⊕ x) * y = y ⊕ x*y`.
    pub fn and(&self, other: &Self) -> Self {
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

    /// Computes Boolean negation using `not p = 1 ⊕ p`.
    pub fn complement(&self) -> Self {
        self.xor(&Self::one())
    }
}

impl From<bool> for BooleanPolynomial {
    fn from(value: bool) -> Self {
        if value { Self::one() } else { Self::zero() }
    }
}

impl fmt::Display for Variable {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Input(qubit) => write!(formatter, "x{}_{}", qubit.register.0, qubit.index),
            Self::Path(index) => write!(formatter, "y{index}"),
        }
    }
}

impl fmt::Display for Monomial {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return formatter.write_str("1");
        }
        for (index, variable) in self.0.iter().enumerate() {
            if index > 0 {
                formatter.write_str("·")?;
            }
            write!(formatter, "{variable}")?;
        }
        Ok(())
    }
}

impl fmt::Display for BooleanPolynomial {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.terms.is_empty() {
            return formatter.write_str("0");
        }
        for (index, term) in self.terms.iter().enumerate() {
            if index > 0 {
                formatter.write_str(" ⊕ ")?;
            }
            write!(formatter, "{term}")?;
        }
        Ok(())
    }
}
