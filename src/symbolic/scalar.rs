use std::collections::BTreeMap;
use std::fmt;

use num_bigint::BigInt;
use num_rational::BigRational;
use rug::Float;
use rug::float::Constant;
use thiserror::Error;

use crate::ir::{NumericConstant, NumericExpr, SymbolId};

use super::{BooleanPolynomial, Variable};

/// A real scalar multiplying one hybrid path-sum component.
///
/// The complex part of an amplitude remains in the HPS phase. For example,
/// `Rx(θ)` uses `sin(θ/2)` as a scalar and the phase `-1/4` to represent
/// `-i sin(θ/2)` on paths where the target bit flips.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Scalar {
    /// An exact rational number.
    Rational(BigRational),
    /// A square root retained symbolically.
    Sqrt(Box<Scalar>),
    /// Sine of an angle in radians.
    Sin(NumericExpr),
    /// Cosine of an angle in radians.
    Cos(NumericExpr),
    /// Sum of two scalar expressions.
    Add(Box<Scalar>, Box<Scalar>),
    /// Product of two scalar expressions.
    Mul(Box<Scalar>, Box<Scalar>),
    /// Additive inverse.
    Neg(Box<Scalar>),
    /// Multiplicative inverse.
    Inverse(Box<Scalar>),
    /// Chooses a scalar according to a Boolean input or path expression.
    ///
    /// For example, `select(x ⊕ y, sin(θ/2), cos(θ/2))` is the magnitude of a
    /// rotation path: sine when the output bit changes and cosine otherwise.
    Select {
        condition: BooleanPolynomial,
        when_true: Box<Scalar>,
        when_false: Box<Scalar>,
    },
}

impl Scalar {
    pub fn zero() -> Self {
        Self::rational(rational(0, 1))
    }

    pub fn one() -> Self {
        Self::rational(rational(1, 1))
    }

    pub fn rational(value: BigRational) -> Self {
        Self::Rational(value)
    }

    pub fn sqrt(value: Self) -> Self {
        match value {
            Self::Rational(value) if value == rational(0, 1) => Self::zero(),
            Self::Rational(value) if value == rational(1, 1) => Self::one(),
            value => Self::Sqrt(Box::new(value)),
        }
    }

    pub fn sin(angle: NumericExpr) -> Self {
        if numeric_zero(&angle) {
            Self::zero()
        } else {
            Self::Sin(angle)
        }
    }

    pub fn cos(angle: NumericExpr) -> Self {
        if numeric_zero(&angle) {
            Self::one()
        } else {
            Self::Cos(angle)
        }
    }

    pub fn sum(self, other: Self) -> Self {
        match (self, other) {
            (Self::Rational(left), Self::Rational(right)) => Self::Rational(left + right),
            (Self::Rational(value), other) if value == rational(0, 1) => other,
            (left, Self::Rational(value)) if value == rational(0, 1) => left,
            (left, right) => Self::Add(Box::new(left), Box::new(right)),
        }
    }

    pub fn multiply(self, other: Self) -> Self {
        match (self, other) {
            (Self::Rational(left), Self::Rational(right)) => Self::Rational(left * right),
            (Self::Rational(value), _) | (_, Self::Rational(value)) if value == rational(0, 1) => {
                Self::zero()
            }
            (Self::Rational(value), other) if value == rational(1, 1) => other,
            (left, Self::Rational(value)) if value == rational(1, 1) => left,
            (left, right) => Self::Mul(Box::new(left), Box::new(right)),
        }
    }

    pub fn negate(self) -> Self {
        match self {
            Self::Rational(value) => Self::Rational(-value),
            Self::Neg(value) => *value,
            value => Self::Neg(Box::new(value)),
        }
    }

    pub fn inverse(self) -> Self {
        match self {
            Self::Rational(value) if value != rational(0, 1) => Self::Rational(value.recip()),
            Self::Inverse(value) => *value,
            value => Self::Inverse(Box::new(value)),
        }
    }

    pub fn select(condition: BooleanPolynomial, when_true: Self, when_false: Self) -> Self {
        if condition.is_zero() {
            when_false
        } else if condition.is_one() || when_true == when_false {
            when_true
        } else {
            Self::Select {
                condition,
                when_true: Box::new(when_true),
                when_false: Box::new(when_false),
            }
        }
    }

    /// Substitutes a Boolean input or path variable in scalar conditions.
    ///
    /// For example, replacing `y` by `0` reduces
    /// `select(y, sin(θ/2), cos(θ/2))` to `cos(θ/2)`.
    pub(crate) fn substitute(&self, variable: &Variable, replacement: &BooleanPolynomial) -> Self {
        match self {
            Self::Rational(_) | Self::Sin(_) | Self::Cos(_) => self.clone(),
            Self::Sqrt(value) => Self::sqrt(value.substitute(variable, replacement)),
            Self::Add(left, right) => left
                .substitute(variable, replacement)
                .sum(right.substitute(variable, replacement)),
            Self::Mul(left, right) => left
                .substitute(variable, replacement)
                .multiply(right.substitute(variable, replacement)),
            Self::Neg(value) => value.substitute(variable, replacement).negate(),
            Self::Inverse(value) => value.substitute(variable, replacement).inverse(),
            Self::Select {
                condition,
                when_true,
                when_false,
            } => Self::select(
                condition.substitute(variable, replacement),
                when_true.substitute(variable, replacement),
                when_false.substitute(variable, replacement),
            ),
        }
    }

    /// Evaluates the symbolic scalar using MPFR at the requested bit precision.
    ///
    /// For example, evaluating `sin(theta / 2)` requires a numeric binding for
    /// `theta`; evaluating `select(y0, a, b)` additionally requires a Boolean
    /// binding for `y0`. This operation is for numerical inspection only:
    /// symbolic execution itself keeps the expression exact.
    pub fn evaluate(
        &self,
        precision: u32,
        bindings: &ScalarBindings,
    ) -> Result<Float, ScalarEvaluationError> {
        if precision < 2 {
            return Err(ScalarEvaluationError::InvalidPrecision(precision));
        }
        match self {
            Self::Rational(value) => Ok(rational_float(value, precision)),
            Self::Sqrt(value) => Ok(value.evaluate(precision, bindings)?.sqrt()),
            Self::Sin(angle) => Ok(evaluate_numeric(angle, precision, bindings)?.sin()),
            Self::Cos(angle) => Ok(evaluate_numeric(angle, precision, bindings)?.cos()),
            Self::Add(left, right) => {
                let mut value = left.evaluate(precision, bindings)?;
                value += right.evaluate(precision, bindings)?;
                Ok(value)
            }
            Self::Mul(left, right) => {
                let mut value = left.evaluate(precision, bindings)?;
                value *= right.evaluate(precision, bindings)?;
                Ok(value)
            }
            Self::Neg(value) => Ok(-value.evaluate(precision, bindings)?),
            Self::Inverse(value) => {
                let value = value.evaluate(precision, bindings)?;
                Ok(Float::with_val(precision, 1) / value)
            }
            Self::Select {
                condition,
                when_true,
                when_false,
            } => {
                if evaluate_boolean(condition, &bindings.booleans)? {
                    when_true.evaluate(precision, bindings)
                } else {
                    when_false.evaluate(precision, bindings)
                }
            }
        }
    }
}

/// Concrete values used only when a symbolic scalar is numerically inspected.
#[derive(Debug, Clone, Default)]
pub struct ScalarBindings {
    pub booleans: BTreeMap<Variable, bool>,
    pub numeric_inputs: BTreeMap<SymbolId, Float>,
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum ScalarEvaluationError {
    #[error("precision must be at least two bits, found {0}")]
    InvalidPrecision(u32),
    #[error("missing Boolean value for {0}")]
    MissingBoolean(Variable),
    #[error("missing numeric value for input{0}")]
    MissingNumericInput(usize),
}

/// Evaluates an ANF Boolean expression under one concrete path assignment.
fn evaluate_boolean(
    polynomial: &BooleanPolynomial,
    bindings: &BTreeMap<Variable, bool>,
) -> Result<bool, ScalarEvaluationError> {
    let mut value = false;
    for monomial in polynomial.terms() {
        let mut term = true;
        for variable in monomial.variables() {
            term &= bindings
                .get(variable)
                .copied()
                .ok_or_else(|| ScalarEvaluationError::MissingBoolean(variable.clone()))?;
        }
        value ^= term;
    }
    Ok(value)
}

/// Evaluates a source-preserving angle expression without first converting it
/// through an `f64`.
fn evaluate_numeric(
    expression: &NumericExpr,
    precision: u32,
    bindings: &ScalarBindings,
) -> Result<Float, ScalarEvaluationError> {
    match expression {
        NumericExpr::Rational(value) => Ok(rational_float(value, precision)),
        NumericExpr::Constant(NumericConstant::Pi) => Ok(Float::with_val(precision, Constant::Pi)),
        NumericExpr::Constant(NumericConstant::Tau) => {
            let mut value = Float::with_val(precision, Constant::Pi);
            value *= 2;
            Ok(value)
        }
        NumericExpr::Constant(NumericConstant::Euler) => Ok(Float::with_val(precision, 1).exp()),
        NumericExpr::Input(id) => bindings
            .numeric_inputs
            .get(id)
            .map(|value| Float::with_val(precision, value))
            .ok_or(ScalarEvaluationError::MissingNumericInput(id.0)),
        NumericExpr::Neg(value) => Ok(-evaluate_numeric(value, precision, bindings)?),
        NumericExpr::Add(left, right) => {
            let mut value = evaluate_numeric(left, precision, bindings)?;
            value += evaluate_numeric(right, precision, bindings)?;
            Ok(value)
        }
        NumericExpr::Sub(left, right) => {
            let mut value = evaluate_numeric(left, precision, bindings)?;
            value -= evaluate_numeric(right, precision, bindings)?;
            Ok(value)
        }
        NumericExpr::Mul(left, right) => {
            let mut value = evaluate_numeric(left, precision, bindings)?;
            value *= evaluate_numeric(right, precision, bindings)?;
            Ok(value)
        }
        NumericExpr::Div(left, right) => {
            let mut value = evaluate_numeric(left, precision, bindings)?;
            value /= evaluate_numeric(right, precision, bindings)?;
            Ok(value)
        }
    }
}

/// Rounds an exact rational directly into an MPFR value at `precision` bits.
fn rational_float(value: &BigRational, precision: u32) -> Float {
    let numerator = Float::with_val(
        precision,
        Float::parse(value.numer().to_string()).expect("BigInt has a valid decimal form"),
    );
    let denominator = Float::with_val(
        precision,
        Float::parse(value.denom().to_string()).expect("BigInt has a valid decimal form"),
    );
    numerator / denominator
}

fn numeric_zero(expression: &NumericExpr) -> bool {
    matches!(expression, NumericExpr::Rational(value) if value == &rational(0, 1))
}

fn rational(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

impl fmt::Display for Scalar {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Rational(value) => write!(formatter, "{value}"),
            Self::Sqrt(value) => write!(formatter, "sqrt({value})"),
            Self::Sin(angle) => write!(formatter, "sin({angle})"),
            Self::Cos(angle) => write!(formatter, "cos({angle})"),
            Self::Add(left, right) => write!(formatter, "({left} + {right})"),
            Self::Mul(left, right) => write!(formatter, "({left} * {right})"),
            Self::Neg(value) => write!(formatter, "-({value})"),
            Self::Inverse(value) => write!(formatter, "1/({value})"),
            Self::Select {
                condition,
                when_true,
                when_false,
            } => write!(
                formatter,
                "if {condition} then {when_true} else {when_false}"
            ),
        }
    }
}
