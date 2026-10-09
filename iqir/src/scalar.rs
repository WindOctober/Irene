//! Typed finite-width scalar expressions, shared by constants and variables.
//!
//! Signed integer widths are 1..=64; unsigned words use the existing bit IR.
//! Signed overflow and integer division by zero must be diagnosed by a consumer,
//! never interpreted as mathematical unbounded arithmetic. Float operations
//! use IEEE binary32/binary64 at *each* node (not exact-real arithmetic).
//! The target profile uses round-to-nearest ties-to-even and gradual underflow.
//! Const qualification and source spelling belong to declarations, not types.
//! Constant evaluation uses these same expression nodes and arithmetic rules.
use crate::{AstId, AstIdGenerator, AstNode, SymbolId};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarType {
    Int { width: u32, signed: bool },
    Float { width: u32 },
}

impl ScalarType {
    pub fn width(self) -> u32 {
        match self {
            Self::Int { width, .. } | Self::Float { width, .. } => width,
        }
    }
    pub fn is_float(self) -> bool {
        matches!(self, Self::Float { .. })
    }

    pub fn contains_integer(self, value: i128) -> bool {
        match self {
            Self::Int {
                width: 1..=64,
                signed,
            } => {
                let width = self.width();
                if signed {
                    (-(1_i128 << (width - 1))..(1_i128 << (width - 1))).contains(&value)
                } else {
                    (0..(1_i128 << width)).contains(&value)
                }
            }
            _ => false,
        }
    }

    /// Shared by constant specialization and expression evaluation.
    pub fn checked_integer_arithmetic(
        self,
        op: ScalarArithmetic,
        a: i128,
        b: i128,
    ) -> Result<i128, &'static str> {
        use ScalarArithmetic as A;
        if !self.contains_integer(a) || !self.contains_integer(b) {
            return Err("integer operand outside its type");
        }
        if let Self::Int {
            width,
            signed: false,
        } = self
        {
            let (a, b) = (a as u128, b as u128);
            let value = match op {
                A::Add => a.wrapping_add(b),
                A::Sub => a.wrapping_sub(b),
                A::Mul => a.wrapping_mul(b),
                A::Div => a.checked_div(b).ok_or("zero divisor")?,
                A::Rem => a.checked_rem(b).ok_or("zero divisor")?,
            };
            return Ok((value & ((1u128 << width) - 1)) as i128);
        }
        if matches!(op, A::Div | A::Rem)
            && b == -1
            && matches!(self, Self::Int { signed: true, .. })
            && a == -(1_i128 << (self.width() - 1))
        {
            return Err("signed division overflow");
        }
        let result = match op {
            A::Add => a.checked_add(b),
            A::Sub => a.checked_sub(b),
            A::Mul => a.checked_mul(b),
            A::Div => a.checked_div(b),
            A::Rem => a.checked_rem(b),
        }
        .filter(|v| self.contains_integer(*v));
        result.ok_or("integer overflow or zero divisor")
    }
}

/// A known value is independent of whether its source binding is const.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarValue {
    Integer(i128),
    Float32(u32),
    Float64(u64),
}

impl ScalarValue {
    pub fn as_float(self) -> Option<f64> {
        match self {
            Self::Float32(bits) => Some(f64::from(f32::from_bits(bits))),
            Self::Float64(bits) => Some(f64::from_bits(bits)),
            Self::Integer(_) => None,
        }
    }

    pub fn expression(self) -> ScalarExprKind {
        match self {
            Self::Integer(value) => ScalarExprKind::Integer(value),
            Self::Float32(bits) => ScalarExprKind::Float32(bits),
            Self::Float64(bits) => ScalarExprKind::Float64(bits),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarArithmetic {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ScalarComparison {
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
}

impl ScalarComparison {
    pub fn compare(self, left: ScalarValue, right: ScalarValue) -> Option<bool> {
        use std::cmp::Ordering::{Equal, Greater, Less};
        let order = match (left, right) {
            (ScalarValue::Integer(a), ScalarValue::Integer(b)) => a.partial_cmp(&b),
            (a, b) => a.as_float()?.partial_cmp(&b.as_float()?),
        };
        Some(match self {
            Self::Eq => order == Some(Equal),
            Self::Ne => order != Some(Equal),
            Self::Lt => order == Some(Less),
            Self::Le => matches!(order, Some(Less | Equal)),
            Self::Gt => order == Some(Greater),
            Self::Ge => matches!(order, Some(Greater | Equal)),
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ScalarExprKind {
    /// Range-checked at import, with signedness and width supplied by `ty`.
    Integer(i128),
    /// IEEE encodings preserve signed zero and do not rely on f64 equality.
    Float32(u32),
    Float64(u64),
    Read(SymbolId),
    /// IEEE conversion between binary32/binary64. The destination is `ty`.
    FloatCast(Box<ScalarExpr>),
    Neg(Box<ScalarExpr>),
    Binary {
        op: ScalarArithmetic,
        left: Box<ScalarExpr>,
        right: Box<ScalarExpr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarExprData {
    pub ty: ScalarType,
    pub kind: ScalarExprKind,
}
pub type ScalarExpr = AstNode<ScalarExprData>;

impl ScalarExpr {
    /// Evaluate a closed expression. Unknown reads are not implicit zeroes.
    /// Nonfinite floating results follow IEEE; const declarations may reject
    /// them separately as part of the frontend's supported constant subset.
    pub fn constant_value(&self) -> Result<Option<ScalarValue>, &'static str> {
        use ScalarArithmetic as A;
        use ScalarExprKind as E;
        use ScalarValue as V;
        let value = match &self.kind.kind {
            E::Integer(v) => V::Integer(*v),
            E::Float32(v) => V::Float32(*v),
            E::Float64(v) => V::Float64(*v),
            E::Read(_) => return Ok(None),
            E::FloatCast(a) => {
                let Some(v) = a.constant_value()? else {
                    return Ok(None);
                };
                let v = v.as_float().ok_or("expected floating conversion operand")?;
                match self.ty {
                    ScalarType::Float { width: 32 } => V::Float32((v as f32).to_bits()),
                    ScalarType::Float { width: 64 } => V::Float64(v.to_bits()),
                    _ => return Err("unsupported float precision"),
                }
            }
            E::Neg(a) => {
                let Some(v) = a.constant_value()? else {
                    return Ok(None);
                };
                match v {
                    V::Integer(v) => {
                        V::Integer(self.ty.checked_integer_arithmetic(A::Sub, 0, v)?)
                    }
                    V::Float32(v) => V::Float32((-f32::from_bits(v)).to_bits()),
                    V::Float64(v) => V::Float64((-f64::from_bits(v)).to_bits()),
                }
            }
            E::Binary { op, left, right } => {
                let left = left.constant_value()?;
                let right = right.constant_value()?;
                let (Some(left), Some(right)) = (left, right) else {
                    return Ok(None);
                };
                match (left, right) {
                    (V::Integer(a), V::Integer(b)) => {
                        V::Integer(self.ty.checked_integer_arithmetic(*op, a, b)?)
                    }
                    (V::Float32(a), V::Float32(b)) => {
                        let (a, b) = (f32::from_bits(a), f32::from_bits(b));
                        V::Float32(
                            match op {
                                A::Add => a + b,
                                A::Sub => a - b,
                                A::Mul => a * b,
                                A::Div => a / b,
                                A::Rem => return Err("floating remainder is unsupported"),
                            }
                            .to_bits(),
                        )
                    }
                    (V::Float64(a), V::Float64(b)) => {
                        let (a, b) = (f64::from_bits(a), f64::from_bits(b));
                        V::Float64(
                            match op {
                                A::Add => a + b,
                                A::Sub => a - b,
                                A::Mul => a * b,
                                A::Div => a / b,
                                A::Rem => return Err("floating remainder is unsupported"),
                            }
                            .to_bits(),
                        )
                    }
                    _ => return Err("incompatible scalar operands"),
                }
            }
        };
        match (self.ty, value) {
            (ScalarType::Int { .. }, V::Integer(v)) if self.ty.contains_integer(v) => {}
            (ScalarType::Float { width: 32 }, V::Float32(_)) => {}
            (ScalarType::Float { width: 64 }, V::Float64(_)) => {}
            _ => return Err("scalar value outside its type"),
        }
        Ok(Some(value))
    }

    pub fn visit_ids(&self, visit: &mut impl FnMut(AstId)) {
        visit(self.ast_id());
        match &self.kind.kind {
            ScalarExprKind::Neg(a) | ScalarExprKind::FloatCast(a) => a.visit_ids(visit),
            ScalarExprKind::Binary { left, right, .. } => {
                left.visit_ids(visit);
                right.visit_ids(visit);
            }
            _ => {}
        }
    }
}

impl AstIdGenerator {
    pub fn clone_scalar_expr(&mut self, value: &ScalarExpr) -> ScalarExpr {
        let kind = match &value.kind.kind {
            ScalarExprKind::Neg(a) => ScalarExprKind::Neg(Box::new(self.clone_scalar_expr(a))),
            ScalarExprKind::FloatCast(a) => {
                ScalarExprKind::FloatCast(Box::new(self.clone_scalar_expr(a)))
            }
            ScalarExprKind::Binary { op, left, right } => ScalarExprKind::Binary {
                op: *op,
                left: Box::new(self.clone_scalar_expr(left)),
                right: Box::new(self.clone_scalar_expr(right)),
            },
            other => other.clone(),
        };
        self.node(ScalarExprData { ty: value.ty, kind })
    }
}
