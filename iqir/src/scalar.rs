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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScalarType {
    Int { width: u32, signed: bool },
    Float { width: u32 },
}

impl ScalarType {
    /// Exact unsigned shifts. Signed constant shifts are restricted to
    /// nonnegative values and representable results; negative signed shifts
    /// are not silently treated as truncating division.
    pub fn checked_integer_shift(
        self,
        left: bool,
        value: i128,
        count: i128,
    ) -> Result<i128, &'static str> {
        let Self::Int { width, signed } = self else {
            return Err("integer shift type required");
        };
        if !self.contains_integer(value) || count < 0 || (signed && value < 0) {
            return Err("invalid or unsupported integer shift operand");
        }
        if count >= i128::from(width) {
            return if signed && left && value != 0 {
                Err("signed shift overflow")
            } else {
                Ok(0)
            };
        }
        let result = if left {
            (value as u128) << count as u32
        } else {
            (value as u128) >> count as u32
        };
        if signed {
            let result = result as i128;
            self.contains_integer(result)
                .then_some(result)
                .ok_or("signed shift overflow")
        } else {
            Ok((result & ((1u128 << width) - 1)) as i128)
        }
    }

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
                A::BitAnd => a & b,
                A::BitOr => a | b,
                A::BitXor => a ^ b,
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
            A::BitAnd => Some(a & b),
            A::BitOr => Some(a | b),
            A::BitXor => Some(a ^ b),
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
    /// Explicit float -> machine integer conversion, truncating toward zero.
    /// Check the rounded integer before conversion; never use saturating casts.
    pub fn to_integer(self, target: ScalarType) -> Result<Self, &'static str> {
        let value = self.as_float().ok_or("floating operand required")?;
        let (integer, _) = rug::Float::with_val(64, value)
            .to_integer_round(rug::float::Round::Zero)
            .ok_or("non-finite integer cast")?;
        let integer = integer.to_i128().ok_or("out-of-range integer cast")?;
        if !target.contains_integer(integer) {
            return Err("out-of-range integer cast");
        }
        Ok(Self::Integer(integer))
    }

    /// Numeric conversion with RNE, directly to the destination precision.
    /// In particular, integer -> binary32 must not round via binary64 first.
    pub fn to_float(self, target: ScalarType) -> Result<Self, &'static str> {
        Ok(match (target, self) {
            (ScalarType::Float { width: 32 }, Self::Integer(v)) => {
                Self::Float32((v as f32).to_bits())
            }
            (ScalarType::Float { width: 64 }, Self::Integer(v)) => {
                Self::Float64((v as f64).to_bits())
            }
            (ScalarType::Float { width: 32 }, Self::Float32(v)) => Self::Float32(v),
            (ScalarType::Float { width: 64 }, Self::Float64(v)) => Self::Float64(v),
            (ScalarType::Float { width: 32 }, Self::Float64(v)) => {
                Self::Float32((f64::from_bits(v) as f32).to_bits())
            }
            (ScalarType::Float { width: 64 }, Self::Float32(v)) => {
                Self::Float64(f64::from(f32::from_bits(v)).to_bits())
            }
            _ => return Err("unsupported float precision"),
        })
    }

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

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScalarArithmetic {
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    /// Fixed-width bit-pattern operations; never Boolean short-circuiting.
    BitAnd,
    BitOr,
    BitXor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ScalarExprKind {
    /// Range-checked at import, with signedness and width supplied by `ty`.
    Integer(i128),
    /// IEEE encodings preserve signed zero and do not rely on f64 equality.
    Float32(u32),
    Float64(u64),
    Read(SymbolId),
    /// Little-endian bit string interpreted at exactly the destination width.
    /// Signed destinations use two's complement, not unsigned zero extension.
    FromBits(Vec<crate::ClassicalExpr>),
    /// Value-preserving integer conversion; narrowing/reinterpretation is not supported.
    IntWiden(Box<ScalarExpr>),
    /// RNE numeric conversion from an integer or float to binary32/binary64.
    /// The source type retains integer signedness; the destination is `ty`.
    FloatCast(Box<ScalarExpr>),
    /// Explicit finite, representable floating-to-integer conversion (RTZ).
    IntFromFloat(Box<ScalarExpr>),
    FloatUnary {
        op: FloatUnary,
        argument: Box<ScalarExpr>,
    },
    Neg(Box<ScalarExpr>),
    Binary {
        op: ScalarArithmetic,
        left: Box<ScalarExpr>,
        right: Box<ScalarExpr>,
    },
}

/// Typed floating functions, distinct from exact-real math. A consumer must
/// reject operations for which it has no checked semantics (e.g. runtime Acos).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum FloatUnary {
    Floor,
    Ceiling,
    Sqrt,
    /// Principal arccosine on [-1, 1], rounded to the operand precision (RNE).
    Acos,
    /// Sine of a finite argument in radians, rounded at operand precision (RNE).
    Sin,
    /// Principal arcsine on [-1, 1], rounded at operand precision (RNE).
    Asin,
    /// Natural logarithm of a finite positive argument, rounded with RNE.
    Log,
}

impl FloatUnary {
    /// These functions use a finite-input/domain-checked target profile, unlike
    /// total IEEE basic operations. Evaluating them must not be silently erased.
    pub fn requires_domain_check(self) -> bool {
        matches!(self, Self::Acos | Self::Sin | Self::Asin | Self::Log)
    }
    /// Evaluate at the operand's precision. Basic IEEE operations preserve
    /// signed zero/special values; transcendentals require finite inputs in their domains
    /// and a certified rounded result, otherwise evaluation fails closed.
    pub fn evaluate(self, value: ScalarValue) -> Result<ScalarValue, &'static str> {
        if self.requires_domain_check() {
            return rounded_float_math(value, |v, round| match self {
                Self::Acos => {
                    v.acos_round(round);
                }
                Self::Sin => {
                    v.sin_round(round);
                }
                Self::Asin => {
                    v.asin_round(round);
                }
                Self::Log => {
                    v.ln_round(round);
                }
                _ => unreachable!(),
            });
        }
        Ok(match value {
            ScalarValue::Float32(bits) => {
                let x = f32::from_bits(bits);
                ScalarValue::Float32(
                    match self {
                        Self::Floor => x.floor(),
                        Self::Ceiling => x.ceil(),
                        Self::Sqrt => x.sqrt(),
                        Self::Acos | Self::Sin | Self::Asin | Self::Log => unreachable!(),
                    }
                    .to_bits(),
                )
            }
            ScalarValue::Float64(bits) => {
                let x = f64::from_bits(bits);
                ScalarValue::Float64(
                    match self {
                        Self::Floor => x.floor(),
                        Self::Ceiling => x.ceil(),
                        Self::Sqrt => x.sqrt(),
                        Self::Acos | Self::Sin | Self::Asin | Self::Log => unreachable!(),
                    }
                    .to_bits(),
                )
            }
            _ => return Err("floating operand required"),
        })
    }
}

/// Shared certified rounding for closed transcendental calls, including values
/// that become known only during symbolic execution. No host libm approximation.
pub fn rounded_float_math(
    input: ScalarValue,
    apply: impl Fn(&mut rug::Float, rug::float::Round),
) -> Result<ScalarValue, &'static str> {
    use rug::{Float, float::Round};
    let value = input.as_float().ok_or("floating operand required")?;
    if !value.is_finite() {
        return Err("non-finite constant math argument");
    }
    for precision in [128, 256, 512, 1024, 2048, 4096] {
        let mut lo = Float::with_val(precision, value);
        let mut hi = lo.clone();
        apply(&mut lo, Round::Down);
        apply(&mut hi, Round::Up);
        if lo.is_nan() || hi.is_nan() {
            return Err("constant math function domain");
        }
        let round = |v: &Float| match input {
            ScalarValue::Float32(_) => {
                ScalarValue::Float32(v.to_f32_round(Round::Nearest).to_bits())
            }
            ScalarValue::Float64(_) => {
                ScalarValue::Float64(v.to_f64_round(Round::Nearest).to_bits())
            }
            _ => unreachable!(),
        };
        let lower = round(&lo);
        if lower == round(&hi) {
            return if lower.as_float().unwrap().is_finite() {
                Ok(lower)
            } else {
                Err("non-finite constant math result")
            };
        }
    }
    Err("constant math rounding precision budget")
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScalarExprData {
    pub ty: ScalarType,
    pub kind: ScalarExprKind,
}
pub type ScalarExpr = AstNode<ScalarExprData>;

impl ScalarExpr {
    /// Check local IR typing before looking up any values. Unknown operands
    /// must not hide malformed nodes or unsupported operations.
    fn validate_operation(&self) -> Result<(), &'static str> {
        use ScalarExprKind as E;
        let valid_type = |ty| {
            matches!(ty,
                ScalarType::Int { width: 1..=64, .. }
                    | ScalarType::Float { width: 32 | 64 })
        };
        if !valid_type(self.ty) {
            return Err("invalid scalar IR type");
        }
        match &self.kind.kind {
            E::Neg(a) if a.ty != self.ty => return Err("scalar negation type mismatch"),
            E::Binary { op, left, right } => {
                if left.ty != self.ty || right.ty != self.ty {
                    return Err("scalar binary type mismatch");
                }
                if self.ty.is_float() {
                    match op {
                        ScalarArithmetic::BitAnd
                        | ScalarArithmetic::BitOr
                        | ScalarArithmetic::BitXor => {
                            return Err("bitwise operands must be integers");
                        }
                        ScalarArithmetic::Rem => {
                            todo!("IEEE floating remainder is not implemented in scalar IR");
                        }
                        _ => {}
                    }
                }
            }
            E::FloatCast(a) if !self.ty.is_float() || !valid_type(a.ty) => {
                return Err("invalid floating cast types");
            }
            E::IntFromFloat(a) if self.ty.is_float() || !a.ty.is_float() || !valid_type(a.ty) => {
                return Err("invalid float-to-integer cast types");
            }
            E::FloatUnary { argument, .. } if !self.ty.is_float() || argument.ty != self.ty => {
                return Err("floating unary type mismatch");
            }
            _ => {}
        }
        Ok(())
    }

    /// Evaluate a closed expression. Unknown reads are not implicit zeroes.
    /// Nonfinite floating results follow IEEE; const declarations may reject
    /// them separately as part of the frontend's supported constant subset.
    pub fn constant_value(&self) -> Result<Option<ScalarValue>, &'static str> {
        self.constant_value_with(&|_| None)
    }

    /// Evaluate against read-only known values without cloning/substituting
    /// the expression tree. Unknown reads remain unknown; lookup values are
    /// checked against the read node's type just like literal values.
    pub fn constant_value_with(
        &self,
        lookup: &impl Fn(SymbolId) -> Option<ScalarValue>,
    ) -> Result<Option<ScalarValue>, &'static str> {
        self.constant_value_inner(lookup, 0, &mut 65536)
    }

    fn constant_value_inner(
        &self,
        lookup: &impl Fn(SymbolId) -> Option<ScalarValue>,
        depth: usize,
        work: &mut usize,
    ) -> Result<Option<ScalarValue>, &'static str> {
        if depth >= 128 || *work == 0 {
            return Err("constant scalar evaluation budget");
        }
        *work -= 1;
        self.validate_operation()?;
        use ScalarArithmetic as A;
        use ScalarExprKind as E;
        use ScalarValue as V;
        let value = match &self.kind.kind {
            E::Integer(v) => V::Integer(*v),
            E::Float32(v) => V::Float32(*v),
            E::Float64(v) => V::Float64(*v),
            E::Read(id) => match lookup(*id) {
                Some(value) => value,
                None => return Ok(None),
            },
            E::FromBits(bits) => {
                let ScalarType::Int { width, signed } = self.ty else {
                    return Err("bit conversion requires integer type");
                };
                if !(1..=64).contains(&width) || bits.len() != width as usize {
                    return Err("bit conversion width mismatch");
                }
                let mut value = 0i128;
                for (i, bit) in bits.iter().enumerate() {
                    // More complex Boolean expressions remain executable IR;
                    // never replace an unknown measurement/read with zero.
                    let crate::ClassicalExprKind::Bool(bit) = bit.kind else {
                        return Ok(None);
                    };
                    if bit {
                        let weight = 1i128 << i;
                        value += if signed && i + 1 == bits.len() {
                            -weight
                        } else {
                            weight
                        };
                    }
                }
                V::Integer(value)
            }
            E::IntWiden(a) => {
                if !self.ty.losslessly_contains(a.ty) {
                    return Err("unsupported integer conversion");
                }
                let Some(value) = a.constant_value_inner(lookup, depth + 1, work)? else {
                    return Ok(None);
                };
                value
            }
            E::FloatCast(a) => {
                let Some(v) = a.constant_value_inner(lookup, depth + 1, work)? else {
                    return Ok(None);
                };
                v.to_float(self.ty)?
            }
            E::IntFromFloat(a) => {
                let Some(v) = a.constant_value_inner(lookup, depth + 1, work)? else {
                    return Ok(None);
                };
                v.to_integer(self.ty)?
            }
            E::FloatUnary { op, argument } => {
                if self.ty != argument.ty || !self.ty.is_float() {
                    return Err("floating unary type mismatch");
                }
                let Some(v) = argument.constant_value_inner(lookup, depth + 1, work)? else {
                    return Ok(None);
                };
                op.evaluate(v)?
            }
            E::Neg(a) => {
                let Some(v) = a.constant_value_inner(lookup, depth + 1, work)? else {
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
                let left = left.constant_value_inner(lookup, depth + 1, work)?;
                let right = right.constant_value_inner(lookup, depth + 1, work)?;
                if !self.ty.is_float() {
                    if matches!(op, A::Div | A::Rem) && right == Some(V::Integer(0)) {
                        return Err("zero divisor");
                    }
                }
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
                                A::Rem => unreachable!("validated scalar operation"),
                                A::BitAnd | A::BitOr | A::BitXor => {
                                    return Err("bitwise operands must be integers");
                                }
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
                                A::Rem => unreachable!("validated scalar operation"),
                                A::BitAnd | A::BitOr | A::BitXor => {
                                    return Err("bitwise operands must be integers");
                                }
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
            ScalarExprKind::Neg(a)
            | ScalarExprKind::FloatCast(a)
            | ScalarExprKind::IntWiden(a)
            | ScalarExprKind::IntFromFloat(a)
            | ScalarExprKind::FloatUnary { argument: a, .. } => a.visit_ids(visit),
            ScalarExprKind::FromBits(bits) => {
                for bit in bits {
                    bit.visit_ids(visit);
                }
            }
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
            ScalarExprKind::IntFromFloat(a) => {
                ScalarExprKind::IntFromFloat(Box::new(self.clone_scalar_expr(a)))
            }
            ScalarExprKind::FloatUnary { op, argument } => ScalarExprKind::FloatUnary {
                op: *op,
                argument: Box::new(self.clone_scalar_expr(argument)),
            },
            ScalarExprKind::IntWiden(a) => {
                ScalarExprKind::IntWiden(Box::new(self.clone_scalar_expr(a)))
            }
            ScalarExprKind::FromBits(bits) => ScalarExprKind::FromBits(
                bits.iter().map(|b| self.clone_classical_expr(b)).collect(),
            ),
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

impl ScalarType {
    /// All source values fit, without a range precondition or truncation.
    pub fn losslessly_contains(self, source: Self) -> bool {
        match (self, source) {
            (
                Self::Int {
                    width: dst,
                    signed: ds,
                },
                Self::Int {
                    width: src,
                    signed: ss,
                },
            ) if (1..=64).contains(&dst) && (1..=64).contains(&src) => {
                (ds == ss && dst >= src) || (ds && !ss && dst > src)
            }
            _ => false,
        }
    }
}

impl crate::ClassicalExpr {
    pub fn visit_ids(&self, visit: &mut impl FnMut(AstId)) {
        use crate::ClassicalExprKind as C;
        visit(self.ast_id());
        match &self.kind {
            C::Not(a) => a.visit_ids(visit),
            C::Eq(a, b) | C::And(a, b) | C::Or(a, b) | C::Xor(a, b) => {
                a.visit_ids(visit);
                b.visit_ids(visit);
            }
            C::ScalarCompare { left, right, .. } => {
                left.visit_ids(visit);
                right.visit_ids(visit);
            }
            C::Bool(_) | C::Bit(_) => {}
        }
    }
}

impl AstIdGenerator {
    pub fn clone_classical_expr(&mut self, e: &crate::ClassicalExpr) -> crate::ClassicalExpr {
        use crate::ClassicalExprKind as C;
        let kind = match &e.kind {
            C::Not(a) => C::Not(Box::new(self.clone_classical_expr(a))),
            C::Eq(a, b) => C::Eq(
                Box::new(self.clone_classical_expr(a)),
                Box::new(self.clone_classical_expr(b)),
            ),
            C::And(a, b) => C::And(
                Box::new(self.clone_classical_expr(a)),
                Box::new(self.clone_classical_expr(b)),
            ),
            C::Or(a, b) => C::Or(
                Box::new(self.clone_classical_expr(a)),
                Box::new(self.clone_classical_expr(b)),
            ),
            C::Xor(a, b) => C::Xor(
                Box::new(self.clone_classical_expr(a)),
                Box::new(self.clone_classical_expr(b)),
            ),
            C::ScalarCompare { op, left, right } => C::ScalarCompare {
                op: *op,
                left: Box::new(self.clone_scalar_expr(left)),
                right: Box::new(self.clone_scalar_expr(right)),
            },
            other => other.clone(),
        };
        self.node(kind)
    }
}
