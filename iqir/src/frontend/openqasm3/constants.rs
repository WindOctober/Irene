//! Typed compile-time constants. In particular, a float constant stores an
//! IEEE value, not the exact real expression that initialized it.
use super::*;
use crate::{ScalarExpr, ScalarType, ScalarValue};

impl Lowerer {
    pub(super) fn has_float_binding(&self, expr: &Expr) -> Result<bool, FrontendError> {
        if let Expr::Identifier(id) = expr {
            return Ok(matches!(
                self.scopes.lookup(&id.string()).map_err(scope_error)?.kind,
                BindingKind::Scalar {
                    ty: ScalarType::Float { .. },
                    ..
                }
            ));
        }
        if let Expr::CastExpression(c) = expr
            && c.scalar_type().is_some_and(|t| t.float_token().is_some())
        {
            return Ok(true);
        }
        for child in expr.syntax().children().filter_map(Expr::cast) {
            if self.has_float_binding(&child)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn is_integer_expression(&self, expr: &Expr) -> Result<bool, FrontendError> {
        match expr {
            Expr::Literal(l) => Ok(matches!(l.kind(), ast::LiteralKind::IntNumber(_))),
            Expr::Identifier(id) => Ok(matches!(
                self.scopes.lookup(&id.string()).map_err(scope_error)?.kind,
                BindingKind::Scalar {
                    ty: ScalarType::Int { .. },
                    value: Some(_),
                    ..
                }
            )),
            Expr::ParenExpr(_) | Expr::PrefixExpr(_) | Expr::BinExpr(_) => {
                for child in expr.syntax().children().filter_map(Expr::cast) {
                    if !self.is_integer_expression(&child)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            _ => Ok(false),
        }
    }

    pub(super) fn check_constant_visibility<T: AstNode>(
        &self,
        binding: Binding,
        source: &T,
    ) -> Result<(), FrontendError> {
        if self.scopes.global_static_ids().contains(&binding.id)
            && self.active_subroutines.iter().any(|index| {
                !self.subroutines[*index]
                    .static_globals
                    .contains(&binding.id)
            })
        {
            return Err(expected!(
                "a constant visible at subroutine definition",
                source
            ));
        }
        Ok(())
    }

    /// Check const-typedness before evaluating: even `false && scalar_bit`
    /// is not a const expression. Reject unsupported syntax instead of guessing.
    pub(super) fn check_const_expression(
        &self,
        expr: &Expr,
        depth: usize,
    ) -> Result<(), FrontendError> {
        if depth >= 64 || expr.syntax().text().len() > 65536.into() {
            return Err(unsupported!("constant expression budget", expr));
        }
        match expr {
            Expr::Literal(_) => Ok(()),
            Expr::Identifier(id) => {
                let binding = self.scopes.lookup(&id.string()).map_err(scope_error)?;
                if !matches!(
                    binding.kind,
                    BindingKind::Constant(_)
                        | BindingKind::Scalar { is_const: true, .. }
                        | BindingKind::StaticBits { .. }
                ) {
                    return Err(expected!("a const-typed expression", expr));
                }
                self.check_constant_visibility(binding, expr)
            }
            Expr::IndexedIdentifier(indexed) => {
                let (name, index) = static_integer::single_index(indexed.clone())?;
                let binding = self.scopes.lookup(&name).map_err(scope_error)?;
                if !matches!(binding.kind, BindingKind::StaticBits { .. }) {
                    return Err(expected!("an indexable constant", expr));
                }
                self.check_constant_visibility(binding, expr)?;
                self.static_index(index, true)?;
                Ok(())
            }
            Expr::ParenExpr(_)
            | Expr::PrefixExpr(_)
            | Expr::BinExpr(_)
            | Expr::CastExpression(_) => {
                for child in expr.syntax().children().filter_map(Expr::cast) {
                    self.check_const_expression(&child, depth + 1)?;
                }
                Ok(())
            }
            _ => Err(unsupported!("constant expression form", expr)),
        }
    }

    pub(super) fn constant_bits(&mut self, value: u64, ty: BitType) -> TypedClassicalExpr {
        let bits: Vec<_> = (0..ty.width())
            .map(|i| {
                self.ids
                    .node(ClassicalExprKind::Bool(value & (1_u64 << i) != 0))
            })
            .collect();
        match ty {
            BitType::Bool => TypedClassicalExpr::Bool(bits.into_iter().next().unwrap()),
            BitType::Bit => TypedClassicalExpr::Bit(bits.into_iter().next().unwrap()),
            BitType::Register { .. } => TypedClassicalExpr::Register(bits),
            BitType::Angle { .. } => TypedClassicalExpr::Angle(bits),
            BitType::Uint { explicit_width, .. } => TypedClassicalExpr::Integer {
                bits,
                signedness: Signedness::Unsigned,
                explicit_width,
            },
        }
    }

    pub(super) fn lower_bit_constant(
        &mut self,
        declaration: ast::ClassicalDeclarationStatement,
        ty: ast::ScalarType,
    ) -> Result<(), FrontendError> {
        self.charge_static_expansion(&declaration)?;
        let expr = declaration
            .expr()
            .ok_or_else(|| expected!("a const initializer", &declaration))?;
        self.check_const_expression(&expr, 0)?;
        let kind = {
            let storage = if ty.angle_token().is_some() {
                BitType::Angle {
                    width: self.angle_width(&ty)?,
                }
            } else if ty.bool_token().is_some() && ty.designator().is_none() {
                BitType::Bool
            } else if ty.bit_token().is_some() {
                self.static_bit_type(ty.designator(), "a constant bit width")?
            } else {
                return Err(unsupported!("constant type", &ty));
            };
            if storage.width() > 64 {
                return Err(unsupported!("constant bit width above 64", &ty));
            }
            // Constant folding must not consume IDs of executable IR nodes.
            let saved_ids = self.ids.clone();
            let folded = (|| {
                let expression = if let BitType::Angle { width } = storage {
                    self.angle_value(expr, width, false)?
                } else {
                    self.lower_bit_expr(expr)?
                };
                if expression
                    .bit_type()
                    .is_none_or(|t| !bit_types_compatible(storage, t))
                {
                    return Err(expected!(
                        "a type-compatible constant initializer",
                        &declaration
                    ));
                }
                let mut value = 0;
                for (i, bit) in expression.into_bit_cells().unwrap().iter().enumerate() {
                    let b = eval_constant_bit(bit)
                        .ok_or_else(|| expected!("a constant value", &declaration))?;
                    value |= u64::from(b) << i;
                }
                Ok(BindingKind::StaticBits { value, ty: storage })
            })();
            self.ids = saved_ids;
            folded?
        };
        self.scopes
            .declare(declaration_name(&declaration)?, kind)
            .map_err(scope_error)?;
        Ok(())
    }

    pub(super) fn require_scalar_constant<T: AstNode>(
        &self,
        expression: &ScalarExpr,
        source: &T,
    ) -> Result<ScalarValue, FrontendError> {
        let value = expression
            .constant_value()
            .map_err(|_| unsupported!("invalid constant scalar arithmetic", source))?
            .ok_or_else(|| expected!("a constant scalar value", source))?;
        if value.as_float().is_some_and(|f| !f.is_finite()) {
            return Err(unsupported!("non-finite constant float", source));
        }
        Ok(value)
    }

    /// Bridge typed finite-precision values to existing angle/gate consumers.
    /// Parsing, promotion and rounding are shared with all scalar expressions.
    pub(super) fn static_float(
        &mut self,
        expr: Expr,
        _depth: usize,
    ) -> Result<(f64, u32), FrontendError> {
        self.check_const_expression(&expr, 0)?;
        let saved_ids = self.ids.clone();
        let result = (|| {
            let value = self.lower_scalar_expr(expr.clone(), ScalarType::Float { width: 64 })?;
            let value = self.require_scalar_constant(&value, &expr)?;
            Ok((
                value
                    .as_float()
                    .ok_or_else(|| expected!("a floating-point value", &expr))?,
                64,
            ))
        })();
        self.ids = saved_ids;
        result
    }
}

pub(super) fn eval_constant_bit(e: &ClassicalExpr) -> Option<bool> {
    Some(match &e.kind {
        ClassicalExprKind::ScalarCompare { .. } => return None,
        ClassicalExprKind::Bool(b) => *b,
        ClassicalExprKind::Bit(_) => return None,
        ClassicalExprKind::Not(a) => !eval_constant_bit(a)?,
        ClassicalExprKind::And(a, b) => eval_constant_bit(a)? & eval_constant_bit(b)?,
        ClassicalExprKind::Or(a, b) => eval_constant_bit(a)? | eval_constant_bit(b)?,
        ClassicalExprKind::Xor(a, b) => eval_constant_bit(a)? ^ eval_constant_bit(b)?,
        ClassicalExprKind::Eq(a, b) => eval_constant_bit(a)? == eval_constant_bit(b)?,
    })
}
