//! Constant numeric evaluation used by fixed-point angle initialization.
use super::*;
use crate::ir::NumericConstant;

impl Lowerer {
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

    fn check_const_expression(&self, expr: &Expr, depth: usize) -> Result<(), FrontendError> {
        if depth >= 64 || expr.syntax().text().len() > 65536.into() {
            return Err(unsupported!("constant expression budget", expr));
        }
        match expr {
            Expr::Literal(_) => Ok(()),
            Expr::Identifier(id) => {
                let binding = self.scopes.lookup(&id.string()).map_err(scope_error)?;
                if !matches!(
                    binding.kind,
                    BindingKind::Constant(_) | BindingKind::StaticInteger { is_const: true, .. }
                ) {
                    return Err(expected!("a const-typed expression", expr));
                }
                self.check_constant_visibility(binding, expr)
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

    fn float_width(&self, ty: &ast::ScalarType) -> Result<u32, FrontendError> {
        // Target choice: unspecified float precision is binary64.
        let width = match ty.designator() {
            None => 64,
            Some(d) => self.static_index(
                d.expr().ok_or_else(|| expected!("a float width", ty))?,
                true,
            )?,
        };
        if width != 32 && width != 64 {
            return Err(unsupported!("float precision other than 32/64", ty));
        }
        Ok(width as u32)
    }

    fn contains_float(&self, expr: &Expr) -> Result<bool, FrontendError> {
        match expr {
            Expr::Literal(l) => Ok(matches!(l.kind(), ast::LiteralKind::FloatNumber(_))),
            Expr::Identifier(id) => Ok(matches!(
                self.scopes.lookup(&id.string()).map_err(scope_error)?.kind,
                BindingKind::Constant(_)
            )),
            Expr::CastExpression(c)
                if c.scalar_type().is_some_and(|t| t.float_token().is_some()) =>
            {
                Ok(true)
            }
            _ => {
                for c in expr.syntax().children().filter_map(Expr::cast) {
                    if self.contains_float(&c)? {
                        return Ok(true);
                    }
                }
                Ok(false)
            }
        }
    }

    pub(super) fn static_float(
        &self,
        expr: Expr,
        depth: usize,
    ) -> Result<(f64, u32), FrontendError> {
        if depth == 0 {
            self.check_const_expression(&expr, 0)?;
        }
        if depth >= 64 {
            return Err(unsupported!("constant float expression depth", &expr));
        }
        if !self.contains_float(&expr)? {
            let value = self.static_integer(expr, true)?.value;
            // Integer-to-float promotion defaults to binary64. A typed binary32
            // context uses the original integer through float_operand below.
            return Ok((value as f64, 0));
        }
        let result = match expr.clone() {
            Expr::Identifier(id) => {
                let binding = self.scopes.lookup(&id.string()).map_err(scope_error)?;
                self.check_constant_visibility(binding, &id)?;
                match binding.kind {
                    BindingKind::Constant(c) => (
                        match c {
                            NumericConstant::Pi => std::f64::consts::PI,
                            NumericConstant::Tau => std::f64::consts::TAU,
                            NumericConstant::Euler => std::f64::consts::E,
                        },
                        64,
                    ),
                    _ => return Err(expected!("a numeric constant", &id)),
                }
            }
            Expr::Literal(l) => {
                let ast::LiteralKind::FloatNumber(n) = l.kind() else {
                    return Err(expected!("a float literal", &l));
                };
                (
                    n.to_string()
                        .replace('_', "")
                        .parse::<f64>()
                        .map_err(|_| expected!("a binary64 literal", &l))?,
                    64,
                )
            }
            Expr::ParenExpr(p) => self.static_float(
                p.expr().ok_or_else(|| expected!("an operand", &p))?,
                depth + 1,
            )?,
            Expr::PrefixExpr(p) if p.op_kind() == Some(ast::UnaryOp::Neg) => {
                let (v, w) = self.static_float(
                    p.expr().ok_or_else(|| expected!("an operand", &p))?,
                    depth + 1,
                )?;
                (-v, w)
            }
            Expr::CastExpression(c) => {
                let t = c
                    .scalar_type()
                    .ok_or_else(|| expected!("a float cast", &c))?;
                if t.float_token().is_none() {
                    return Err(unsupported!("constant numeric cast", &c));
                }
                let w = self.float_width(&t)?;
                let operand = c.expr().ok_or_else(|| expected!("a cast operand", &c))?;
                (self.float_operand(operand, w, depth + 1)?, w)
            }
            Expr::BinExpr(b) => {
                let l = b.lhs().ok_or_else(|| expected!("a left operand", &b))?;
                let r = b.rhs().ok_or_else(|| expected!("a right operand", &b))?;
                let (av, lw) = self.static_float(l.clone(), depth + 1)?;
                let (zv, rw) = self.static_float(r.clone(), depth + 1)?;
                let w = lw.max(rw).max(32);
                let a = if lw == 0 && w == 32 {
                    f64::from(self.static_integer(l, true)?.value as f32)
                } else {
                    av
                };
                let z = if rw == 0 && w == 32 {
                    f64::from(self.static_integer(r, true)?.value as f32)
                } else {
                    zv
                };
                let op = b.op_kind();
                let v = if w == 32 {
                    let (a, z) = (a as f32, z as f32);
                    f64::from(match op {
                        Some(ast::BinaryOp::ArithOp(ast::ArithOp::Add)) => a + z,
                        Some(ast::BinaryOp::ArithOp(ast::ArithOp::Sub)) => a - z,
                        Some(ast::BinaryOp::ArithOp(ast::ArithOp::Mul)) => a * z,
                        Some(ast::BinaryOp::ArithOp(ast::ArithOp::Div)) => a / z,
                        _ => return Err(unsupported!("constant float operator", &b)),
                    })
                } else {
                    match op {
                        Some(ast::BinaryOp::ArithOp(ast::ArithOp::Add)) => a + z,
                        Some(ast::BinaryOp::ArithOp(ast::ArithOp::Sub)) => a - z,
                        Some(ast::BinaryOp::ArithOp(ast::ArithOp::Mul)) => a * z,
                        Some(ast::BinaryOp::ArithOp(ast::ArithOp::Div)) => a / z,
                        _ => return Err(unsupported!("constant float operator", &b)),
                    }
                };
                (v, w)
            }
            _ => return Err(unsupported!("constant float expression", &expr)),
        };
        if !result.0.is_finite() {
            return Err(unsupported!("non-finite constant float", &expr));
        }
        Ok(result)
    }

    fn float_operand(&self, expr: Expr, width: u32, depth: usize) -> Result<f64, FrontendError> {
        if !self.contains_float(&expr)? {
            let v = self.static_integer(expr, true)?.value;
            return Ok(if width == 32 {
                f64::from(v as f32)
            } else {
                v as f64
            });
        }
        let (v, _) = self.static_float(expr, depth)?;
        Ok(if width == 32 { f64::from(v as f32) } else { v })
    }
}
