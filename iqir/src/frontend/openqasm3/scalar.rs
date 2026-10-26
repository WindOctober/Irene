//! Typed scalar lowering shared by const declarations and ordinary variables.
//! Type/width, const qualification and known values are independent properties.
use super::*;
use crate::{
    ScalarArithmetic as A, ScalarComparison as C, ScalarExpr, ScalarExprData, ScalarExprKind as E,
    ScalarType,
};

impl Lowerer {
    pub(super) fn is_scalar_declaration(
        &self,
        declaration: &ast::ClassicalDeclarationStatement,
    ) -> bool {
        declaration.scalar_type().is_some_and(|ty| {
            ty.int_token().is_some()
                || ty.float_token().is_some()
                || ((declaration.const_token().is_some() || self.preserve_uint)
                    && ty.uint_token().is_some())
        })
    }

    /// One type parser for const declarations, variables and casts.
    pub(super) fn scalar_type(
        &self,
        source: &ast::ScalarType,
    ) -> Result<ScalarType, FrontendError> {
        let width = match source.designator() {
            Some(d) => self.static_index(
                d.expr().ok_or_else(|| expected!("scalar width", source))?,
                true,
            )?,
            None if source.float_token().is_some() => 64,
            None => static_integer::DEFAULT_INTEGER_WIDTH as usize,
        };
        if source.float_token().is_some() && matches!(width, 32 | 64) {
            Ok(ScalarType::Float {
                width: width as u32,
            })
        } else if (source.int_token().is_some() || source.uint_token().is_some())
            && (1..=64).contains(&width)
        {
            Ok(ScalarType::Int {
                width: width as u32,
                signed: source.int_token().is_some(),
            })
        } else {
            Err(unsupported!("scalar type or width", source))
        }
    }

    pub(super) fn lower_scalar_declaration(
        &mut self,
        declaration: ast::ClassicalDeclarationStatement,
    ) -> Result<Vec<Statement>, FrontendError> {
        self.charge_static_expansion(&declaration)?;
        let name = declaration_name(&declaration)?;
        let source_ty = declaration
            .scalar_type()
            .ok_or_else(|| expected!("scalar type", &declaration))?;
        let ty = self.scalar_type(&source_ty)?;
        let explicit_width = source_ty.designator().is_some();
        let is_const = declaration.const_token().is_some();
        let binding = self
            .scopes
            .declare(
                name.clone(),
                BindingKind::Scalar {
                    ty,
                    explicit_width,
                    is_const,
                    assignable: !is_const,
                    value: None,
                },
            )
            .map_err(scope_error)?;
        let source = declaration.expr();
        if let Some(Expr::CallExpr(call)) = &source {
            if self.is_subroutine_call(call) {
                if is_const {
                    return Err(unsupported!(
                        "subroutine call in const initializer",
                        &declaration
                    ));
                }
                let storage = self.ids.node(StatementKind::ScalarDeclare {
                    id: binding.id,
                    name,
                    ty,
                    explicit_width,
                    initializer: None,
                });
                self.known_scalars.declare(binding.id, None)?;
                let invocation = self.lower_subroutine_call(
                    call.clone(),
                    Some(super::subroutines::CallTarget::Scalar { id: binding.id, ty }),
                )?;
                return Ok(vec![storage, invocation]);
            }
        }
        if is_const {
            let source = source
                .as_ref()
                .ok_or_else(|| expected!("a const initializer", &declaration))?;
            self.check_const_expression(source, 0)?;
        }
        // Both declarations use the same typed expression builder. Const
        // evaluation consumes no executable AST identities.
        let saved_ids = self.ids.clone();
        let initializer = source.map(|e| self.lower_scalar_expr(e, ty)).transpose();
        if is_const {
            self.ids = saved_ids;
        }
        let initializer = initializer?;
        if !is_const {
            // Declaration lowering can bypass lower_statement (top level and
            // block declarations), so establish its fact here as well.
            self.known_scalars.declare(binding.id, initializer.as_ref())?;
        }
        if is_const {
            let value =
                self.require_scalar_constant(initializer.as_ref().unwrap(), &declaration)?;
            self.scopes.set_scalar_value(&name, value);
        }
        Ok(if is_const {
            Vec::new()
        } else {
            vec![self.ids.node(StatementKind::ScalarDeclare {
                id: binding.id,
                name,
                ty,
                explicit_width,
                initializer,
            })]
        })
    }

    /// Infer from declared types, regardless of const qualification or known value.
    pub(super) fn scalar_hint(
        &self,
        expression: &Expr,
    ) -> Result<Option<ScalarType>, FrontendError> {
        self.scalar_hint_depth(expression, 0)
    }

    fn scalar_hint_depth(
        &self,
        expression: &Expr,
        depth: usize,
    ) -> Result<Option<ScalarType>, FrontendError> {
        if let Some(Binding {
            kind: BindingKind::Scalar { ty, .. },
            ..
        }) = self.array_cell(expression, false)?
        {
            return Ok(Some(ty));
        }
        if depth >= 128 {
            return Err(unsupported!("scalar expression depth", expression));
        }
        match expression {
            Expr::CallExpr(call) => {
                self.builtin_math_call(call)?;
                Ok(Some(self.float_expression_type_depth(
                    expression,
                    ScalarType::Float { width: 64 },
                    depth + 1,
                )?))
            }
            Expr::Identifier(id) => Ok(
                match self.scopes.lookup(&id.string()).map_err(scope_error)?.kind {
                    BindingKind::Scalar { ty, .. } => Some(ty),
                    BindingKind::ClassicalBit(BitType::Uint { width, .. }) => {
                        Some(ScalarType::Int {
                            width: width as u32,
                            signed: false,
                        })
                    }
                    _ => None,
                },
            ),
            Expr::CastExpression(c) => {
                let ty = c.scalar_type().ok_or_else(|| expected!("cast type", c))?;
                if ty.float_token().is_some()
                    || ty.int_token().is_some()
                    || ty.uint_token().is_some()
                {
                    Ok(Some(self.scalar_type(&ty)?))
                } else {
                    Ok(None)
                }
            }
            _ => {
                let mut result = None;
                for child in expression.syntax().children().filter_map(Expr::cast) {
                    if let Some(ty) = self.scalar_hint_depth(&child, depth + 1)? {
                        result = Some(match result {
                            Some(ScalarType::Float { width }) if ty.is_float() => {
                                ScalarType::Float {
                                    width: width.max(ty.width()),
                                }
                            }
                            Some(previous) if previous != ty => {
                                return Err(unsupported!(
                                    "mixed scalar types require a supported conversion",
                                    expression
                                ));
                            }
                            _ => ty,
                        });
                    }
                }
                Ok(result)
            }
        }
    }

    /// Boolean words retain their established lowering; numeric storage and
    /// float comparisons use typed scalar expressions, including const floats.
    pub(super) fn has_scalar_comparison(&self, expression: &Expr) -> Result<bool, FrontendError> {
        self.has_scalar_comparison_depth(expression, 0)
    }

    fn has_scalar_comparison_depth(
        &self,
        expression: &Expr,
        depth: usize,
    ) -> Result<bool, FrontendError> {
        if self.array_cell(expression, false)?.is_some() {
            return Ok(true);
        }
        if depth >= 128 {
            return Err(unsupported!("scalar expression depth", expression));
        }
        if let Expr::CallExpr(call) = expression {
            self.builtin_math_call(call)?;
            return Ok(true);
        }
        if let Expr::Identifier(id) = expression {
            return Ok(matches!(
                self.scopes.lookup(&id.string()).map_err(scope_error)?.kind,
                BindingKind::Scalar { value: None, .. }
                    | BindingKind::Scalar {
                        ty: ScalarType::Float { .. },
                        ..
                    }
            ));
        }
        if let Expr::Literal(l) = expression {
            return Ok(matches!(l.kind(), ast::LiteralKind::FloatNumber(_)));
        }
        if let Expr::CastExpression(c) = expression
            && c.scalar_type().is_some_and(|t| t.float_token().is_some())
        {
            return Ok(true);
        }
        for child in expression.syntax().children().filter_map(Expr::cast) {
            if self.has_scalar_comparison_depth(&child, depth + 1)? {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(super) fn lower_scalar_expr(
        &mut self,
        source: Expr,
        ty: ScalarType,
    ) -> Result<ScalarExpr, FrontendError> {
        if source.syntax().text().len() > 65536.into()
            || source.syntax().descendants().filter_map(Expr::cast).count() > 4096
        {
            return Err(unsupported!("scalar expression budget", &source));
        }
        let result = self.scalar_expr_depth(source.clone(), ty, 0)?;
        // Diagnose invalid closed integer arithmetic even in a variable's
        // initializer; lack of const qualification is not a different semantics.
        result
            .constant_value()
            .map_err(|_| unsupported!("invalid scalar constant arithmetic", &source))?;
        Ok(result)
    }

    pub(super) fn float_expression_type(
        &self,
        source: &Expr,
        fallback: ScalarType,
    ) -> Result<ScalarType, FrontendError> {
        self.float_expression_type_depth(source, fallback, 0)
    }

    fn float_expression_type_depth(
        &self,
        source: &Expr,
        fallback: ScalarType,
        depth: usize,
    ) -> Result<ScalarType, FrontendError> {
        if let Some(Binding {
            kind: BindingKind::Scalar { ty, .. },
            ..
        }) = self.array_cell(source, false)?
        {
            return Ok(if ty.is_float() { ty } else { fallback });
        }
        if depth >= 128 {
            return Err(unsupported!("scalar expression depth", source));
        }
        let width = match source {
            Expr::CallExpr(call) => {
                let (_, argument) = self.builtin_math_call(call)?;
                self.float_expression_type_depth(
                    &argument,
                    ScalarType::Float { width: 64 },
                    depth + 1,
                )?
                .width()
            }
            Expr::Literal(l) if matches!(l.kind(), ast::LiteralKind::FloatNumber(_)) => 64,
            Expr::Identifier(id) => {
                match self.scopes.lookup(&id.string()).map_err(scope_error)?.kind {
                    BindingKind::Scalar {
                        ty: ScalarType::Float { width },
                        ..
                    } => width,
                    BindingKind::Constant(_) => 64,
                    _ => 0,
                }
            }
            Expr::CastExpression(c)
                if c.scalar_type().is_some_and(|t| t.float_token().is_some()) =>
            {
                self.scalar_type(&c.scalar_type().unwrap())?.width()
            }
            _ => {
                let mut width = 0;
                for child in source.syntax().children().filter_map(Expr::cast) {
                    width = width.max(
                        self.float_expression_type_depth(
                            &child,
                            ScalarType::Float { width: 0 },
                            depth + 1,
                        )?
                        .width(),
                    );
                }
                width
            }
        };
        Ok(if width == 0 {
            fallback
        } else {
            ScalarType::Float { width }
        })
    }

    fn float_convert(&mut self, expression: ScalarExpr, ty: ScalarType) -> ScalarExpr {
        if expression.ty == ty {
            expression
        } else {
            debug_assert!(ty.is_float());
            self.ids.node(ScalarExprData {
                ty,
                kind: E::FloatCast(Box::new(expression)),
            })
        }
    }

    fn scalar_expr_depth(
        &mut self,
        source: Expr,
        ty: ScalarType,
        depth: usize,
    ) -> Result<ScalarExpr, FrontendError> {
        if depth >= 128 {
            return Err(unsupported!("scalar expression depth", &source));
        }
        if !self.resolving_known_scalars
            && (matches!(&source, Expr::CallExpr(_) | Expr::CastExpression(_))
                || static_integer::is_bit_operation(&source))
        {
            return self.with_known_scalars(|this| this.scalar_expr_depth(source, ty, depth));
        }
        // Integer-only closed subexpressions retain integer division and
        // checked width semantics even inside a floating-point expression.
        if let Some(value) = self.closed_integer(&source)? {
            if depth > 0
                && !ty.is_float()
                && value.width.is_some_and(|width| {
                    width != ty.width()
                        || value.signed != matches!(ty, ScalarType::Int { signed: true, .. })
                })
            {
                return Err(unsupported!(
                    "mixed-width typed integer subexpression",
                    &source
                ));
            }
            let kind = if ty.is_float() {
                if ty.width() == 32 {
                    E::Float32((value.value as f32).to_bits())
                } else {
                    E::Float64((value.value as f64).to_bits())
                }
            } else {
                self.scalar_integer(value.value, ty, &source)?
            };
            return Ok(self.ids.node(ScalarExprData { ty, kind }));
        }
        let requested = ty;
        if ty.is_float()
            && self
                .float_expression_type(&source, ScalarType::Float { width: 0 })?
                .width()
                == 0
            && let Some(source_ty @ ScalarType::Int { .. }) =
                self.scalar_hint_depth(&source, depth + 1)?
        {
            let value = self.scalar_expr_depth(source, source_ty, depth + 1)?;
            return Ok(self.float_convert(value, requested));
        }
        let ty = if ty.is_float() {
            self.float_expression_type(&source, ty)?
        } else {
            ty
        };
        let kind = match source.clone() {
            Expr::IndexedIdentifier(_) if self.array_cell(&source, false)?.is_some() => {
                let binding = self.array_cell(&source, false)?.unwrap();
                let BindingKind::Scalar {
                    ty: found, value, ..
                } = binding.kind
                else {
                    unreachable!()
                };
                let kind = value
                    .map(crate::ScalarValue::expression)
                    .unwrap_or(E::Read(binding.id));
                let read = self.ids.node(ScalarExprData { ty: found, kind });
                if found == ty || (found.is_float() && ty.is_float()) {
                    return Ok(if found.is_float() {
                        self.float_convert(read, requested)
                    } else {
                        read
                    });
                }
                return Err(expected!(
                    "an array element of matching scalar type and width",
                    &source
                ));
            }
            Expr::CallExpr(call) => {
                if !ty.is_float() {
                    return Err(expected!("an explicit float-to-integer cast", &call));
                }
                let (function, argument) = self.builtin_math_call(&call)?;
                if let Some(op) = function.symbolic() {
                    let argument = self.scalar_expr_depth(argument, ty, depth + 1)?;
                    let expression = self.ids.node(ScalarExprData {
                        ty,
                        kind: E::FloatUnary {
                            op,
                            argument: Box::new(argument),
                        },
                    });
                    // Known and unknown operands share the same typed operation.
                    if let Some(value) = expression
                        .constant_value()
                        .map_err(|r| unsupported!(r, &call))?
                    {
                        if !value.as_float().unwrap().is_finite() {
                            return Err(unsupported!("non-finite constant math result", &call));
                        }
                        return Ok(self.ids.node(ScalarExprData {
                            ty: requested,
                            kind: value
                                .to_float(requested)
                                .map_err(|r| unsupported!(r, &call))?
                                .expression(),
                        }));
                    }
                    return Ok(self.float_convert(expression, requested));
                }
                let saved_ids = self.ids.clone();
                let result = (|| {
                    let argument = self.scalar_expr_depth(argument, ty, depth + 1)?;
                    let value = self.require_scalar_constant(&argument, &source)?;
                    function
                        .evaluate(value.as_float().unwrap(), ty)
                        .map_err(|reason| unsupported!(reason, &call))
                })();
                self.ids = saved_ids;
                result?.expression()
            }
            Expr::ParenExpr(p) => {
                return self.scalar_expr_depth(
                    p.expr()
                        .ok_or_else(|| expected!("parenthesized value", &p))?,
                    requested,
                    depth + 1,
                );
            }
            Expr::Identifier(id) => {
                let binding = self.scopes.lookup(&id.string()).map_err(scope_error)?;
                match binding.kind {
                    BindingKind::ClassicalBit(BitType::Uint { width, .. }) => {
                        let source_ty = ScalarType::Int {
                            width: width as u32,
                            signed: false,
                        };
                        let TypedClassicalExpr::Integer { bits, .. } =
                            self.lower_typed_classical_expr(source.clone())?
                        else {
                            return Err(expected!("an unsigned integer", &source));
                        };
                        if !(1..=64).contains(&width) || (!ty.is_float() && source_ty != ty) {
                            return Err(expected!("a scalar of matching type and width", &source));
                        }
                        let value = self.ids.node(ScalarExprData {
                            ty: source_ty,
                            kind: E::FromBits(bits),
                        });
                        return Ok(if ty.is_float() {
                            self.float_convert(value, requested)
                        } else {
                            value
                        });
                    }
                    BindingKind::Scalar {
                        ty: found, value, ..
                    } => {
                        if value.is_some() {
                            self.check_constant_visibility(binding, &source)?;
                        }
                        let kind = value
                            .map(crate::ScalarValue::expression)
                            .unwrap_or(E::Read(binding.id));
                        let read = self.ids.node(ScalarExprData { ty: found, kind });
                        if found == ty {
                            return Ok(if found.is_float() {
                                self.float_convert(read, requested)
                            } else {
                                read
                            });
                        }
                        if found.is_float() && ty.is_float() {
                            return Ok(self.float_convert(read, requested));
                        }
                        if !found.is_float() && ty.is_float() {
                            let converted = self.float_convert(read, ty);
                            return Ok(self.float_convert(converted, requested));
                        }
                        return Err(expected!("a scalar of matching type and width", &source));
                    }
                    BindingKind::Constant(c) if ty.is_float() => {
                        let value = match c {
                            crate::NumericConstant::Pi => std::f64::consts::PI,
                            crate::NumericConstant::Tau => std::f64::consts::TAU,
                            crate::NumericConstant::Euler => std::f64::consts::E,
                        };
                        float_value(value, ty, &source)?
                    }
                    _ => return Err(expected!("a numeric scalar", &source)),
                }
            }
            Expr::CastExpression(c) => {
                let target = c
                    .scalar_type()
                    .ok_or_else(|| expected!("a scalar cast type", &c))?;
                let target = self.scalar_type(&target)?;
                let operand = c
                    .expr()
                    .ok_or_else(|| expected!("a scalar cast operand", &c))?;
                if !target.is_float() {
                    let operand_hint = match &operand {
                        Expr::CastExpression(inner) => {
                            let ty = inner
                                .scalar_type()
                                .ok_or_else(|| expected!("cast type", inner))?;
                            if ty.int_token().is_some() || ty.uint_token().is_some() {
                                Some(self.scalar_type(&ty)?)
                            } else {
                                self.scalar_hint_depth(&operand, depth + 1)?
                            }
                        }
                        _ => self.scalar_hint_depth(&operand, depth + 1)?,
                    };
                    let operand_float_ty =
                        self.float_expression_type(&operand, ScalarType::Float { width: 0 })?;
                    if !operand_hint.is_some_and(ScalarType::is_float)
                        && operand_float_ty.width() == 0
                    {
                        if requested != target {
                            return Err(unsupported!(
                                "implicit conversion of an integer cast result",
                                &c
                            ));
                        }
                        let kind = if let Some(source_ty) = operand_hint {
                            if !target.losslessly_contains(source_ty) {
                                return Err(unsupported!("non-value-preserving integer cast", &c));
                            }
                            E::IntWiden(Box::new(self.scalar_expr_depth(
                                operand,
                                source_ty,
                                depth + 1,
                            )?))
                        } else if self.is_closed_integer_expression(&operand)? {
                            let value = self.static_integer(operand, false)?;
                            self.scalar_integer(value.value, target, &source)?
                        } else {
                            match self.lower_typed_classical_expr(operand)? {
                                TypedClassicalExpr::Register(bits) => {
                                    if !c.scalar_type().is_some_and(|t| t.designator().is_some())
                                        || bits.len() != target.width() as usize
                                    {
                                        return Err(expected!(
                                            "an explicitly sized integer cast matching its bit width",
                                            &c
                                        ));
                                    }
                                    E::FromBits(bits)
                                }
                                TypedClassicalExpr::Integer {
                                    bits, signedness, ..
                                } => {
                                    let source_ty = ScalarType::Int {
                                        width: bits.len() as u32,
                                        signed: signedness == Signedness::Signed,
                                    };
                                    if !target.losslessly_contains(source_ty) {
                                        return Err(unsupported!(
                                            "non-value-preserving integer cast",
                                            &c
                                        ));
                                    }
                                    let value = self.ids.node(ScalarExprData {
                                        ty: source_ty,
                                        kind: E::FromBits(bits),
                                    });
                                    E::IntWiden(Box::new(value))
                                }
                                _ => return Err(unsupported!("bit string to integer cast", &c)),
                            }
                        };
                        return Ok(self.ids.node(ScalarExprData { ty: target, kind }));
                    }
                    // Preserve an explicit conversion when the operand is symbolic.
                    let operand_ty = operand_float_ty;
                    if operand_ty.width() == 0 || (!requested.is_float() && requested != target) {
                        return Err(unsupported!("scalar cast", &c));
                    }
                    let operand = self.scalar_expr_depth(operand, operand_ty, depth + 1)?;
                    let mut converted = self.ids.node(ScalarExprData {
                        ty: target,
                        kind: E::IntFromFloat(Box::new(operand)),
                    });
                    if let Some(value) = converted
                        .constant_value()
                        .map_err(|r| unsupported!(r, &c))?
                    {
                        converted = self.ids.node(ScalarExprData {
                            ty: target,
                            kind: value.expression(),
                        });
                    }
                    return Ok(if requested.is_float() {
                        self.float_convert(converted, requested)
                    } else {
                        converted
                    });
                }
                if !requested.is_float() {
                    return Err(unsupported!("scalar cast", &c));
                }
                // Evaluate integer arithmetic at its original width before
                // conversion, e.g. float[64](n / 2) retains integer division.
                let source_hint = match &operand {
                    Expr::CastExpression(inner) => Some(
                        self.scalar_type(
                            &inner
                                .scalar_type()
                                .ok_or_else(|| expected!("cast type", inner))?,
                        )?,
                    ),
                    _ if self
                        .float_expression_type(&operand, ScalarType::Float { width: 0 })?
                        .width()
                        == 0 =>
                    {
                        self.scalar_hint_depth(&operand, depth + 1)?
                    }
                    _ => None,
                };
                let source_ty = source_hint.filter(|ty| !ty.is_float()).unwrap_or(target);
                let value = self.scalar_expr_depth(operand, source_ty, depth + 1)?;
                let converted = self.float_convert(value, target);
                return Ok(self.float_convert(converted, requested));
            }
            Expr::Literal(ref lit) => match lit.kind() {
                ast::LiteralKind::IntNumber(n) if !ty.is_float() => {
                    let value = i128::try_from(exact_integer_value(n)?)
                        .map_err(|_| expected!("representable integer literal", &source))?;
                    self.scalar_integer(value, ty, &source)?
                }
                ast::LiteralKind::FloatNumber(_) if ty.is_float() => {
                    let text = source.syntax().text().to_string().replace('_', "");
                    // Like the existing constant frontend, source float
                    // literals are binary64; narrowing is an explicit IR node.
                    let value = text
                        .parse::<f64>()
                        .map_err(|_| expected!("binary64 literal", &source))?;
                    float_value(value, ty, &source)?
                }
                ast::LiteralKind::IntNumber(n) if ty.is_float() => {
                    let value = i128::try_from(exact_integer_value(n)?)
                        .map_err(|_| expected!("integer literal in supported range", &source))?;
                    if ty.width() == 32 {
                        E::Float32((value as f32).to_bits())
                    } else {
                        E::Float64((value as f64).to_bits())
                    }
                }
                _ => {
                    return Err(expected!(
                        "numeric literal of matching scalar type",
                        &source
                    ));
                }
            },
            Expr::PrefixExpr(p) if matches!(p.op_kind(), Some(ast::UnaryOp::Not)) => {
                let ScalarType::Int { width, signed } = ty else {
                    return Err(expected!("an integer bitwise operand", &p));
                };
                let left = self.scalar_expr_depth(
                    p.expr()
                        .ok_or_else(|| expected!("complement operand", &p))?,
                    ty,
                    depth + 1,
                )?;
                // Complement is XOR with the same-width all-ones word.
                let right = self.ids.node(ScalarExprData {
                    ty,
                    kind: E::Integer(if signed { -1 } else { (1i128 << width) - 1 }),
                });
                E::Binary {
                    op: A::BitXor,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            }
            Expr::PrefixExpr(p) if matches!(p.op_kind(), Some(ast::UnaryOp::Neg)) => {
                let arg = p.expr().ok_or_else(|| expected!("negation operand", &p))?;
                // Admit -2^(n-1) without first rejecting its positive magnitude.
                if !ty.is_float()
                    && let Expr::Literal(ref lit) = arg
                    && let ast::LiteralKind::IntNumber(n) = lit.kind()
                {
                    let value = i128::try_from(-exact_integer_value(n)?)
                        .map_err(|_| expected!("representable negative integer", &source))?;
                    self.scalar_integer(value, ty, &source)?
                } else {
                    E::Neg(Box::new(self.scalar_expr_depth(arg, ty, depth + 1)?))
                }
            }
            Expr::BinExpr(b) => {
                if let Some(ast::BinaryOp::ArithOp(op @ (ast::ArithOp::Shl | ast::ArithOp::Shr))) =
                    b.op_kind()
                {
                    let left = self.scalar_expr_depth(
                        b.lhs().ok_or_else(|| expected!("shift operand", &b))?,
                        ty,
                        depth + 1,
                    )?;
                    return self.lower_unsigned_shift(
                        left,
                        b.rhs().ok_or_else(|| expected!("shift count", &b))?,
                        op,
                        &b,
                    );
                }
                let Some(ast::BinaryOp::ArithOp(op)) = b.op_kind() else {
                    return Err(unsupported!("scalar numeric operator", &b));
                };
                let op = arithmetic(op, ty, &b)?;
                let left = self.scalar_expr_depth(
                    b.lhs().ok_or_else(|| expected!("left operand", &b))?,
                    ty,
                    depth + 1,
                )?;
                let right = self.scalar_expr_depth(
                    b.rhs().ok_or_else(|| expected!("right operand", &b))?,
                    ty,
                    depth + 1,
                )?;
                E::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            }
            _ => return Err(unsupported!("scalar numeric expression", &source)),
        };
        let result = self.ids.node(ScalarExprData { ty, kind });
        Ok(if requested.is_float() {
            self.float_convert(result, requested)
        } else {
            result
        })
    }

    fn lower_unsigned_shift<T: AstNode>(
        &mut self,
        left: ScalarExpr,
        count: Expr,
        op: ast::ArithOp,
        source: &T,
    ) -> Result<ScalarExpr, FrontendError> {
        let ty = left.ty;
        if !matches!(ty, ScalarType::Int { signed: false, .. }) {
            return Err(unsupported!(
                "runtime signed shift (only closed nonnegative signed shifts are supported)",
                source
            ));
        }
        let count = self
            .with_known_scalars(|this| this.static_integer(count, false))?
            .value;
        let factor = ty
            .checked_integer_shift(true, 1, count)
            .map_err(|_| expected!("a nonnegative static integer shift count", source))?;
        // k >= width gives zero, but retain evaluation of the entire operand
        // via multiplication, including its reads and definedness conditions.
        let operation = if op == ast::ArithOp::Shl || factor == 0 {
            A::Mul
        } else {
            A::Div
        };
        let right = self.ids.node(ScalarExprData {
            ty,
            kind: E::Integer(factor),
        });
        Ok(self.ids.node(ScalarExprData {
            ty,
            kind: E::Binary {
                op: operation,
                left: Box::new(left),
                right: Box::new(right),
            },
        }))
    }

    fn scalar_integer(
        &self,
        value: i128,
        ty: ScalarType,
        source: &Expr,
    ) -> Result<E, FrontendError> {
        if !ty.contains_integer(value) {
            return Err(expected!(
                "integer literal representable at declared width",
                source
            ));
        }
        Ok(E::Integer(value))
    }

    pub(super) fn lower_scalar_compound(
        &mut self,
        assignment: ast::BinExpr,
        target: SymbolId,
        ty: ScalarType,
    ) -> Result<Statement, FrontendError> {
        let Some(ast::BinaryOp::Assignment { op: Some(op) }) = assignment.op_kind() else {
            return Err(unsupported!("scalar compound operator", &assignment));
        };
        if matches!(op, ast::ArithOp::Shl | ast::ArithOp::Shr) {
            let left = self.ids.node(ScalarExprData {
                ty,
                kind: E::Read(target),
            });
            let value = self.lower_unsigned_shift(
                left,
                assignment
                    .rhs()
                    .ok_or_else(|| expected!("shift count", &assignment))?,
                op,
                &assignment,
            )?;
            return Ok(self.ids.node(StatementKind::ScalarAssign { target, value }));
        }
        let op = arithmetic(op, ty, &assignment)?;
        let operation_ty = if ty.is_float() {
            let rhs_ty = self.float_expression_type(&Expr::BinExpr(assignment.clone()), ty)?;
            ScalarType::Float {
                width: ty.width().max(rhs_ty.width()),
            }
        } else {
            ty
        };
        let right = self.lower_scalar_expr(
            assignment
                .rhs()
                .ok_or_else(|| expected!("scalar assignment value", &assignment))?,
            operation_ty,
        )?;
        let left = self.ids.node(ScalarExprData {
            ty,
            kind: E::Read(target),
        });
        let left = if ty.is_float() {
            self.float_convert(left, operation_ty)
        } else {
            left
        };
        let value = self.ids.node(ScalarExprData {
            ty: operation_ty,
            kind: E::Binary {
                op,
                left: Box::new(left),
                right: Box::new(right),
            },
        });
        let value = if ty.is_float() {
            self.float_convert(value, ty)
        } else {
            value
        };
        Ok(self.ids.node(StatementKind::ScalarAssign { target, value }))
    }

    pub(super) fn lower_scalar_comparison(
        &mut self,
        binary: ast::BinExpr,
    ) -> Result<ClassicalExpr, FrontendError> {
        let ty = self
            .scalar_hint(&Expr::BinExpr(binary.clone()))?
            .unwrap_or(ScalarType::Float { width: 64 });
        let ty = if ty.is_float() {
            self.float_expression_type(&Expr::BinExpr(binary.clone()), ty)?
        } else {
            ty
        };
        let left = self.lower_scalar_expr(
            binary
                .lhs()
                .ok_or_else(|| expected!("comparison operand", &binary))?,
            ty,
        )?;
        let right = self.lower_scalar_expr(
            binary
                .rhs()
                .ok_or_else(|| expected!("comparison operand", &binary))?,
            ty,
        )?;
        let op = match binary.op_kind() {
            Some(ast::BinaryOp::CmpOp(ast::CmpOp::Eq { negated: false })) => C::Eq,
            Some(ast::BinaryOp::CmpOp(ast::CmpOp::Eq { negated: true })) => C::Ne,
            Some(ast::BinaryOp::CmpOp(ast::CmpOp::Ord {
                ordering: ast::Ordering::Less,
                strict: true,
            })) => C::Lt,
            Some(ast::BinaryOp::CmpOp(ast::CmpOp::Ord {
                ordering: ast::Ordering::Less,
                strict: false,
            })) => C::Le,
            Some(ast::BinaryOp::CmpOp(ast::CmpOp::Ord {
                ordering: ast::Ordering::Greater,
                strict: true,
            })) => C::Gt,
            Some(ast::BinaryOp::CmpOp(ast::CmpOp::Ord {
                ordering: ast::Ordering::Greater,
                strict: false,
            })) => C::Ge,
            _ => return Err(unsupported!("scalar comparison", &binary)),
        };
        if let (Some(a), Some(b)) = (
            left.constant_value()
                .map_err(|_| unsupported!("constant comparison", &binary))?,
            right
                .constant_value()
                .map_err(|_| unsupported!("constant comparison", &binary))?,
        ) {
            return Ok(self
                .ids
                .node(ClassicalExprKind::Bool(op.compare(a, b).ok_or_else(
                    || expected!("compatible comparison operands", &binary),
                )?)));
        }
        // Ordinary scalar reads stay executable elsewhere. A comparison can
        // additionally specialize from current flow facts, using the SAME
        // typed evaluator (including each IEEE rounding step), not host math.
        if let (Some(a), Some(b)) = (
            self.known_scalars.value(&left)?,
            self.known_scalars.value(&right)?,
        ) {
            return Ok(self
                .ids
                .node(ClassicalExprKind::Bool(op.compare(a, b).ok_or_else(
                    || expected!("compatible comparison operands", &binary),
                )?)));
        }
        Ok(self.ids.node(ClassicalExprKind::ScalarCompare {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }))
    }
}

pub(super) fn arithmetic<T: AstNode>(
    op: ast::ArithOp,
    ty: ScalarType,
    source: &T,
) -> Result<A, FrontendError> {
    match op {
        ast::ArithOp::Add => Ok(A::Add),
        ast::ArithOp::Sub => Ok(A::Sub),
        ast::ArithOp::Mul => Ok(A::Mul),
        ast::ArithOp::Div => Ok(A::Div),
        ast::ArithOp::Rem if !ty.is_float() => Ok(A::Rem),
        ast::ArithOp::BitAnd if !ty.is_float() => Ok(A::BitAnd),
        ast::ArithOp::BitOr if !ty.is_float() => Ok(A::BitOr),
        ast::ArithOp::BitXor if !ty.is_float() => Ok(A::BitXor),
        _ => Err(unsupported!("scalar arithmetic operator", source)),
    }
}

fn float_value(value: f64, ty: ScalarType, source: &Expr) -> Result<E, FrontendError> {
    if !value.is_finite() {
        return Err(expected!("finite scalar float literal", source));
    }
    Ok(if ty.width() == 32 {
        E::Float32((value as f32).to_bits())
    } else {
        E::Float64(value.to_bits())
    })
}
