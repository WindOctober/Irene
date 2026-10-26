//! Fixed-point angles: bit j denotes 2*pi*2^(j-n), not 2^j radians.
//! Keep classical arithmetic modulo 2^n, then lower rotations as a product
//! of commuting, classically guarded exact rotations. No outcome enumeration.
use super::*;
use crate::NumericConstant;

impl Lowerer {
    pub(super) fn angle_width(&self, ty: &ast::ScalarType) -> Result<usize, FrontendError> {
        // Target choice, matching Irene's default classical machine word.
        let n = match ty.designator() {
            None => 32,
            Some(d) => self.static_index(
                d.expr().ok_or_else(|| expected!("an angle width", ty))?,
                true,
            )?,
        };
        // The exact phase evaluator supports dyadic denominators through 2^62.
        // Rz divides an angle by two, so limit angles to 61 bits uniformly.
        if !(1..=61).contains(&n) {
            return Err(unsupported!("angle width outside 1..61", ty));
        }
        Ok(n)
    }

    pub(super) fn is_angle_expression(&self, e: &Expr) -> Result<bool, FrontendError> {
        match e {
            Expr::Identifier(id) => Ok(matches!(
                self.scopes.lookup(&id.string()).map_err(scope_error)?.kind,
                BindingKind::ClassicalBit(BitType::Angle { .. })
                    | BindingKind::StaticBits {
                        ty: BitType::Angle { .. },
                        ..
                    }
            )),
            Expr::CastExpression(c) => {
                Ok(c.scalar_type().is_some_and(|t| t.angle_token().is_some()))
            }
            Expr::ParenExpr(p) => {
                self.is_angle_expression(&p.expr().ok_or_else(|| expected!("an operand", p))?)
            }
            Expr::PrefixExpr(p)
                if matches!(p.op_kind(), Some(ast::UnaryOp::Neg | ast::UnaryOp::Not)) =>
            {
                self.is_angle_expression(&p.expr().ok_or_else(|| expected!("an operand", p))?)
            }
            Expr::BinExpr(b) if matches!(b.op_kind(), Some(ast::BinaryOp::ArithOp(_))) => Ok(self
                .is_angle_expression(&b.lhs().ok_or_else(|| expected!("a left operand", b))?)?
                || self.is_angle_expression(
                    &b.rhs().ok_or_else(|| expected!("a right operand", b))?,
                )?),
            _ => Ok(false),
        }
    }

    pub(super) fn angle_value(
        &mut self,
        e: Expr,
        n: usize,
        cast_bits: bool,
    ) -> Result<TypedClassicalExpr, FrontendError> {
        if self.is_angle_expression(&e)? {
            let TypedClassicalExpr::Angle(bits) = self.lower_angle_expression(e.clone())? else {
                unreachable!()
            };
            if bits.len() != n {
                return Err(unsupported!(
                    "angle conversion between different widths",
                    &e
                ));
            }
            return Ok(TypedClassicalExpr::Angle(bits));
        }
        let bit_source = match &e {
            Expr::Literal(l) => matches!(l.kind(), ast::LiteralKind::BitString(_)),
            Expr::Identifier(id) => matches!(
                self.scopes.lookup(&id.string()).map_err(scope_error)?.kind,
                BindingKind::ClassicalBit(_) | BindingKind::StaticBits { .. }
            ),
            Expr::CastExpression(c) => c.scalar_type().is_some_and(|t| t.bit_token().is_some()),
            Expr::ParenExpr(p) => {
                return self.angle_value(
                    p.expr().ok_or_else(|| expected!("an operand", p))?,
                    n,
                    cast_bits,
                );
            }
            _ => false,
        };
        if cast_bits && bit_source {
            let TypedClassicalExpr::Register(bits) = self.lower_typed_classical_expr(e.clone())?
            else {
                return Err(expected!(
                    "an equally sized bit register for an angle cast",
                    &e
                ));
            };
            if bits.len() != n {
                return Err(expected!(
                    "an equally sized bit register for an angle cast",
                    &e
                ));
            }
            return Ok(TypedClassicalExpr::Angle(bits));
        }
        let (radians, source_width) = self.static_float(e.clone(), 0)?;
        let value = quantize_angle(radians, source_width, n)
            .ok_or_else(|| unsupported!("uncertified float-to-angle rounding", &e))?;
        Ok(self.constant_bits(value, BitType::Angle { width: n }))
    }

    pub(super) fn lower_angle_expression(
        &mut self,
        e: Expr,
    ) -> Result<TypedClassicalExpr, FrontendError> {
        // Arithmetic uses scratch expressions (e.g. discarded carry bits).
        // Allocate permanent IDs only for nodes retained by the final value.
        let saved = self.ids.clone();
        let result = self.lower_angle_expression_inner(e);
        self.ids = saved;
        self.own_angle(result)
    }

    fn own_angle(
        &mut self,
        result: Result<TypedClassicalExpr, FrontendError>,
    ) -> Result<TypedClassicalExpr, FrontendError> {
        let TypedClassicalExpr::Angle(bits) = result? else {
            unreachable!()
        };
        Ok(TypedClassicalExpr::Angle(
            bits.iter().map(|b| self.clone_classical_expr(b)).collect(),
        ))
    }

    fn lower_angle_expression_inner(
        &mut self,
        e: Expr,
    ) -> Result<TypedClassicalExpr, FrontendError> {
        match e {
            Expr::Identifier(id) => {
                let binding = self.scopes.lookup(&id.string()).map_err(scope_error)?;
                match binding.kind {
                    BindingKind::StaticBits {
                        value,
                        ty: ty @ BitType::Angle { .. },
                    } => {
                        self.check_constant_visibility(binding, &id)?;
                        Ok(self.constant_bits(value, ty))
                    }
                    BindingKind::ClassicalBit(ty @ BitType::Angle { .. }) => {
                        Ok(self.bit_operand_expr(bit_operand(binding.id, ty)))
                    }
                    _ => Err(expected!("an angle expression", &id)),
                }
            }
            Expr::CastExpression(c) => {
                let ty = c
                    .scalar_type()
                    .ok_or_else(|| expected!("an angle cast", &c))?;
                let n = self.angle_width(&ty)?;
                self.angle_value(
                    c.expr()
                        .ok_or_else(|| expected!("an angle cast operand", &c))?,
                    n,
                    true,
                )
            }
            Expr::ParenExpr(p) => self
                .lower_angle_expression(p.expr().ok_or_else(|| expected!("an angle operand", &p))?),
            Expr::PrefixExpr(p) => {
                let TypedClassicalExpr::Angle(bits) = self.lower_angle_expression(
                    p.expr().ok_or_else(|| expected!("an angle operand", &p))?,
                )?
                else {
                    unreachable!()
                };
                let bits = match p.op_kind() {
                    Some(ast::UnaryOp::Not) => bits
                        .into_iter()
                        .map(|b| self.ids.node(ClassicalExprKind::Not(Box::new(b))))
                        .collect(),
                    Some(ast::UnaryOp::Neg) => {
                        let zero = (0..bits.len())
                            .map(|_| self.ids.node(ClassicalExprKind::Bool(false)))
                            .collect();
                        self.add_word(zero, bits, true)
                    }
                    _ => return Err(unsupported!("angle unary operator", &p)),
                };
                Ok(TypedClassicalExpr::Angle(bits))
            }
            Expr::BinExpr(b) => {
                let lhs = b
                    .lhs()
                    .ok_or_else(|| expected!("a left angle operand", &b))?;
                let rhs = b
                    .rhs()
                    .ok_or_else(|| expected!("a right angle operand", &b))?;
                let Some(ast::BinaryOp::ArithOp(op)) = b.op_kind() else {
                    return Err(unsupported!("angle operator", &b));
                };
                self.angle_binary(op, lhs, rhs, &b)
            }
            _ => Err(expected!("an angle expression", &e)),
        }
    }

    pub(super) fn angle_binary<T: AstNode>(
        &mut self,
        op: ast::ArithOp,
        lhs: Expr,
        rhs: Expr,
        source: &T,
    ) -> Result<TypedClassicalExpr, FrontendError> {
        let saved = self.ids.clone();
        let result = self.angle_binary_inner(op, lhs, rhs, source);
        self.ids = saved;
        self.own_angle(result)
    }

    fn angle_binary_inner<T: AstNode>(
        &mut self,
        op: ast::ArithOp,
        lhs: Expr,
        rhs: Expr,
        source: &T,
    ) -> Result<TypedClassicalExpr, FrontendError> {
        let TypedClassicalExpr::Angle(left) = self.lower_angle_expression(lhs)? else {
            unreachable!()
        };
        if matches!(op, ast::ArithOp::Shl | ast::ArithOp::Shr) {
            let shift = self.static_integer(rhs, false)?.value;
            let shift = usize::try_from(shift)
                .map_err(|_| expected!("a non-negative static shift", source))?;
            return Ok(TypedClassicalExpr::Angle(self.shift_word(left, op, shift)));
        }
        let TypedClassicalExpr::Angle(right) = self.lower_angle_expression(rhs)? else {
            unreachable!()
        };
        if left.len() != right.len() {
            return Err(expected!("equal-width angle operands", source));
        }
        let result = match op {
            ast::ArithOp::Add | ast::ArithOp::Sub => {
                self.add_word(left, right, op == ast::ArithOp::Sub)
            }
            ast::ArithOp::BitAnd | ast::ArithOp::BitOr | ast::ArithOp::BitXor => left
                .into_iter()
                .zip(right)
                .map(|(a, b)| self.bitwise_scalar(op, a, b))
                .collect(),
            _ => return Err(unsupported!("angle arithmetic operator", source)),
        };
        Ok(TypedClassicalExpr::Angle(result))
    }

    pub(super) fn angle_gate(
        &mut self,
        gate: Gate,
        bits: &[ClassicalExpr],
        qubits: Vec<Qubit>,
    ) -> Statement {
        let n = bits.len();
        let mut statements = Vec::new();
        for (j, bit) in bits.iter().enumerate() {
            let pi = self
                .ids
                .node(NumericExprKind::Constant(NumericConstant::Pi));
            let weight = self.ids.node(NumericExprKind::Rational(BigRational::new(
                BigInt::from(1),
                BigInt::from(1_u64 << (n - j - 1)),
            )));
            let parameter = self
                .ids
                .node(NumericExprKind::Mul(Box::new(pi), Box::new(weight)));
            let apply = self.ids.node(StatementKind::Apply {
                gate,
                parameters: vec![parameter],
                qubits: qubits.clone(),
            });
            let then_block = self.ids.node(BlockData {
                classical_registers: vec![],
                statements: vec![apply],
            });
            let condition = self.clone_classical_expr(bit);
            let else_branch = self.ids.node(BlockData::default());
            statements.push(self.ids.node(StatementKind::If {
                condition,
                then_branch: then_block,
                else_branch,
            }));
        }
        self.sequence(statements)
    }
}

/// OpenQASM float[n] -> angle[m]: use float_n(2*pi) as one turn,
/// round to nearest/even, then reduce modulo 2^m. IEEE inputs and the
/// period are exact rationals here; no intermediate rounding, epsilon or
/// transcendental approximation is needed. The OUTPUT bit weights still
/// denote exact mathematical 2*pi / 2^m, as required for angle values.
fn quantize_angle(radians: f64, source_width: u32, width: usize) -> Option<u64> {
    if !radians.is_finite() || !(1..=61).contains(&width) {
        return None;
    }
    let period = match source_width {
        32 => f64::from(std::f32::consts::TAU),
        64 => std::f64::consts::TAU,
        _ => return None,
    };
    let modulus = BigInt::from(1_u64 << width);
    let scaled = BigRational::from_float(radians.abs())?
        * BigRational::from_integer(modulus.clone())
        / BigRational::from_float(period)?;
    let mut rounded = scaled.numer() / scaled.denom();
    let twice_remainder = (scaled.numer() % scaled.denom()) * BigInt::from(2);
    if twice_remainder > *scaled.denom()
        || (twice_remainder == *scaled.denom()
            && &rounded % BigInt::from(2) != BigInt::from(0))
    {
        rounded += 1;
    }
    if radians.is_sign_negative() {
        rounded = -rounded;
    }
    let residue = ((rounded % &modulus) + &modulus) % &modulus;
    u64::try_from(residue).ok()
}
