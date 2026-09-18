//! Constant-width unsigned storage lowers to the existing Boolean word IR.
//! A constant width does not make the stored value a compile-time constant.
use super::*;

impl Lowerer {
    pub(super) fn uint_storage_type(&self, ty: &ast::ScalarType) -> Result<BitType, FrontendError> {
        // Irene's target default is 32 bits, not an OpenQASM-wide default.
        let width = match ty.designator() {
            Some(d) => {
                self.static_index(d.expr().ok_or_else(|| expected!("a uint width", ty))?, true)?
            }
            None => static_integer::DEFAULT_INTEGER_WIDTH as usize,
        };
        if !(1..=64).contains(&width) {
            return Err(unsupported!("uint storage width outside 1..64", ty));
        }
        Ok(BitType::Uint {
            width,
            explicit_width: ty.designator().is_some(),
        })
    }

    pub(super) fn uint_value(
        &mut self,
        rhs: Expr,
        width: usize,
    ) -> Result<Vec<ClassicalExpr>, FrontendError> {
        // Static expressions and constants may initialize any representable
        // uint width; they are never silently truncated or reinterpreted.
        if let Ok(value) = self.static_integer(rhs.clone(), false) {
            return self.integer_literal_bits(
                BigInt::from(value.value),
                width,
                Signedness::Unsigned,
                &rhs,
            );
        }
        match self.lower_typed_classical_expr(rhs.clone())? {
            TypedClassicalExpr::IntegerLiteral(value) => {
                self.integer_literal_bits(value, width, Signedness::Unsigned, &rhs)
            }
            TypedClassicalExpr::Integer {
                bits,
                signedness: Signedness::Unsigned,
                ..
            } if bits.len() == width => Ok(bits),
            _ => Err(expected!(
                "an unsigned integer of matching width or a representable static integer",
                &rhs
            )),
        }
    }

    pub(super) fn uint_compound_assignment(
        &mut self,
        targets: BitOperand,
        assignment: ast::BinExpr,
    ) -> Result<Statement, FrontendError> {
        let lhs = assignment
            .lhs()
            .ok_or_else(|| expected!("a uint target", &assignment))?;
        let rhs = assignment
            .rhs()
            .ok_or_else(|| expected!("a uint operand", &assignment))?;
        let Some(ast::BinaryOp::Assignment { op: Some(op) }) = assignment.op_kind() else {
            return Err(unsupported!("uint compound assignment", &assignment));
        };
        let value = if matches!(op, ast::ArithOp::Shl | ast::ArithOp::Shr) {
            self.uint_shift(op, lhs, rhs, &assignment)?
        } else if matches!(
            op,
            ast::ArithOp::BitAnd | ast::ArithOp::BitOr | ast::ArithOp::BitXor
        ) {
            let left = self.bit_operand_expr(targets.clone());
            let right = self.lower_typed_classical_expr(rhs)?;
            self.lower_bitwise_expr(op, left, right, &assignment)?
        } else {
            return Err(unsupported!("uint arithmetic assignment", &assignment));
        };
        let TypedClassicalExpr::Integer { bits, .. } = value else {
            unreachable!()
        };
        Ok(self.assign_cells(targets.into_cells(), bits))
    }

    pub(super) fn uint_shift<T: AstNode>(
        &mut self,
        op: ast::ArithOp,
        lhs: Expr,
        rhs: Expr,
        source: &T,
    ) -> Result<TypedClassicalExpr, FrontendError> {
        // Discard temporary AST IDs before owning only
        // the final expression. All reads (even shifted-out bits) are retained.
        let saved = self.ids.clone();
        let result = (|| {
            let TypedClassicalExpr::Integer {
                bits,
                signedness: Signedness::Unsigned,
                explicit_width: true,
            } = self.lower_typed_classical_expr(lhs)?
            else {
                return Err(expected!("an explicitly sized uint shift operand", source));
            };
            let shift = usize::try_from(self.static_integer(rhs, false)?.value)
                .map_err(|_| expected!("a non-negative static shift", source))?;
            Ok(self.shift_word(bits, op, shift))
        })();
        self.ids = saved;
        Ok(TypedClassicalExpr::Integer {
            bits: result?
                .iter()
                .map(|b| self.clone_classical_expr(b))
                .collect(),
            signedness: Signedness::Unsigned,
            explicit_width: true,
        })
    }

    /// Exact logical shift shared by angle and uint. Shifts at least as wide
    /// as the word give zero, but still read the entire initialized source.
    pub(super) fn shift_word(
        &mut self,
        bits: Vec<ClassicalExpr>,
        op: ast::ArithOp,
        shift: usize,
    ) -> Vec<ClassicalExpr> {
        let n = bits.len();
        let mut result: Vec<_> = (0..n)
            .map(|i| {
                let from = if op == ast::ArithOp::Shl {
                    i.checked_sub(shift)
                } else {
                    i.checked_add(shift).filter(|j| *j < n)
                };
                from.map(|j| self.clone_classical_expr(&bits[j]))
                    .unwrap_or_else(|| self.ids.node(ClassicalExprKind::Bool(false)))
            })
            .collect();
        for (j, bit) in bits.iter().enumerate() {
            let discarded = if op == ast::ArithOp::Shl {
                j.checked_add(shift).is_none_or(|k| k >= n)
            } else {
                j < shift
            };
            if discarded {
                let bit = self.clone_classical_expr(bit);
                let zero = self.ids.node(ClassicalExprKind::Bool(false));
                let zero = self.bitwise_scalar(ast::ArithOp::BitAnd, bit, zero);
                let first = result.remove(0);
                result.insert(0, self.bitwise_scalar(ast::ArithOp::BitXor, first, zero));
            }
        }
        result
    }
}
