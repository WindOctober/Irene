//! Bounded static integer specialization. Overflow and lossy conversions are
//! refused; floating semantics and mutable integer state are not approximated.
use super::*;

// OpenQASM leaves unspecified integer widths to the target. Irene chooses
// 32 bits for both `int` and `uint`; this is not a language-wide default.
pub(super) const DEFAULT_INTEGER_WIDTH: u32 = 32;

pub(super) struct StaticInteger {
    pub(super) value: i128,
    pub(super) width: Option<u32>,
    pub(super) signed: bool,
    pub(super) explicit_width: bool,
}

impl Lowerer {
    pub(super) fn charge_static_expansion<T: AstNode>(
        &mut self,
        source: &T,
    ) -> Result<(), FrontendError> {
        if self.static_loop_depth > 0 {
            self.static_statements_left = self
                .static_statements_left
                .checked_sub(1)
                .ok_or_else(|| unsupported!("static expansion statement budget", source))?;
        }
        Ok(())
    }
    pub(super) fn static_integer(
        &self,
        expression: Expr,
        require_const: bool,
    ) -> Result<StaticInteger, FrontendError> {
        let mut work = 4096;
        self.static_integer_inner(expression, require_const, 0, &mut work)
    }

    fn static_integer_inner(
        &self,
        expression: Expr,
        require_const: bool,
        depth: usize,
        work: &mut usize,
    ) -> Result<StaticInteger, FrontendError> {
        if depth >= 64 || *work == 0 {
            return Err(unsupported!(
                "static integer expression budget",
                &expression
            ));
        }
        *work -= 1;
        match expression {
            Expr::Literal(literal) => {
                let ast::LiteralKind::IntNumber(number) = literal.kind() else {
                    return Err(expected!("an unsigned integer literal", &literal));
                };
                // Bound the source before arbitrary-precision token conversion.
                if number.to_string().len() > 128 {
                    return Err(unsupported!("static integer literal budget", &literal));
                }
                let value = u64::try_from(exact_integer_value(number)?)
                    .map_err(|_| expected!("a static integer at most 64 bits", &literal))?;
                Ok(StaticInteger {
                    value: i128::from(value),
                    width: None,
                    signed: true,
                    explicit_width: false,
                })
            }
            Expr::Identifier(identifier) => {
                let name = identifier.string();
                let binding = self.scopes.lookup(&name).map_err(scope_error)?;
                let BindingKind::StaticInteger {
                    value,
                    width,
                    is_const,
                    signed,
                    explicit_width,
                } = binding.kind
                else {
                    return Err(expected!("a statically known integer", &identifier));
                };
                if require_const && !is_const {
                    return Err(expected!("a const-typed integer expression", &identifier));
                }
                // Called templates may not capture constants declared after
                // their definition, nor caller-local bindings (ScopeStack).
                if self.scopes.global_static_ids().contains(&binding.id)
                    && self.active_subroutines.iter().any(|index| {
                        !self.subroutines[*index]
                            .static_globals
                            .contains(&binding.id)
                    })
                {
                    return Err(expected!(
                        "a constant visible at subroutine definition",
                        &identifier
                    ));
                }
                Ok(StaticInteger {
                    value,
                    width: Some(width),
                    signed,
                    explicit_width,
                })
            }
            Expr::PrefixExpr(prefix) if matches!(prefix.op_kind(), Some(ast::UnaryOp::Neg)) => {
                let mut value = self.static_integer_inner(
                    prefix
                        .expr()
                        .ok_or_else(|| expected!("an integer operand", &prefix))?,
                    require_const,
                    depth + 1,
                    work,
                )?;
                value.value = value
                    .value
                    .checked_neg()
                    .filter(|v| value.width.is_none_or(|w| fits(*v, w, value.signed)))
                    .ok_or_else(|| unsupported!("static integer negation overflow", &prefix))?;
                Ok(value)
            }
            Expr::ParenExpr(paren) => self.static_integer_inner(
                paren
                    .expr()
                    .ok_or_else(|| expected!("an integer expression", &paren))?,
                require_const,
                depth + 1,
                work,
            ),
            Expr::BinExpr(binary) => {
                let left = self.static_integer_inner(
                    binary
                        .lhs()
                        .ok_or_else(|| expected!("a left integer", &binary))?,
                    require_const,
                    depth + 1,
                    work,
                )?;
                let right = self.static_integer_inner(
                    binary
                        .rhs()
                        .ok_or_else(|| expected!("a right integer", &binary))?,
                    require_const,
                    depth + 1,
                    work,
                )?;
                // Literals use the other operand's admitted type, or Irene's
                // signed machine integer for a literal-only expression.
                // Mixed signed/unsigned typed arithmetic needs additional
                // conversion rules and is conservatively refused here.
                if left.width.is_some() && right.width.is_some() && left.signed != right.signed {
                    return Err(unsupported!(
                        "mixed signed/unsigned static arithmetic",
                        &binary
                    ));
                }
                let signed = if left.width.is_some() {
                    left.signed
                } else if right.width.is_some() {
                    right.signed
                } else {
                    true
                };
                let width = left
                    .width
                    .into_iter()
                    .chain(right.width)
                    .max()
                    .unwrap_or(DEFAULT_INTEGER_WIDTH);
                if !fits(left.value, width, signed) || !fits(right.value, width, signed) {
                    return Err(unsupported!(
                        "static integer promotion outside admitted range",
                        &binary
                    ));
                }
                if signed
                    && left.value == -(1_i128 << (width - 1))
                    && right.value == -1
                    && matches!(
                        binary.op_kind(),
                        Some(ast::BinaryOp::ArithOp(
                            ast::ArithOp::Div | ast::ArithOp::Rem
                        ))
                    )
                {
                    return Err(unsupported!("static signed division overflow", &binary));
                }
                let value = match binary.op_kind() {
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Add)) => {
                        left.value.checked_add(right.value)
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Sub)) => {
                        left.value.checked_sub(right.value)
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Mul)) => {
                        left.value.checked_mul(right.value)
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Div)) => {
                        left.value.checked_div(right.value)
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Rem)) => {
                        left.value.checked_rem(right.value)
                    }
                    _ => return Err(unsupported!("static integer operator", &binary)),
                }
                .filter(|value| fits(*value, width, signed))
                .ok_or_else(|| {
                    unsupported!(
                        "static integer overflow, underflow or zero divisor",
                        &binary
                    )
                })?;
                // On this no-overflow subset, widening integer
                // promotions cannot change the mathematical result. A source
                // overflow is refused rather than interpreted as exact integers.
                Ok(StaticInteger {
                    value,
                    width: Some(width),
                    signed,
                    explicit_width: left.explicit_width && right.explicit_width,
                })
            }
            other => Err(unsupported!("static integer expression", &other)),
        }
    }

    fn static_integer_width(&self, ty: &ast::ScalarType) -> Result<u32, FrontendError> {
        if ty.uint_token().is_none() && ty.int_token().is_none() {
            return Err(unsupported!("static type other than int/uint", ty));
        }
        let Some(designator) = ty.designator() else {
            return Ok(DEFAULT_INTEGER_WIDTH);
        };
        let width = self
            .static_integer(
                designator
                    .expr()
                    .ok_or_else(|| expected!("an integer width", &designator))?,
                true,
            )?
            .value;
        if !(1..=64).contains(&width) {
            return Err(unsupported!("static integer width outside 1..64", ty));
        }
        Ok(width as u32)
    }

    pub(super) fn lower_static_constant(
        &mut self,
        declaration: ast::ClassicalDeclarationStatement,
    ) -> Result<(), FrontendError> {
        self.charge_static_expansion(&declaration)?;
        let ty = declaration
            .scalar_type()
            .ok_or_else(|| expected!("a static integer type", &declaration))?;
        if ty.int_token().is_none() && ty.uint_token().is_none() {
            return Err(unsupported!("const type other than int/uint", &declaration));
        }
        let width = self.static_integer_width(&ty)?;
        let signed = ty.int_token().is_some();
        let value = self
            .static_integer(
                declaration
                    .expr()
                    .ok_or_else(|| expected!("a const initializer", &declaration))?,
                true,
            )?
            .value;
        if !fits(value, width, signed) {
            return Err(unsupported!(
                "lossy static integer initialization",
                &declaration
            ));
        }
        self.scopes
            .declare(
                declaration_name(&declaration)?,
                BindingKind::StaticInteger {
                    value,
                    width,
                    signed,
                    explicit_width: ty.designator().is_some(),
                    is_const: true,
                },
            )
            .map_err(scope_error)?;
        Ok(())
    }

    pub(super) fn static_index(
        &self,
        expression: Expr,
        require_const: bool,
    ) -> Result<usize, FrontendError> {
        let value = self.static_integer(expression.clone(), require_const)?;
        // Do not change the old literal admission; bound newly expanded forms.
        if !matches!(expression, Expr::Literal(_)) && value.value > 65536 {
            return Err(unsupported!(
                "expanded static width/index budget",
                &expression
            ));
        }
        usize::try_from(value.value).map_err(|_| expected!("a representable index", &expression))
    }

    fn static_width(
        &self,
        designator: ast::Designator,
        expected_width: &'static str,
    ) -> Result<usize, FrontendError> {
        let width = self.static_index(
            designator
                .expr()
                .ok_or_else(|| expected!(expected_width, &designator))?,
            true,
        )?;
        if width == 0 {
            return Err(expected!("a positive register width", &designator));
        }
        Ok(width)
    }

    pub(super) fn static_quantum_type(
        &self,
        designator: Option<ast::Designator>,
        expected_width: &'static str,
    ) -> Result<QuantumType, FrontendError> {
        match designator {
            Some(designator) => Ok(QuantumType::Register {
                width: self.static_width(designator, expected_width)?,
            }),
            None => Ok(QuantumType::Scalar),
        }
    }

    pub(super) fn static_bit_type(
        &self,
        designator: Option<ast::Designator>,
        expected_width: &'static str,
    ) -> Result<BitType, FrontendError> {
        match designator {
            Some(designator) => Ok(BitType::Register {
                width: self.static_width(designator, expected_width)?,
            }),
            None => Ok(BitType::Bit),
        }
    }

    fn static_range(&self, range: &ast::RangeExpr) -> Result<(i128, i128, i128), FrontendError> {
        // Inspect delimiters too: the dependency's helper alone does not
        // distinguish omitted range operands. Refuse all open-ended ranges.
        let colon_count = range
            .syntax()
            .children_with_tokens()
            .filter(|element| element.as_token().is_some_and(|token| token.text() == ":"))
            .count();
        let count = range.syntax().children().filter_map(Expr::cast).count();
        if !(colon_count == 1 || colon_count == 2) || count != colon_count + 1 {
            return Err(unsupported!("open-ended static range", range));
        }
        let (start, step, stop) = range.start_step_stop();
        let start = self
            .static_integer(
                start.ok_or_else(|| expected!("a range start", range))?,
                false,
            )?
            .value;
        let stop = self
            .static_integer(stop.ok_or_else(|| expected!("a range stop", range))?, false)?
            .value;
        let step = step
            .map(|step| self.static_integer(step, false).map(|x| x.value))
            .transpose()?
            .unwrap_or(1);
        if step == 0 || (step > 0 && start > stop) || (step < 0 && start < stop) {
            return Err(unsupported!("zero-step or empty static range", range));
        }
        Ok((start, step, stop))
    }

    pub(super) fn static_quantum_index(
        &self,
        indexed: ast::IndexedIdentifier,
    ) -> Result<QuantumOperand, FrontendError> {
        let (name, expression) = single_index(indexed)?;
        if let Expr::RangeExpr(range) = expression {
            let (start, step, stop) = self.static_range(&range)?;
            let count = ((stop - start) / step)
                .checked_add(1)
                .ok_or_else(|| unsupported!("static quantum slice cardinality", &range))?;
            if count > 65536 {
                return Err(unsupported!("static quantum slice budget", &range));
            }
            let cells = (0..count)
                .map(|i| {
                    let index = usize::try_from(start + i * step)
                        .map_err(|_| expected!("a representable slice index", &range))?;
                    self.checked_qubit(name.clone(), index)
                })
                .collect::<Result<Vec<_>, _>>()?;
            Ok(QuantumOperand::Register(cells))
        } else {
            Ok(QuantumOperand::Scalar(self.checked_qubit(
                name,
                self.static_index(expression, false)?,
            )?))
        }
    }

    pub(super) fn lower_static_for(
        &mut self,
        statement: ast::ForStmt,
    ) -> Result<Statement, FrontendError> {
        let ty = statement
            .scalar_type()
            .ok_or_else(|| expected!("an explicit loop type", &statement))?;
        let width = self.static_integer_width(&ty)?;
        let signed = ty.int_token().is_some();
        let range = statement
            .for_iterable()
            .and_then(|iterable| iterable.range_expr())
            .ok_or_else(|| unsupported!("non-range static iteration", &statement))?;
        let (start, step, stop) = self.static_range(&range)?;
        let count = ((stop - start) / step)
            .checked_add(1)
            .ok_or_else(|| unsupported!("static loop cardinality", &range))?;
        if !fits(start, width, signed) || !fits(stop, width, signed) {
            return Err(unsupported!(
                "lossy static loop range conversion",
                &statement
            ));
        }
        if count > self.static_iterations_left as i128 || self.static_loop_depth >= 32 {
            return Err(unsupported!(
                "shared static iteration/depth budget",
                &statement
            ));
        }
        self.static_iterations_left -= count as usize;
        let name = statement
            .loop_var()
            .ok_or_else(|| expected!("a loop variable", &statement))?
            .string();
        let mut statements = Vec::new();
        self.static_loop_depth += 1;
        let result = (|| {
            for i in 0..count {
                self.scopes.enter(ScopeKind::Block);
                let lowered = (|| {
                    self.scopes
                        .declare(
                            name.clone(),
                            BindingKind::StaticInteger {
                                value: start + i * step,
                                width,
                                signed,
                                explicit_width: ty.designator().is_some(),
                                is_const: false,
                            },
                        )
                        .map_err(scope_error)?;
                    // The iterator and braced body share one source scope.
                    match statement.block_or_stmt() {
                        BlockOrStmt::BlockExpr(block) => self.lower_block_contents(block),
                        BlockOrStmt::Stmt(statement) => {
                            let statement = self.lower_statement(statement)?;
                            Ok(self.ids.node(BlockData {
                                statements: vec![statement],
                                ..BlockData::default()
                            }))
                        }
                    }
                })();
                self.scopes.exit();
                statements.push(self.ids.node(StatementKind::Scope(lowered?)));
            }
            Ok(self.sequence(statements))
        })();
        self.static_loop_depth -= 1;
        result
    }

    pub(super) fn is_integer_expression(&self, expr: &Expr) -> Result<bool, FrontendError> {
        match expr {
            Expr::Literal(l) => Ok(matches!(l.kind(), ast::LiteralKind::IntNumber(_))),
            Expr::Identifier(id) => Ok(matches!(
                self.scopes.lookup(&id.string()).map_err(scope_error)?.kind,
                BindingKind::StaticInteger { .. }
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
}

fn fits(value: i128, width: u32, signed: bool) -> bool {
    if signed {
        let bound = 1_i128 << (width - 1);
        -bound <= value && value < bound
    } else {
        0 <= value && value < (1_i128 << width)
    }
}

pub(super) fn single_index(
    indexed: ast::IndexedIdentifier,
) -> Result<(String, Expr), FrontendError> {
    let name = indexed
        .identifier()
        .map(|identifier| identifier.string())
        .ok_or_else(|| expected!("an indexed identifier name", &indexed))?;
    let mut operators = indexed.index_operators();
    let operator = operators
        .next()
        .ok_or_else(|| expected!("one index", &indexed))?;
    if operators.next().is_some() {
        return Err(unsupported!("multi-dimensional index", &indexed));
    }
    let Some(IndexKind::ExpressionList(list)) = operator.index_kind() else {
        return Err(unsupported!("index set", &operator));
    };
    let mut expressions = list.exprs();
    let expression = expressions
        .next()
        .ok_or_else(|| expected!("one index expression", &list))?;
    if expressions.next().is_some() {
        return Err(unsupported!("multiple indices", &list));
    }
    Ok((name, expression))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn static_expansion_budgets_are_shared_and_refuse_complete_results() {
        let source = "OPENQASM 3.0; include \"stdgates.inc\"; qubit q; for uint[8] i in [0:1] { const uint[8] n=1; bit c; x q; }";
        let lower = |iterations, statements| {
            let parsed = parse_source_string(source, Some("budget.qasm"), None::<&[PathBuf]>);
            let syntax = parsed.syntax_ast().unwrap();
            assert!(syntax.errors().is_empty());
            Lowerer {
                static_iterations_left: iterations,
                static_statements_left: statements,
                ..Lowerer::default()
            }
            .lower(syntax.tree())
        };
        assert!(lower(2, 6).is_ok());
        assert!(lower(1, 6).is_err());
        assert!(lower(2, 5).is_err());
        let nested = format!(
            "OPENQASM 3.0; qubit q; {} reset q; {}",
            (0..33)
                .map(|i| format!("for uint[8] i{i} in [0:0] {{"))
                .collect::<String>(),
            "}".repeat(33)
        );
        assert!(parse_str(&nested, "depth.qasm").is_err());
    }
}
