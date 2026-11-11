//! Shared structured lowering for runtime wire selection and integer gate power.
//! Source loops remain loops. Wire dispatch is finite in the register width,
//! not in the source iteration count. No no-spec-only semantics live here.
use super::*;
use crate::{ScalarArithmetic as A, ScalarComparison as C, ScalarExpr, ScalarExprKind as E};

impl Lowerer {
    pub(super) fn lower_dynamic_gate(
        &mut self,
        statement: &Stmt,
    ) -> Result<Option<Statement>, FrontendError> {
        let Stmt::ExprStmt(s) = statement else {
            return Ok(None);
        };
        let Some(expression) = s.expr() else {
            return Ok(None);
        };
        let (gate, modified) = match expression {
            Expr::GateCallExpr(g) => (g, None),
            Expr::ModifiedGateCallExpr(m) => {
                let g = m
                    .gate_call_expr()
                    .ok_or_else(|| expected!("gate call", &m))?;
                (g, Some(m))
            }
            _ => return Ok(None),
        };
        if let Some(list) = gate.qubit_list() {
            for operand in list.gate_operands() {
                let GateOperand::IndexedIdentifier(indexed) = operand else {
                    continue;
                };
                let key = u32::from(indexed.syntax().text_range().start());
                if self.quantum_index_overrides.contains_key(&key) {
                    continue;
                }
                let (name, index) = static_integer::single_index(indexed.clone())?;
                if matches!(index, Expr::RangeExpr(_))
                    || self.is_closed_integer_expression(&index)?
                {
                    continue;
                }
                let binding = self.scopes.lookup(&name).map_err(scope_error)?;
                let QuantumOperand::Register(wires) = self.quantum_cells(&name, binding)? else {
                    return Err(expected!(
                        "a quantum register for dynamic indexing",
                        &indexed
                    ));
                };
                if wires.is_empty() || wires.len() > 64 {
                    return Err(unsupported!(
                        "dynamic wire dispatch width outside 1..64",
                        &indexed
                    ));
                }
                self.scopes.enter(ScopeKind::Block);
                let result = self.indexed_gate(statement, key, index, wires);
                self.quantum_index_overrides.remove(&key);
                self.scopes.exit();
                return result.map(Some);
            }
        }
        if let Some(modified) = modified {
            for modifier in modified.modifiers() {
                let ast::Modifier::PowModifier(p) = modifier else {
                    continue;
                };
                let e = p
                    .paren_expr()
                    .and_then(|p| p.expr())
                    .ok_or_else(|| expected!("integer gate power", &p))?;
                let key = u32::from(e.syntax().text_range().start());
                if self.gate_power_overrides.contains_key(&key) {
                    continue;
                }
                // Preserve the existing checked constant/known-bit path.
                if let Ok(k) = self.known_power(e.clone()) {
                    if k == 0 {
                        // Constant zero powers must not erase potentially
                        // undefined numeric parameter evaluation either.
                        if let Some(args) = gate.arg_list().and_then(|a| a.expression_list()) {
                            for parameter in args.exprs() {
                                let ids = self.ids.clone();
                                let lowered = self.lower_numeric_expr(parameter)?;
                                self.ids = ids;
                                if !closed_numeric(&lowered) {
                                    return Err(unsupported!(
                                        "zero gate power with non-closed parameters",
                                        &e
                                    ));
                                }
                            }
                        }
                    }
                    continue;
                }
                self.scopes.enter(ScopeKind::Block);
                let result = self.powered_gate(statement, key, e);
                self.gate_power_overrides.remove(&key);
                self.scopes.exit();
                return result.map(Some);
            }
        }
        Ok(None)
    }

    // Use the existing checked-table IR operation as an executable finite-domain
    // check, not an assumed predicate. Its value is private/unused, but reads and
    // bounds are still evaluated by both the executor and the Rocq source checks.
    fn index_check(
        &mut self,
        index: ScalarExpr,
        length: usize,
    ) -> Result<Statement, FrontendError> {
        let ty = ScalarType::Int {
            width: 1,
            signed: false,
        };
        let table = crate::ConstantTable::new(ty, vec![ScalarValue::Integer(0); length]).unwrap();
        let initializer = self.ids.node(crate::ScalarExprData {
            ty,
            kind: E::TableRead {
                table: std::sync::Arc::new(table),
                index: Box::new(index),
            },
        });
        let (_, decl) = self.for_storage(
            format!("@index.check.{}", initializer.ast_id().index()),
            ty,
            initializer,
            false,
        )?;
        Ok(decl)
    }
    fn indexed_gate(
        &mut self,
        statement: &Stmt,
        key: u32,
        index: Expr,
        wires: Vec<Qubit>,
    ) -> Result<Statement, FrontendError> {
        let ty = self.scalar_hint(&index)?.unwrap_or(ScalarType::Int {
            width: 64,
            signed: true,
        });
        if ty.is_float() {
            return Err(expected!("integer wire index", &index));
        }
        let value = self.lower_scalar_expr(index, ty)?;
        let bounds = self.wire_index_range(&value);
        let (selector, declare) = self.for_storage(format!("@index.{key}"), ty, value, false)?;
        let read = self.for_read(selector, ty);
        let check = self.index_check(read, wires.len())?;
        let mut statements = vec![declare, check];
        for (i, wire) in wires.into_iter().enumerate() {
            if !ty.contains_integer(i as i128) {
                continue;
            }
            if bounds.is_some_and(|(lo, hi)| (i as i128) < lo || (i as i128) > hi) {
                continue;
            }
            self.quantum_index_overrides.insert(key, wire);
            let ids = self.ids.clone();
            let body = match self.lower_statement_inner(statement.clone()) {
                Ok(s) => s,
                Err(FrontendError::Expected {
                    expected: "distinct qubit operands for each gate application",
                    ..
                }) => {
                    // This selection aliases controls/targets. Reject this
                    // execution, not all other (possibly disjoint) selections.
                    self.ids = ids;
                    let guard_ty = if ty
                        == (ScalarType::Int {
                            width: 1,
                            signed: true,
                        }) {
                        ScalarType::Int {
                            width: 64,
                            signed: true,
                        }
                    } else {
                        ty
                    };
                    let read = self.for_read(selector, ty);
                    let read = if guard_ty != ty {
                        self.ids.node(crate::ScalarExprData {
                            ty: guard_ty,
                            kind: E::IntWiden(Box::new(read)),
                        })
                    } else {
                        read
                    };
                    let zero = self.for_literal(0, guard_ty);
                    let zero = self.ids.node(crate::ScalarExprData {
                        ty: guard_ty,
                        kind: E::Binary {
                            op: A::Mul,
                            left: Box::new(read),
                            right: Box::new(zero),
                        },
                    });
                    let one = self.for_literal(1, guard_ty);
                    let invalid = self.ids.node(crate::ScalarExprData {
                        ty: guard_ty,
                        kind: E::Binary {
                            op: A::Add,
                            left: Box::new(zero),
                            right: Box::new(one),
                        },
                    });
                    self.index_check(invalid, 1)?
                }
                Err(e) => return Err(e),
            };
            let then_branch = self.for_block(vec![body]);
            let else_branch = self.for_block(vec![]);
            let left = self.for_read(selector, ty);
            let right = self.for_literal(i as i128, ty);
            let condition = self.ids.node(ClassicalExprKind::ScalarCompare {
                op: C::Eq,
                left: Box::new(left),
                right: Box::new(right),
            });
            statements.push(self.ids.node(StatementKind::If {
                condition,
                then_branch,
                else_branch,
            }));
        }
        let block = self.for_block(statements);
        Ok(self.ids.node(StatementKind::Scope(block)))
    }

    fn wire_index_range(&self, e: &ScalarExpr) -> Option<(i128, i128)> {
        let result = match &e.kind.kind {
            E::Integer(n) => (*n, *n),
            E::Read(id) => *self.immutable_loop_ranges.get(id)?,
            E::IntWiden(a) => self.wire_index_range(a)?,
            E::Neg(a) => {
                let (lo, hi) = self.wire_index_range(a)?;
                (hi.checked_neg()?, lo.checked_neg()?)
            }
            E::Binary { op, left, right } => {
                let (al, ah) = self.wire_index_range(left)?;
                let (bl, bh) = self.wire_index_range(right)?;
                match op {
                    A::Add => (al.checked_add(bl)?, ah.checked_add(bh)?),
                    A::Sub => (al.checked_sub(bh)?, ah.checked_sub(bl)?),
                    _ => return None,
                }
            }
            _ => return None,
        };
        // Never apply mathematical intervals to wrapping machine arithmetic.
        (e.ty.contains_integer(result.0) && e.ty.contains_integer(result.1)).then_some(result)
    }

    fn powered_gate(
        &mut self,
        statement: &Stmt,
        key: u32,
        exponent: Expr,
    ) -> Result<Statement, FrontendError> {
        let ty = self.scalar_hint(&exponent)?.unwrap_or(ScalarType::Int {
            width: 64,
            signed: true,
        });
        let ScalarType::Int { width, signed } = ty else {
            return Err(expected!("integer gate exponent", &exponent));
        };
        let value = self.lower_scalar_expr(exponent.clone(), ty)?;
        let (cursor, declare) = self.for_storage(format!("@power.{key}"), ty, value, false)?;
        let mut branches = vec![];
        for positive in [true, false] {
            if !signed && !positive {
                break;
            }
            self.gate_power_overrides
                .insert(key, if positive { 1 } else { -1 });
            let gate = self.lower_statement_inner(statement.clone())?;
            // A zero exponent must not hide evaluation/definedness of dynamic
            // parameters. Admit only closed, total gate bodies here; otherwise
            // a separate parameter-snapshot lowering is required.
            if !closed_unitary(&gate) {
                return Err(unsupported!(
                    "runtime gate power with non-closed gate parameters",
                    &exponent
                ));
            }
            let tiny = signed && width == 1;
            let left = self.for_read(cursor, ty);
            let right = self.for_literal(if tiny { -1 } else { 1 }, ty);
            let op = if positive != tiny { A::Sub } else { A::Add };
            let value = self.ids.node(crate::ScalarExprData {
                ty,
                kind: E::Binary {
                    op,
                    left: Box::new(left),
                    right: Box::new(right),
                },
            });
            let advance = self.ids.node(StatementKind::ScalarAssign {
                target: cursor,
                value,
            });
            branches.push(self.for_block(vec![gate, advance]));
        }
        let body = if signed {
            let left = self.for_read(cursor, ty);
            let right = self.for_literal(0, ty);
            let condition = self.ids.node(ClassicalExprKind::ScalarCompare {
                op: C::Gt,
                left: Box::new(left),
                right: Box::new(right),
            });
            let choose = self.ids.node(StatementKind::If {
                condition,
                then_branch: branches.remove(0),
                else_branch: branches.remove(0),
            });
            self.for_block(vec![choose])
        } else {
            branches.remove(0)
        };
        let left = self.for_read(cursor, ty);
        let right = self.for_literal(0, ty);
        let condition = self.ids.node(ClassicalExprKind::ScalarCompare {
            op: C::Ne,
            left: Box::new(left),
            right: Box::new(right),
        });
        let repeat = self.ids.node(StatementKind::While { condition, body });
        let block = self.for_block(vec![declare, repeat]);
        Ok(self.ids.node(StatementKind::Scope(block)))
    }
}

fn closed_numeric(e: &NumericExpr) -> bool {
    match &e.kind {
        NumericExprKind::Rational(_) | NumericExprKind::Constant(_) => true,
        NumericExprKind::Neg(a) => closed_numeric(a),
        NumericExprKind::Add(a, b) | NumericExprKind::Sub(a, b) | NumericExprKind::Mul(a, b) => {
            closed_numeric(a) && closed_numeric(b)
        }
        // Division and embedded machine expressions need explicit use-site
        // domains even if their current operands look constant.
        _ => false,
    }
}
fn closed_unitary(s: &Statement) -> bool {
    match &s.kind {
        StatementKind::Apply { parameters, .. } => parameters.iter().all(closed_numeric),
        StatementKind::GateCall {
            definition,
            parameters,
            ..
        } => parameters.is_empty() && definition.body.statements.iter().all(closed_unitary),
        StatementKind::Unitary { body, .. } | StatementKind::Scope(body) => {
            body.statements.iter().all(closed_unitary)
        }
        StatementKind::GlobalPhase(e) => closed_numeric(e),
        _ => false,
    }
}
