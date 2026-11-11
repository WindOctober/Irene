//! Runtime, inclusive +/-1-step ranges use the existing scoped while IR.
//! Snapshot bounds once; a private cursor is unaffected by writes to the
//! source iterator. Never increment the maximum representable final value.
use super::*;
use crate::annotation::{Annotation, AnnotationKind};
use crate::{
    ScalarArithmetic as A, ScalarComparison as C, ScalarExpr, ScalarExprData, ScalarExprKind as E,
};

impl Lowerer {
    pub(super) fn should_unroll_for(&mut self, statement: &ast::ForStmt) -> Result<bool, FrontendError> {
        // Source-only translation preserves every loop, including one-iteration
        // and nested loops. Never fall back to
        // expansion when a runtime body contains an unsupported construct.
        if self.translation_profile || !self.for_range_is_static(statement)? {
            return Ok(false);
        }
        if !self.structured { return Ok(true); }
        let range = statement.for_iterable().and_then(|i| i.range_expr()).unwrap();
        let (start, step, stop) = self.with_known_scalars(|this| this.static_range(&range))?;
        let count = (stop - start) / step + 1;
        Ok(count <= crate::DEFAULT_LOOP_UNROLL_LIMIT as i128
            && count <= self.static_iterations_left as i128)
    }

    pub(super) fn for_range_is_static(
        &mut self,
        statement: &ast::ForStmt,
    ) -> Result<bool, FrontendError> {
        let range = statement
            .for_iterable()
            .and_then(|i| i.range_expr())
            .ok_or_else(|| unsupported!("non-range iteration", statement))?;
        self.with_known_scalars(|this| {
            for expr in range.syntax().children().filter_map(Expr::cast) {
                if !this.is_closed_integer_expression(&expr)? {
                    return Ok(false);
                }
            }
            Ok(true)
        })
    }

    pub(super) fn lower_runtime_for(
        &mut self,
        statement: ast::ForStmt,
        annotations: Vec<Annotation>,
    ) -> Result<Statement, FrontendError> {
        if self.structured
            && !self.translation_profile
            && self.for_range_is_static(&statement)?
            && !self.should_unroll_for(&statement)?
            && !annotations.iter().any(|a| a.kind == AnnotationKind::Invariant)
        {
            return Err(unsupported!(
                "static for exceeds the 10-iteration unrolling limit; provide invariant and exit_state contracts",
                &statement
            ));
        }
        if self.loop_depth >= 64 {
            return Err(unsupported!("loop nesting budget", &statement));
        }
        if annotations.iter().any(|a| {
            matches!(
                a.kind,
                AnnotationKind::GhostDeclare | AnnotationKind::GhostAssign
            )
        }) {
            return Err(unsupported!(
                "ghost declarations/assignments attached to runtime for (use an enclosing scope)",
                &statement
            ));
        }
        let before = self.known_scalars.clone();
        let bits_before = self.known_bits.clone();
        self.scopes.enter(ScopeKind::Block);
        let result = self.runtime_for_inner(statement, annotations);
        self.scopes.exit();
        self.known_scalars = before;
        self.known_bits = bits_before;
        if let Ok(s) = &result {
            self.known_scalars.statement(s)?;
            if let Some(bits) = &mut self.known_bits {
                bits.statement(s);
            }
        }
        result
    }

    fn runtime_for_inner(
        &mut self,
        statement: ast::ForStmt,
        mut annotations: Vec<Annotation>,
    ) -> Result<Statement, FrontendError> {
        let source_ty = statement
            .scalar_type()
            .ok_or_else(|| expected!("integer loop type", &statement))?;
        let ty = self.scalar_type(&source_ty)?;
        if !matches!(ty, ScalarType::Int { .. }) {
            return Err(unsupported!("non-integer runtime for", &statement));
        }
        let range = statement
            .for_iterable()
            .and_then(|i| i.range_expr())
            .ok_or_else(|| unsupported!("non-range iteration", &statement))?;
        let colons = range
            .syntax()
            .children_with_tokens()
            .filter(|e| e.as_token().is_some_and(|t| t.text() == ":"))
            .count();
        let operands = range.syntax().children().filter_map(Expr::cast).count();
        if !matches!(colons, 1 | 2) || operands != colons + 1 {
            return Err(unsupported!("open-ended runtime for range", &range));
        }
        let (start, step, stop) = range.start_step_stop();
        let step = if let Some(step) = step {
            self.with_known_scalars(|this| this.static_integer(step, false))?.value
        } else { 1 };
        if !matches!(step, -1 | 1) {
            return Err(unsupported!("runtime for step other than +1 or -1", &range));
        }
        let descending = step < 0;
        // Evaluate in the enclosing source environment before declaring the
        // iterator, so an outer variable with the same name remains visible.
        let start =
            self.lower_scalar_expr(start.ok_or_else(|| expected!("range start", &range))?, ty)?;
        let stop =
            self.lower_scalar_expr(stop.ok_or_else(|| expected!("range stop", &range))?, ty)?;
        let name = statement
            .loop_var()
            .ok_or_else(|| expected!("loop variable", &statement))?
            .string();
        // Restrict finite wire dispatch only for an iterator never assigned
        // anywhere in this body (including nested branches/loops). This is a
        // consequence of the generated cursor semantics, not a user invariant.
        let immutable_range = if iterator_is_read_only(&statement,&name) {
            match (self.known_scalars.value(&start)?,self.known_scalars.value(&stop)?) {
                (Some(ScalarValue::Integer(a)),Some(ScalarValue::Integer(b))) => Some((a.min(b),a.max(b))),
                _=>None,
            }
        } else {None};
        let flag_ty = ScalarType::Int {
            width: 1,
            signed: false,
        };
        // Retained induction must remember the range's original lower bound,
        // not re-read a source variable which the body may change. Keep this
        // extra snapshot only when a contract selects induction.
        let contract_span = annotations.iter().find(|a| {
            use crate::annotation::{AnnotationPayload as P, SpecExpr as X};
            matches!(a.kind, AnnotationKind::Invariant | AnnotationKind::RankingFunction)
                || (a.kind == AnnotationKind::ExitState
                    && !matches!(&a.payload, P::NoState | P::Expression(X::Bool(true))))
        }).map(|a| a.span.clone());
        let (first, first_decl, start) = if contract_span.is_some() {
            let (id, declaration) = self.for_storage("@for.start".into(), ty, start, false)?;
            (Some(id), Some(declaration), self.for_read(id, ty))
        } else { (None, None, start) };
        let (cursor, cursor_decl) = self.for_storage("@for.cursor".into(), ty, start, false)?;
        let (limit, limit_decl) = self.for_storage("@for.limit".into(), ty, stop, false)?;
        let initial_index = self.for_read(cursor, ty);
        let (index, index_decl) = self.for_storage(name.clone(), ty, initial_index, true)?;
        let zero = self.for_literal(0, flag_ty);
        let (active, active_decl) = self.for_storage("@for.active".into(), flag_ty, zero, false)?;
        if let (Some(first), Some(span)) = (first, contract_span) {
            use crate::annotation::{AnnotationPayload, BinaryOp as B, SpecExpr as X};
            let read = |id, name: &str| X::Symbol { id, name: name.into() };
            let binary = |op, left, right| X::Binary {
                op, left: Box::new(left), right: Box::new(right),
            };
            let cursor = read(cursor, "@for.cursor");
            let limit = read(limit, "@for.limit");
            let enabled = binary(B::Eq, read(active, "@for.active"),
                X::Number(num_rational::BigRational::from_integer(1.into())));
            let disabled = binary(B::Eq, read(active, "@for.active"),
                X::Number(num_rational::BigRational::from_integer(0.into())));
            let clauses = [
                binary(B::Eq, read(index, &name), cursor.clone()),
                binary(if descending { B::Ge } else { B::Le }, read(first, "@for.start"), cursor.clone()),
                binary(B::Implies, enabled, binary(if descending { B::Ge } else { B::Le }, cursor.clone(), limit.clone())),
                binary(B::Implies, disabled, binary(if descending { B::Ge } else { B::Le }, limit, cursor)),
            ];
            // These are checked invariants, not trusted assumptions. All
            // consumers use the ordinary entry/preservation/exit machinery.
            // Iterator equality holds at loop heads, not inside source_body;
            // LoopBody skips the restore step on break, as before.
            annotations.push(Annotation {
                kind: AnnotationKind::Invariant,
                payload: AnnotationPayload::Expression(clauses.into_iter()
                    .reduce(|a,b| binary(B::And,a,b)).unwrap()),
                span, summary_hint: None, proof_group: None, selection: Default::default(),
            });
        }
        let condition = self.for_compare(if descending { C::Ge } else { C::Le }, cursor, limit, ty);
        let one = self.for_literal(1, flag_ty);
        let activate = self.ids.node(StatementKind::ScalarAssign {
            target: active,
            value: one,
        });
        let then_branch = self.for_block(vec![activate]);
        let else_branch = self.for_block(vec![]);
        let activate = self.ids.node(StatementKind::If {
            condition,
            then_branch,
            else_branch,
        });

        // Entry-only constants must not specialize a gate/index on a back edge.
        self.known_scalars = Default::default();
        if self.known_bits.is_some() {
            self.known_bits = Some(Default::default());
        }
        // Source iterator and body declarations share a scope, even though
        // the iterator's IR storage lives in the enclosing loop setup.
        self.scopes.enter_block_with_binding(&name).map_err(scope_error)?;
        self.loop_depth += 1;
        let has_control = loop_control::has_control(&statement.block_or_stmt());
        self.loop_controls.push(());
        if let Some(bounds)=immutable_range {self.immutable_loop_ranges.insert(index,bounds);}
        let body_result = match statement.block_or_stmt() {
            BlockOrStmt::BlockExpr(block) => self.lower_block_contents(block),
            BlockOrStmt::Stmt(s) => self.lower_statement(s).map(|s| self.for_block(vec![s])),
        };
        self.immutable_loop_ranges.remove(&index);
        self.loop_controls.pop();
        self.scopes.exit();
        self.loop_depth -= 1;
        let source_body = self.ids.node(StatementKind::Scope(body_result?));
        let condition = self.for_compare(C::Eq, cursor, limit, ty);
        let zero = self.for_literal(0, flag_ty);
        let deactivate = self.ids.node(StatementKind::ScalarAssign {
            target: active,
            value: zero,
        });
        let then_branch = self.for_block(vec![deactivate]);
        let left = self.for_read(cursor, ty);
        // int[1] cannot represent +1. Subtraction of -1 increments it safely.
        let tiny = ty
            == ScalarType::Int {
                width: 1,
                signed: true,
            };
        let right = self.for_literal(if tiny { -1 } else { 1 }, ty);
        let value = self.ids.node(ScalarExprData {
            ty,
            kind: E::Binary {
                op: if tiny != descending { A::Sub } else { A::Add },
                left: Box::new(left),
                right: Box::new(right),
            },
        });
        let increment = self.ids.node(StatementKind::ScalarAssign {
            target: cursor,
            value,
        });
        let else_branch = self.for_block(vec![increment]);
        let advance = self.ids.node(StatementKind::If {
            condition,
            then_branch,
            else_branch,
        });
        let value = self.for_read(cursor, ty);
        let restore_index = self.ids.node(StatementKind::ScalarAssign {
            target: index,
            value,
        });
        let body = if has_control {
            let source_body = self.for_block(vec![source_body]);
            let step = self.for_block(vec![advance, restore_index]);
            let iteration = self.ids.node(StatementKind::LoopBody { body: source_body, step });
            self.for_block(vec![iteration])
        } else {
            self.for_block(vec![source_body, advance, restore_index])
        };
        let left = self.for_read(active, flag_ty);
        let right = self.for_literal(1, flag_ty);
        let condition = self.ids.node(ClassicalExprKind::ScalarCompare {
            op: C::Eq,
            left: Box::new(left),
            right: Box::new(right),
        });
        let generated = self.ids.node(StatementKind::While { condition, body });
        let generated = if annotations.is_empty() {
            generated
        } else {
            self.lower_annotations(
                annotations,
                Stmt::ForStmt(statement),
                false,
                Some(generated),
            )?
        };
        let mut prefix = first_decl.into_iter().collect::<Vec<_>>();
        prefix.extend([cursor_decl, limit_decl, index_decl, active_decl, activate]);
        prefix.push(generated);
        let block = self.for_block(prefix);
        Ok(self.ids.node(StatementKind::Scope(block)))
    }

    pub(super) fn for_storage(
        &mut self,
        name: String,
        ty: ScalarType,
        initializer: ScalarExpr,
        assignable: bool,
    ) -> Result<(SymbolId, Statement), FrontendError> {
        let binding = self
            .scopes
            .declare(
                name.clone(),
                BindingKind::Scalar {
                    ty,
                    explicit_width: true,
                    is_const: false,
                    assignable,
                    value: None,
                },
            )
            .map_err(scope_error)?;
        let declaration = self.ids.node(StatementKind::ScalarDeclare {
            id: binding.id,
            name,
            ty,
            explicit_width: true,
            initializer: Some(initializer),
        });
        Ok((binding.id, declaration))
    }
    pub(super) fn for_read(&mut self, id: SymbolId, ty: ScalarType) -> ScalarExpr {
        self.ids.node(ScalarExprData {
            ty,
            kind: E::Read(id),
        })
    }
    pub(super) fn for_literal(&mut self, n: i128, ty: ScalarType) -> ScalarExpr {
        self.ids.node(ScalarExprData {
            ty,
            kind: E::Integer(n),
        })
    }
    fn for_compare(&mut self, op: C, a: SymbolId, b: SymbolId, ty: ScalarType) -> ClassicalExpr {
        let left = self.for_read(a, ty);
        let right = self.for_read(b, ty);
        self.ids.node(ClassicalExprKind::ScalarCompare {
            op,
            left: Box::new(left),
            right: Box::new(right),
        })
    }
    pub(super) fn for_block(&mut self, statements: Vec<Statement>) -> Block {
        self.ids.node(BlockData {
            statements,
            ..BlockData::default()
        })
    }
}

fn iterator_is_read_only(statement:&ast::ForStmt,name:&str)->bool {
    !statement.syntax().descendants().any(|node| {
        // Calls cannot mutate caller scalars in the admitted language, but
        // conservatively avoid relying on that restriction for this optimization.
        if ast::CallExpr::cast(node.clone()).is_some() {return true;}
        let target=if let Some(a)=ast::AssignmentStmt::cast(node.clone()) {
            a.syntax().children().find_map(Expr::cast)
        } else if let Some(b)=ast::BinExpr::cast(node) {
            if matches!(b.op_kind(),Some(ast::BinaryOp::Assignment{..})) {b.lhs()}else{None}
        } else {None};
        target.is_some_and(|t|t.syntax().descendants().filter_map(ast::Identifier::cast).any(|id|id.string()==name))
    })
}
