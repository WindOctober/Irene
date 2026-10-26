//! Flow facts for evaluating closed calls, not source-level const qualification.
//! Ordinary scalar reads remain in the executable IR. Only consumers requiring
//! concrete values (math calls, casts, closed integer bit operations and gate
//! parameters) see these facts.
use super::*;
use crate::ScalarExpr;

#[derive(Clone, Default)]
pub(super) struct KnownScalars(HashMap<SymbolId, ScalarValue>);

impl KnownScalars {
    pub(super) fn declare(
        &mut self,
        id: SymbolId,
        initializer: Option<&ScalarExpr>,
    ) -> Result<(), FrontendError> {
        let value = initializer.map(|e| self.value(e)).transpose()?.flatten();
        self.0.remove(&id);
        if let Some(value) = value {
            self.0.insert(id, value);
        }
        Ok(())
    }

    pub(super) fn value(&self, expression: &ScalarExpr) -> Result<Option<ScalarValue>, FrontendError> {
        // Unknown values establish no fact; errors must not become unknown.
        expression
            .constant_value_with(&|id| self.0.get(&id).copied())
            .map_err(|reason| FrontendError::ScalarEvaluation {
                reason,
                snippet: format!("known-value propagation at {:?}", expression.ast_id()),
            })
    }

    fn block(&mut self, body: &Block) -> Result<(), FrontendError> {
        for statement in &body.statements {
            self.statement(statement)?;
        }
        for statement in &body.statements {
            if let StatementKind::ScalarDeclare { id, .. } = &statement.kind {
                self.0.remove(id);
            }
        }
        Ok(())
    }

    pub(super) fn statement(&mut self, statement: &Statement) -> Result<(), FrontendError> {
        match &statement.kind {
            StatementKind::ScalarDeclare {
                id, initializer, ..
            } => {
                self.declare(*id, initializer.as_ref())?;
            }
            StatementKind::ScalarAssign { target, value } => {
                let value = self.value(value)?;
                self.0.remove(target);
                if let Some(value) = value {
                    self.0.insert(*target, value);
                }
            }
            StatementKind::If {
                condition,
                then_branch,
                else_branch,
            } => match constants::eval_constant_bit(condition) {
                Some(true) => self.block(then_branch)?,
                Some(false) => self.block(else_branch)?,
                None => {
                    let mut other = self.clone();
                    self.block(then_branch)?;
                    other.block(else_branch)?;
                    self.0.retain(|id, value| other.0.get(id) == Some(value));
                }
            },
            // Preserve only frame facts, irrespective of iteration count.
            StatementKind::While { body, .. } => self.forget_writes(body),
            StatementKind::Scope(body) => self.block(body)?,
            StatementKind::Assign { .. }
            | StatementKind::Measure { .. }
            | StatementKind::Apply { .. }
            | StatementKind::Reset(_)
            | StatementKind::GlobalPhase(_)
            | StatementKind::Unitary { .. } => {}
        }
        Ok(())
    }

    fn forget_writes(&mut self, body: &Block) {
        for s in &body.statements {
            match &s.kind {
                StatementKind::ScalarAssign { target, .. } => {
                    self.0.remove(target);
                }
                StatementKind::ScalarDeclare { id, .. } => {
                    self.0.remove(id);
                }
                StatementKind::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    self.forget_writes(then_branch);
                    self.forget_writes(else_branch);
                }
                StatementKind::While { body, .. } | StatementKind::Scope(body) => {
                    self.forget_writes(body)
                }
                _ => {}
            }
        }
    }
}

impl Lowerer {
    /// Before lowering a back edge, forget possible assignment targets. Names
    /// overapproximate shadowing; scalar references and global mutable captures
    /// by subroutines are not supported by this frontend.
    pub(super) fn forget_loop_scalar_writes(&mut self, statement: &ast::WhileStmt) {
        for node in statement.syntax().descendants() {
            let target = if let Some(assign) = ast::AssignmentStmt::cast(node.clone()) {
                assign.syntax().children().find_map(Expr::cast)
            } else if let Some(binary) = ast::BinExpr::cast(node) {
                if matches!(binary.op_kind(), Some(ast::BinaryOp::Assignment { .. })) {
                    binary.lhs()
                } else {
                    None
                }
            } else {
                None
            };
            if let Some(target) = target {
                for id in target
                    .syntax()
                    .descendants()
                    .filter_map(ast::Identifier::cast)
                {
                    if let Ok(binding) = self.scopes.lookup(&id.string()) {
                        self.known_scalars.0.remove(&binding.id);
                    }
                }
            }
        }
    }

    pub(super) fn with_known_scalars<T>(
        &mut self,
        evaluate: impl FnOnce(&mut Self) -> Result<T, FrontendError>,
    ) -> Result<T, FrontendError> {
        if self.resolving_known_scalars {
            return evaluate(self);
        }
        let scopes = self.scopes.clone();
        self.scopes.supply_scalar_values(&self.known_scalars.0);
        self.resolving_known_scalars = true;
        let result = evaluate(self);
        self.scopes = scopes;
        self.resolving_known_scalars = false;
        result
    }
}
