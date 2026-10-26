//! Preserve loop transfers as control flow, never as program variables.
use super::*;

pub(super) fn has_control(body: &BlockOrStmt) -> bool {
    let root = match body {
        BlockOrStmt::BlockExpr(b) => b.syntax(),
        BlockOrStmt::Stmt(s) => s.syntax(),
    };
    let mut pending = vec![root.clone()];
    while let Some(node) = pending.pop() {
        match Stmt::cast(node.clone()) {
            Some(Stmt::BreakStmt(_) | Stmt::ContinueStmt(_)) => return true,
            Some(Stmt::WhileStmt(_) | Stmt::ForStmt(_) | Stmt::Def(_)) => continue,
            _ => pending.extend(node.children()),
        }
    }
    false
}

impl Lowerer {
    pub(super) fn lower_loop_jump(&mut self, is_break: bool, snippet: String) -> Result<Statement, FrontendError> {
        if self.loop_controls.is_empty() {
            return Err(FrontendError::Expected {
                expected: "break/continue inside the current subroutine's innermost loop",
                snippet,
            });
        }
        Ok(self.ids.node(if is_break { StatementKind::Break } else { StatementKind::Continue }))
    }
}
