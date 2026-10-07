//! Well-formedness checks required before output-directed optimization.

use std::collections::BTreeSet;

use crate::ir::{Block, ClassicalBit, ClassicalExpr, ClassicalExprKind, Program, StatementKind};

use super::{OutputSelection, SymbolicError};

mod numeric;
pub(crate) use numeric::numeric_domains;

/// Checks that every classical read has a value on every control-flow path.
///
/// This pass deliberately runs before sliced execution. Otherwise an `if` affecting
/// only dead outputs could be removed together with an invalid read of its
/// condition.
pub(crate) fn definite_assignment(
    program: &Program,
    output_selection: &OutputSelection,
) -> Result<(), SymbolicError> {
    let assigned = validate_block(&program.body, BTreeSet::new())?;
    if let Some(bit) = output_selection.classical.difference(&assigned).next() {
        return Err(SymbolicError::UninitializedClassical(bit.clone()));
    }
    Ok(())
}

/// Propagates definite assignment through one block.
///
/// After `if c { x = 0 } else { x = 1 }`, `x` is assigned because it occurs
/// in both branch results; a write in only one branch does not survive their
/// intersection.
fn validate_block(
    block: &Block,
    mut assigned: BTreeSet<ClassicalBit>,
) -> Result<BTreeSet<ClassicalBit>, SymbolicError> {
    for statement in &block.statements {
        match &statement.kind {
            StatementKind::While { .. }
            | StatementKind::GlobalPhase(_)
            | StatementKind::Unitary { .. } => {
                return Err(SymbolicError::UnsupportedConstruct("this statement kind"));
            }
            StatementKind::Measure { target, .. } => {
                assigned.insert(target.clone());
            }
            StatementKind::Assign { target, value } => {
                require_assigned(value, &assigned)?;
                assigned.insert(target.clone());
            }
            StatementKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                require_assigned(condition, &assigned)?;
                assigned = match constant_boolean(condition) {
                    Some(true) => validate_block(then_branch, assigned)?,
                    Some(false) => validate_block(else_branch, assigned)?,
                    None => {
                        let then_assigned = validate_block(then_branch, assigned.clone())?;
                        let else_assigned = validate_block(else_branch, assigned)?;
                        then_assigned
                            .intersection(&else_assigned)
                            .cloned()
                            .collect()
                    }
                };
            }
            StatementKind::Scope(body) => {
                assigned = validate_block(body, assigned)?;
            }
            StatementKind::Reset(_) | StatementKind::Apply { .. } => {}
        }
    }

    for register in &block.classical_registers {
        for index in 0..register.width {
            assigned.remove(&ClassicalBit {
                register: register.id,
                index,
            });
        }
    }
    Ok(assigned)
}

fn constant_boolean(expression: &ClassicalExpr) -> Option<bool> {
    match &expression.kind {
        ClassicalExprKind::Bool(value) => Some(*value),
        ClassicalExprKind::Bit(_) => None,
        ClassicalExprKind::Not(inner) => Some(!constant_boolean(inner)?),
        ClassicalExprKind::Eq(left, right) => {
            Some(constant_boolean(left)? == constant_boolean(right)?)
        }
        ClassicalExprKind::And(left, right) => {
            Some(constant_boolean(left)? && constant_boolean(right)?)
        }
        ClassicalExprKind::Or(left, right) => {
            Some(constant_boolean(left)? || constant_boolean(right)?)
        }
        ClassicalExprKind::Xor(left, right) => {
            Some(constant_boolean(left)? ^ constant_boolean(right)?)
        }
    }
}

fn require_assigned(
    expression: &ClassicalExpr,
    assigned: &BTreeSet<ClassicalBit>,
) -> Result<(), SymbolicError> {
    match &expression.kind {
        ClassicalExprKind::Bool(_) => Ok(()),
        ClassicalExprKind::Bit(bit) => {
            if assigned.contains(bit) {
                Ok(())
            } else {
                Err(SymbolicError::UninitializedClassical(bit.clone()))
            }
        }
        ClassicalExprKind::Not(inner) => require_assigned(inner, assigned),
        ClassicalExprKind::Eq(left, right)
        | ClassicalExprKind::And(left, right)
        | ClassicalExprKind::Or(left, right)
        | ClassicalExprKind::Xor(left, right) => {
            require_assigned(left, assigned)?;
            require_assigned(right, assigned)
        }
    }
}
