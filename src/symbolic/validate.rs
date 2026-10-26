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
    let flow = validate_block(&program.body, BTreeSet::new())?;
    let assigned = meet(flow.finish().map_err(SymbolicError::UnsupportedConstruct)?).unwrap_or_default();
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
) -> Result<iqir::ExecutionFlow<BTreeSet<ClassicalBit>>, SymbolicError> {
    let mut exits = iqir::ExecutionFlow::normal(Vec::new());
    let mut reachable = true;
    for statement in &block.statements {
        if !reachable { break; }
        match &statement.kind {
            StatementKind::Break => { exits.breaks.push(assigned.clone()); reachable = false; }
            StatementKind::Continue => { exits.continues.push(assigned.clone()); reachable = false; }
            StatementKind::LoopBody { .. } => return Err(SymbolicError::UnsupportedConstruct("runtime for update")),
            StatementKind::UnrolledLoop { iterations } => {
                let mut normal = Some(assigned.clone());
                let mut done = Vec::new();
                for body in iterations {
                    let Some(entry) = normal.take() else { break; };
                    let mut flow = validate_block(body, entry)?;
                    done.append(&mut flow.breaks);
                    flow.resume_continue();
                    normal = meet(flow.normal);
                }
                done.extend(normal);
                match meet(done) { Some(a) => assigned = a, None => reachable = false }
            }
            StatementKind::While { .. }
            | StatementKind::ScalarDeclare { .. }
            | StatementKind::ScalarAssign { .. }
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
                let mut flow = match constant_boolean(condition) {
                    Some(true) => validate_block(then_branch, assigned)?,
                    Some(false) => validate_block(else_branch, assigned)?,
                    None => {
                        let mut yes = validate_block(then_branch, assigned.clone())?;
                        yes.append(validate_block(else_branch, assigned)?);
                        yes
                    }
                };
                assigned = meet(std::mem::take(&mut flow.normal)).unwrap_or_else(|| {
                    reachable = false; BTreeSet::new()
                });
                exits.append(flow);
            }
            StatementKind::Scope(body) => {
                let mut flow = validate_block(body, assigned)?;
                assigned = meet(std::mem::take(&mut flow.normal)).unwrap_or_else(|| {
                    reachable = false; BTreeSet::new()
                });
                exits.append(flow);
            }
            StatementKind::Reset(_) | StatementKind::Apply { .. } => {}
        }
    }

    if reachable { exits.normal.push(assigned); }
    for assigned in exits.states_mut() {
    for register in &block.classical_registers {
        for index in 0..register.width {
            assigned.remove(&ClassicalBit {
                register: register.id,
                index,
            });
        }
    }
    }
    Ok(exits)
}

fn meet(mut states: Vec<BTreeSet<ClassicalBit>>) -> Option<BTreeSet<ClassicalBit>> {
    let mut result = states.pop()?;
    for state in states { result.retain(|b| state.contains(b)); }
    Some(result)
}

fn constant_boolean(expression: &ClassicalExpr) -> Option<bool> {
    match &expression.kind {
        ClassicalExprKind::Bool(value) => Some(*value),
        ClassicalExprKind::Bit(_) | ClassicalExprKind::ScalarCompare { .. } => None,
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
        ClassicalExprKind::ScalarCompare { .. } => {
            Err(SymbolicError::UnsupportedConstruct("scalar comparison"))
        }
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
