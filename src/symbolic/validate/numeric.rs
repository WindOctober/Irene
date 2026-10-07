//! Bounded sufficient real-domain check BEFORE slicing or scalar/phase algebra.
//! Finite rational intervals certify nonzero denominators; an inconclusive
//! interval refuses rather than assuming a unit. Both operands and all source
//! branches are visited, even when a later zero/guard/slice would erase them.
//! This does not implement target-specific finite-width floating arithmetic.

use num_rational::BigRational;

use crate::ir::{
    Block, ClassicalExpr, ClassicalExprKind, NumericConstant, NumericExpr, NumericExprKind,
    Program, StatementKind,
};
use crate::symbolic::SymbolicError;

// TODO: Revisit these temporary fixed caps. Profile their checking overhead
// and remove redundant limits once resource control is handled elsewhere.
// These are resource guards, not semantic restrictions; removing the depth
// cap requires stack-safe traversal, and large intervals still need memory
// protection. Do not assume that omitting the checks makes validation cheaper.
const MAX_WORK: usize = 1_000_000;
const MAX_DEPTH: usize = 128;
const MAX_BITS: u64 = 4096;
type Interval = (BigRational, BigRational);
type CheckedInterval = Result<Option<Interval>, SymbolicError>;

fn error(reason: &'static str) -> SymbolicError {
    SymbolicError::NumericDomain(reason)
}

fn spend(work: &mut usize) -> Result<(), SymbolicError> {
    *work = work
        .checked_sub(1)
        .ok_or_else(|| error("source work bound"))?;
    Ok(())
}

fn bounded(value: Interval) -> CheckedInterval {
    if [&value.0, &value.1]
        .iter()
        .any(|r| r.numer().bits() > MAX_BITS || r.denom().bits() > MAX_BITS)
    {
        return Err(error("rational interval bit bound"));
    }
    Ok(Some(value))
}

fn integer(n: i32) -> BigRational {
    BigRational::from_integer(n.into())
}

fn product(a: Interval, b: Interval) -> Interval {
    let values = [&a.0 * &b.0, &a.0 * &b.1, &a.1 * &b.0, &a.1 * &b.1];
    (
        values.iter().min().unwrap().clone(),
        values.iter().max().unwrap().clone(),
    )
}

fn expression(source: &NumericExpr, work: &mut usize, depth: usize) -> CheckedInterval {
    spend(work)?;
    if depth >= MAX_DEPTH {
        return Err(error("numeric expression depth bound"));
    }
    match &source.kind {
        NumericExprKind::Rational(r) => {
            if r.numer().bits() > MAX_BITS || r.denom().bits() > MAX_BITS {
                return Err(error("rational source bit bound"));
            }
            bounded((r.clone(), r.clone()))
        }
        NumericExprKind::Constant(c) => {
            // Deliberately loose, exact bounds for the named real constants.
            let (low, high) = match c {
                NumericConstant::Pi => (3, 4),
                NumericConstant::Tau => (6, 8),
                NumericConstant::Euler => (2, 3),
            };
            bounded((integer(low), integer(high)))
        }
        // Inputs have the executor's formal-real domain, but no known range.
        // The equivalence interface separately refuses numeric input pairs.
        NumericExprKind::Input(_) => Ok(None),
        NumericExprKind::Neg(a) => match expression(a, work, depth + 1)? {
            Some((low, high)) => bounded((-high, -low)),
            None => Ok(None),
        },
        NumericExprKind::Add(a, b)
        | NumericExprKind::Sub(a, b)
        | NumericExprKind::Mul(a, b)
        | NumericExprKind::Div(a, b) => {
            // Always recurse into BOTH original operands before algebra.
            let a = expression(a, work, depth + 1)?;
            let b = expression(b, work, depth + 1)?;
            if matches!(source.kind, NumericExprKind::Div(_, _)) {
                // TODO: Replace this temporary, conservative interval-only gate
                // with nonzero proofs that can use algebraic facts or explicit
                // input assumptions. It may reject a genuinely nonzero divisor;
                // failure to prove nonzero does not prove division by zero.
                let b = b.ok_or_else(|| error("divisor lacks a proved nonzero range"))?;
                if b.0 <= integer(0) && b.1 >= integer(0) {
                    return Err(error("divisor range includes zero"));
                }
                // On either a positive or negative interval, 1/x reverses
                // the endpoints. No potentially-zero denominator is inverted.
                let inverse = (b.1.recip(), b.0.recip());
                return match a {
                    Some(a) => bounded(product(a, inverse)),
                    None => Ok(None),
                };
            }
            let (Some(a), Some(b)) = (a, b) else {
                return Ok(None);
            };
            bounded(match source.kind {
                NumericExprKind::Add(_, _) => (a.0 + b.0, a.1 + b.1),
                NumericExprKind::Sub(_, _) => (a.0 - b.1, a.1 - b.0),
                NumericExprKind::Mul(_, _) => product(a, b),
                _ => unreachable!(),
            })
        }
    }
}

// Check both operands, even when constant folding could erase an unsupported read.
fn classical(source: &ClassicalExpr) -> Result<(), SymbolicError> {
    match &source.kind {
        ClassicalExprKind::ScalarCompare { .. } => {
            Err(SymbolicError::UnsupportedConstruct("scalar comparison"))
        }
        ClassicalExprKind::Not(a) => classical(a),
        ClassicalExprKind::Eq(a, b)
        | ClassicalExprKind::And(a, b)
        | ClassicalExprKind::Or(a, b)
        | ClassicalExprKind::Xor(a, b) => {
            classical(a)?;
            classical(b)
        }
        ClassicalExprKind::Bool(_) | ClassicalExprKind::Bit(_) => Ok(()),
    }
}

fn block(source: &Block, work: &mut usize, depth: usize) -> Result<(), SymbolicError> {
    spend(work)?;
    if depth >= MAX_DEPTH {
        return Err(error("source block depth bound"));
    }
    for statement in &source.statements {
        spend(work)?;
        match &statement.kind {
            StatementKind::While { .. } => {
                return Err(SymbolicError::UnsupportedConstruct("while loops"));
            }
            StatementKind::ScalarDeclare { .. } | StatementKind::ScalarAssign { .. } => {
                return Err(SymbolicError::UnsupportedConstruct("scalar storage"));
            }
            StatementKind::GlobalPhase(_) => {
                return Err(SymbolicError::UnsupportedConstruct("explicit global phase"));
            }
            StatementKind::Unitary { .. } => {
                return Err(SymbolicError::UnsupportedConstruct(
                    "composite unitary modifiers",
                ));
            }
            StatementKind::Apply { parameters, .. } => {
                for parameter in parameters {
                    expression(parameter, work, 0)?;
                }
            }
            StatementKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                classical(condition)?;
                block(then_branch, work, depth + 1)?;
                block(else_branch, work, depth + 1)?;
            }
            StatementKind::Scope(body) => block(body, work, depth + 1)?,
            StatementKind::Assign { value, .. } => classical(value)?,
            StatementKind::Measure { .. } | StatementKind::Reset(_) => {}
        }
    }
    Ok(())
}

pub(crate) fn numeric_domains(program: &Program) -> Result<(), SymbolicError> {
    let mut work = MAX_WORK;
    block(&program.body, &mut work, 0)
}

#[cfg(test)]
mod tests;
