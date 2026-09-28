//! Bounded sufficient real-domain check BEFORE slicing or scalar/phase algebra.
//! Finite rational intervals certify nonzero denominators; an inconclusive
//! interval refuses rather than assuming a unit. Both operands and all source
//! branches are visited, even when a later zero/guard/slice would erase them.
//! This does not implement target-specific finite-width floating arithmetic.

use num_rational::BigRational;

use crate::ir::{Block, NumericConstant, NumericExpr, NumericExprKind, Program, StatementKind};
use crate::symbolic::SymbolicError;

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

fn block(source: &Block, work: &mut usize, depth: usize) -> Result<(), SymbolicError> {
    spend(work)?;
    if depth >= MAX_DEPTH {
        return Err(error("source block depth bound"));
    }
    for statement in &source.statements {
        spend(work)?;
        match &statement.kind {
            StatementKind::Apply { parameters, .. } => {
                for parameter in parameters {
                    expression(parameter, work, 0)?;
                }
            }
            StatementKind::If {
                then_branch,
                else_branch,
                ..
            } => {
                block(then_branch, work, depth + 1)?;
                block(else_branch, work, depth + 1)?;
            }
            StatementKind::Scope(body) => block(body, work, depth + 1)?,
            StatementKind::Measure { .. }
            | StatementKind::Assign { .. }
            | StatementKind::Reset(_) => {}
        }
    }
    Ok(())
}

pub(crate) fn numeric_domains(program: &Program) -> Result<(), SymbolicError> {
    let mut work = MAX_WORK;
    block(&program.body, &mut work, 0)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::openqasm3::parse_str;

    fn parse(body: &str) -> Program {
        parse_str(
            &format!("OPENQASM 3.0; include \"stdgates.inc\"; qubit q; {body}"),
            "numeric-domain.qasm",
        )
        .unwrap()
    }

    #[test]
    fn all_rational_signs_and_constant_divisors_are_checked_exactly() {
        for numerator in -4..=4 {
            for denominator in -4..=4 {
                // Floating-source nodes keep the composite divisor in the IR.
                let source = parse(&format!("p(({numerator}.0)/(0.0+({denominator}.0))) q;"));
                let result = numeric_domains(&source);
                assert_eq!(
                    result.is_ok(),
                    denominator != 0,
                    "{numerator}/{denominator}"
                );
            }
        }
        for angle in [
            "pi/2",
            "pi/(0.5+0.5)",
            "1.0/pi",
            "1.0/(-pi)",
            "1.0/(tau-euler)",
            "0.0/(pi*pi)",
        ] {
            assert!(
                numeric_domains(&parse(&format!("p({angle}) q;"))).is_ok(),
                "{angle}"
            );
        }
    }

    #[test]
    fn zero_products_inactive_branches_and_dead_wires_do_not_hide_domains() {
        for body in [
            "p(0.0*(1.0/(0.0+0.0))) q;",
            "p(1.0/(0.0*(1.0/(0.0+0.0)))) q;",
            "if (false) { p(1.0/(0.0+0.0)) q; }",
            "if (true) { } else { p(1.0/(0.0+0.0)) q; }",
            "qubit dead; p(1.0/(0.0+0.0)) dead;",
            "p(1.0/(pi-pi)) q;",
            "p(1.0/(tau-2*pi)) q;",
        ] {
            assert!(numeric_domains(&parse(body)).is_err(), "{body}");
        }
    }

    #[test]
    fn formal_inputs_are_not_implicitly_assumed_nonzero_and_refusal_is_bounded() {
        for (body, accepted) in [
            ("input angle theta; p(theta/2) q;", true),
            ("input angle theta; p(theta*pi) q;", true),
            ("input angle theta; p(1.0/theta) q;", false),
            ("input angle theta; p(0.0*(1.0/theta)) q;", false),
        ] {
            assert_eq!(numeric_domains(&parse(body)).is_ok(), accepted, "{body}");
        }
        let source = parse("p(pi/(0.5+0.5)) q;");
        let mut work = MAX_WORK;
        block(&source.body, &mut work, 0).unwrap();
        let mut short = MAX_WORK - work - 1;
        assert!(block(&source.body, &mut short, 0).is_err());
        let mut work = MAX_WORK;
        assert!(block(&source.body, &mut work, MAX_DEPTH).is_err());
    }
}
