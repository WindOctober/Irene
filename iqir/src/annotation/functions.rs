//! Classical sort checking and pure, non-recursive helper functions.
use super::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{0}")]
pub struct FunctionError(pub String);
fn fail(message: impl Into<String>) -> FunctionError {
    FunctionError(message.into())
}

impl SpecType {
    fn boolean(self) -> bool {
        matches!(self, Self::Bool | Self::Bit)
    }
    fn integer(self) -> bool {
        matches!(self, Self::Int | Self::Uint)
    }
    fn numeric(self) -> bool {
        !self.boolean()
    }
}

fn compatible(actual: SpecType, expected: SpecType) -> bool {
    actual == expected
        || (actual.boolean() && expected.boolean())
        || (actual.integer() && expected.integer())
        || (actual.numeric() && matches!(expected, SpecType::Float | SpecType::Angle))
}

fn join(a: SpecType, b: SpecType) -> Result<SpecType, FunctionError> {
    if a.boolean() && b.boolean() {
        return Ok(SpecType::Bool);
    }
    if !a.numeric() || !b.numeric() {
        return Err(fail("cannot mix Boolean and numeric values"));
    }
    Ok(if !a.integer() || !b.integer() {
        SpecType::Float
    } else if a == SpecType::Uint && b == SpecType::Uint {
        SpecType::Uint
    } else {
        SpecType::Int
    })
}

struct Checker<'a, F> {
    functions: &'a [SpecFunction],
    parameters: &'a [Parameter],
    locals: Vec<(String, u32, SpecType)>,
    next_local: u32,
    work: usize,
    resolve: F,
}

/// Resolve names/calls and check classical sorts. Domains, convergence,
/// nonnegative Uint values and proof obligations are NOT discharged here.
pub fn check_expression(
    expression: &mut SpecExpr,
    functions: &[SpecFunction],
    resolve: impl FnMut(&str) -> Result<(SpecExpr, SpecType), String>,
) -> Result<SpecType, FunctionError> {
    Checker {
        functions,
        parameters: &[],
        locals: Vec::new(),
        next_local: 0,
        work: 0,
        resolve,
    }
    .check(expression, 0)
}

/// Definitions see only their explicit parameters, mathematical constants and
/// earlier helpers. No forward references, recursion, program-state capture,
/// overloading or silent replacement. Failed definitions never enter the table.
pub fn define_function(
    functions: &mut Vec<SpecFunction>,
    mut f: SpecFunction,
) -> Result<FunctionId, FunctionError> {
    if functions.len() >= 128 || f.parameters.len() > 32 {
        return Err(fail("helper function budget exceeded"));
    }
    if functions.iter().any(|old| old.name == f.name)
        || parser::builtin(&f.name).is_some()
        || matches!(
            f.name.as_str(),
            "sum" | "product" | "forall" | "exists" | "sup" | "infimum" | "inf" | "true" | "false"
        )
    {
        return Err(fail(format!(
            "duplicate or reserved helper name `{}`",
            f.name
        )));
    }
    let mut names = BTreeSet::new();
    for p in &f.parameters {
        if !names.insert(&p.name) || matches!(p.name.as_str(), "true" | "false" | "inf") {
            return Err(fail(format!(
                "duplicate or reserved parameter `{}`",
                p.name
            )));
        }
    }
    let mut checker = Checker {
        functions,
        parameters: &f.parameters,
        locals: Vec::new(),
        next_local: 0,
        work: 0,
        resolve: |name: &str| {
            let c = match name {
                "pi" | "π" => NumericConstant::Pi,
                "tau" | "τ" => NumericConstant::Tau,
                "euler" | "ℇ" => NumericConstant::Euler,
                _ => {
                    return Err(format!(
                        "helper cannot capture `{name}`; declare it as a parameter"
                    ));
                }
            };
            Ok((SpecExpr::Constant(c), SpecType::Float))
        },
    };
    let ty = checker.check(&mut f.body, 0)?;
    if !compatible(ty, f.result) {
        return Err(fail(format!(
            "helper `{}` returns {ty:?}, expected {:?}",
            f.name, f.result
        )));
    }
    let id = FunctionId(functions.len());
    functions.push(f);
    Ok(id)
}

impl<F> Checker<'_, F>
where
    F: FnMut(&str) -> Result<(SpecExpr, SpecType), String>,
{
    fn check(&mut self, e: &mut SpecExpr, depth: usize) -> Result<SpecType, FunctionError> {
        self.work += 1;
        if depth > 64 || self.work > 2048 {
            return Err(fail("specification checking budget exceeded"));
        }
        use SpecType::{Bool, Float, Int, Uint};
        match e {
            SpecExpr::Number(n) => Ok(if n.is_integer() {
                if n < &mut num_rational::BigRational::from_integer(0.into()) {
                    Int
                } else {
                    Uint
                }
            } else {
                Float
            }),
            SpecExpr::Bool(_) => Ok(Bool),
            SpecExpr::Constant(_) | SpecExpr::Infinity => Ok(Float),
            SpecExpr::Name(name) => {
                if let Some((_, id, ty)) = self.locals.iter().rev().find(|(n, ..)| n == name) {
                    let ty = *ty;
                    *e = SpecExpr::BoundVariable(*id);
                    return Ok(ty);
                }
                if let Some((index, p)) = self
                    .parameters
                    .iter()
                    .enumerate()
                    .find(|(_, p)| &p.name == name)
                {
                    *e = SpecExpr::Parameter(index);
                    return Ok(p.ty);
                }
                let (value, ty) = (self.resolve)(name).map_err(fail)?;
                *e = value;
                Ok(ty)
            }
            SpecExpr::Parameter(i) => self
                .parameters
                .get(*i)
                .map(|p| p.ty)
                .ok_or_else(|| fail("unbound helper parameter")),
            SpecExpr::BoundVariable(id) => self
                .locals
                .iter()
                .rev()
                .find(|(_, i, _)| i == id)
                .map(|(_, _, t)| *t)
                .ok_or_else(|| fail("unbound quantified variable")),
            SpecExpr::Symbol { name, id } => {
                let (resolved, ty) = (self.resolve)(name).map_err(fail)?;
                if !matches!(resolved, SpecExpr::Symbol { id: found, .. } if found == *id) {
                    return Err(fail("symbol does not belong to this scope"));
                }
                Ok(ty)
            }
            SpecExpr::Unary { op, operand } => {
                let t = self.check(operand, depth + 1)?;
                match op {
                    UnaryOp::Not if t.boolean() => Ok(Bool),
                    UnaryOp::Neg if t.numeric() => Ok(if t.integer() { Int } else { Float }),
                    UnaryOp::Factorial if t.integer() => Ok(Uint),
                    _ => Err(fail(format!("invalid operand {t:?} for {op:?}"))),
                }
            }
            SpecExpr::Binary { op, left, right } => {
                let a = self.check(left, depth + 1)?;
                let b = self.check(right, depth + 1)?;
                use BinaryOp::*;
                match op {
                    And | Or | Implies if a.boolean() && b.boolean() => Ok(Bool),
                    Eq | Ne
                        if (a.boolean() && b.boolean())
                            || (a.numeric() && b.numeric())
                            || (a == SpecType::Bit && b.integer())
                            || (b == SpecType::Bit && a.integer()) =>
                    {
                        Ok(Bool)
                    }
                    Lt | Le | Gt | Ge if a.numeric() && b.numeric() => Ok(Bool),
                    Add | Mul if a.numeric() && b.numeric() => join(a, b),
                    Sub if a.numeric() && b.numeric() => Ok(if a.integer() && b.integer() {
                        Int
                    } else {
                        Float
                    }),
                    Div if a.numeric() && b.numeric() => Ok(Float),
                    Pow if a.numeric() && b.numeric() => {
                        Ok(if a.integer() && b == Uint { a } else { Float })
                    }
                    Mod if a.integer() && b.integer() => Ok(Int),
                    _ => Err(fail(format!("invalid operands {a:?}, {b:?} for {op:?}"))),
                }
            }
            SpecExpr::Conditional {
                condition,
                then_value,
                else_value,
            } => {
                if !self.check(condition, depth + 1)?.boolean() {
                    return Err(fail("conditional requires a Boolean condition"));
                }
                let a = self.check(then_value, depth + 1)?;
                let b = self.check(else_value, depth + 1)?;
                join(a, b)
            }
            SpecExpr::NamedCall { name, arguments } => {
                let (index, f) = self
                    .functions
                    .iter()
                    .enumerate()
                    .find(|(_, f)| &f.name == name)
                    .ok_or_else(|| {
                        fail(format!(
                            "unknown helper `{name}` (forward/recursive calls are unsupported)"
                        ))
                    })?;
                let result = self.call(f, arguments, depth)?;
                *e = SpecExpr::HelperCall {
                    function: FunctionId(index),
                    arguments: std::mem::take(arguments),
                };
                Ok(result)
            }
            SpecExpr::HelperCall {
                function,
                arguments,
            } => {
                let f = self
                    .functions
                    .get(function.0)
                    .ok_or_else(|| fail("invalid helper ID"))?;
                self.call(f, arguments, depth)
            }
            SpecExpr::Call {
                function,
                arguments,
            } => {
                use MathFunction::*;
                if matches!(
                    function,
                    Diag | Trace | Normalize | AvgDensity | TraceDistance
                ) {
                    return Err(fail(
                        "quantum/matrix specification operators are reserved; classical checking does not interpret them",
                    ));
                }
                let required = if matches!(function, Binomial) { 2 } else { 1 };
                if (matches!(function, Min | Max) && arguments.len() < 2)
                    || (!matches!(function, Min | Max) && arguments.len() != required)
                {
                    return Err(fail("wrong mathematical function arity"));
                }
                let types = arguments
                    .iter_mut()
                    .map(|a| self.check(a, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?;
                if *function == Probability {
                    if !types[0].boolean() {
                        return Err(fail("probability expects a Boolean event"));
                    }
                    return Ok(Float);
                }
                if types.iter().any(|t| !t.numeric()) {
                    return Err(fail("mathematical function expects numeric arguments"));
                }
                if *function == Binomial && !types[1].integer() {
                    return Err(fail("binom second argument must be an integer"));
                }
                Ok(match function {
                    Floor | Ceil => Int,
                    Abs => {
                        if types[0].integer() {
                            Uint
                        } else {
                            Float
                        }
                    }
                    Min | Max => types
                        .into_iter()
                        .reduce(|a, b| join(a, b).unwrap())
                        .unwrap(),
                    _ => Float,
                })
            }
            SpecExpr::Binder {
                kind,
                variable,
                id,
                lower,
                upper,
                body,
                ..
            } => {
                if matches!(variable.name.as_str(), "true" | "false" | "inf") {
                    return Err(fail("reserved bound-variable name"));
                }
                let lo = self.check(lower, depth + 1)?;
                let hi = self.check(upper, depth + 1)?;
                if !variable.ty.numeric() || !lo.numeric() || !hi.numeric() {
                    return Err(fail("binder ranges must be numeric"));
                }
                if matches!(kind, BinderKind::Sum | BinderKind::Product) && !variable.ty.integer() {
                    return Err(fail("sum/product require an integer index"));
                }
                if variable.ty.integer()
                    && (!lo.integer()
                        || (!hi.integer() && !matches!(upper.as_ref(), SpecExpr::Infinity)))
                {
                    return Err(fail(
                        "integer binder requires integer bounds (or +inf upper bound)",
                    ));
                }
                let local = self.next_local;
                self.next_local += 1;
                *id = Some(local);
                self.locals
                    .push((variable.name.clone(), local, variable.ty));
                let ty = self.check(body, depth + 1)?;
                self.locals.pop();
                if matches!(kind, BinderKind::Forall | BinderKind::Exists) {
                    if !ty.boolean() {
                        return Err(fail("quantifier body must be Boolean"));
                    }
                    Ok(Bool)
                } else {
                    if !ty.numeric() {
                        return Err(fail("sum/product/extremum body must be numeric"));
                    }
                    Ok(ty)
                }
            }
            SpecExpr::Index { value, index } => {
                if !self.check(index, depth + 1)?.integer() {
                    return Err(fail("index must be an integer"));
                }
                if let SpecExpr::List(items) = value.as_mut() {
                    let mut types = items.iter_mut().map(|e| self.check(e, depth + 1));
                    let mut ty = types
                        .next()
                        .ok_or_else(|| fail("cannot index an empty list"))??;
                    for t in types {
                        ty = join(ty, t?)?;
                    }
                    Ok(ty)
                } else if self.check(value, depth + 1)?.integer() {
                    Ok(SpecType::Bit)
                } else {
                    Err(fail(
                        "indexing requires a classical integer/bit register or list",
                    ))
                }
            }
            SpecExpr::List(_) => Err(fail(
                "helper arguments/results must be scalar; matrix semantics are reserved",
            )),
        }
    }

    fn call(
        &mut self,
        f: &SpecFunction,
        args: &mut [SpecExpr],
        depth: usize,
    ) -> Result<SpecType, FunctionError> {
        if args.len() != f.parameters.len() {
            return Err(fail(format!(
                "wrong argument count for helper `{}`",
                f.name
            )));
        }
        for (arg, parameter) in args.iter_mut().zip(&f.parameters) {
            let actual = self.check(arg, depth + 1)?;
            if !compatible(actual, parameter.ty) {
                return Err(fail(format!(
                    "helper `{}` parameter `{}` expects {:?}, got {actual:?}",
                    f.name, parameter.name, parameter.ty
                )));
            }
        }
        Ok(f.result)
    }
}

/// Substitute already-checked arguments into one helper body. Nested helper
/// calls remain calls; this is NOT recursive unfolding or numerical evaluation.
/// Bound variables in the callee are alpha-renamed to avoid capturing arguments.
pub fn instantiate_function(
    functions: &[SpecFunction],
    id: FunctionId,
    args: &[SpecExpr],
) -> Result<SpecExpr, FunctionError> {
    let f = functions
        .get(id.0)
        .ok_or_else(|| fail("invalid helper ID"))?;
    if args.len() != f.parameters.len() {
        return Err(fail("wrong helper arity"));
    }
    let mut next = 0u32;
    let mut stack: Vec<_> = args.iter().chain(std::iter::once(&f.body)).collect();
    let mut work = 0;
    while let Some(e) = stack.pop() {
        work += 1;
        if work > 4096 {
            return Err(fail("helper substitution budget exceeded"));
        }
        if let SpecExpr::BoundVariable(id) | SpecExpr::Binder { id: Some(id), .. } = e {
            next = next.max(
                id.checked_add(1)
                    .ok_or_else(|| fail("bound-variable ID overflow"))?,
            );
        }
        stack.extend(children(e));
    }
    let mut body = f.body.clone();
    substitute(
        &mut body,
        args,
        &mut BTreeMap::new(),
        &mut next,
        &mut 4096,
        0,
    )?;
    Ok(body)
}

fn substitute(
    e: &mut SpecExpr,
    args: &[SpecExpr],
    renamed: &mut BTreeMap<u32, u32>,
    next: &mut u32,
    work: &mut usize,
    depth: usize,
) -> Result<(), FunctionError> {
    if depth > 64 || *work == 0 {
        return Err(fail("helper substitution budget exceeded"));
    }
    *work -= 1;
    match e {
        SpecExpr::Parameter(i) => {
            let arg = args
                .get(*i)
                .ok_or_else(|| fail("unbound helper parameter"))?;
            let mut pending = vec![(arg, depth)];
            while let Some((node, d)) = pending.pop() {
                if d > 64 || *work == 0 {
                    return Err(fail("helper substitution budget exceeded"));
                }
                *work -= 1;
                pending.extend(children(node).into_iter().map(|c| (c, d + 1)));
            }
            *e = arg.clone();
        }
        SpecExpr::BoundVariable(i) => {
            if let Some(new) = renamed.get(i) {
                *i = *new;
            }
        }
        SpecExpr::Binder {
            id,
            lower,
            upper,
            body,
            ..
        } => {
            substitute(lower, args, renamed, next, work, depth + 1)?;
            substitute(upper, args, renamed, next, work, depth + 1)?;
            let old = id.ok_or_else(|| fail("unresolved binder in helper"))?;
            let new = *next;
            *next = next
                .checked_add(1)
                .ok_or_else(|| fail("bound-variable ID overflow"))?;
            let previous = renamed.insert(old, new);
            *id = Some(new);
            substitute(body, args, renamed, next, work, depth + 1)?;
            if let Some(p) = previous {
                renamed.insert(old, p);
            } else {
                renamed.remove(&old);
            }
        }
        _ => {
            for c in children_mut(e) {
                substitute(c, args, renamed, next, work, depth + 1)?;
            }
        }
    }
    Ok(())
}

pub(super) fn children(e: &SpecExpr) -> Vec<&SpecExpr> {
    match e {
        SpecExpr::Unary { operand, .. } => vec![operand],
        SpecExpr::Binary { left, right, .. } => vec![left, right],
        SpecExpr::Index { value, index } => vec![value, index],
        SpecExpr::Conditional {
            condition,
            then_value,
            else_value,
        } => vec![condition, then_value, else_value],
        SpecExpr::Binder {
            lower, upper, body, ..
        } => vec![lower, upper, body],
        SpecExpr::Call { arguments, .. }
        | SpecExpr::NamedCall { arguments, .. }
        | SpecExpr::HelperCall { arguments, .. }
        | SpecExpr::List(arguments) => arguments.iter().collect(),
        _ => vec![],
    }
}

fn children_mut(e: &mut SpecExpr) -> Vec<&mut SpecExpr> {
    match e {
        SpecExpr::Unary { operand, .. } => vec![operand],
        SpecExpr::Binary { left, right, .. } => vec![left, right],
        SpecExpr::Index { value, index } => vec![value, index],
        SpecExpr::Conditional {
            condition,
            then_value,
            else_value,
        } => vec![condition, then_value, else_value],
        SpecExpr::Call { arguments, .. }
        | SpecExpr::NamedCall { arguments, .. }
        | SpecExpr::HelperCall { arguments, .. }
        | SpecExpr::List(arguments) => arguments.iter_mut().collect(),
        _ => vec![],
    }
}
