//! Specification sort/dimension checking and pure, non-recursive helpers.
use super::*;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("{0}")]
pub struct FunctionError(pub String);
fn fail(message: impl Into<String>) -> FunctionError {
    FunctionError(message.into())
}

fn preserve_type(expression: &mut SpecExpr, ty: SpecType) -> SpecType {
    if ty.numeric() {
        let value = std::mem::replace(expression, SpecExpr::Bool(false));
        *expression = value.cast(ty);
    }
    ty
}

impl SpecType {
    /// Target representation shared with executable scalar expressions.
    pub fn scalar_type(self) -> Option<crate::ScalarType> {
        use crate::ScalarType;
        match self {
            Self::Int(w) => Some(ScalarType::Int {
                width: w.unwrap_or(32) as u32,
                signed: true,
            }),
            Self::Uint(w) => Some(ScalarType::Int {
                width: w.unwrap_or(32) as u32,
                signed: false,
            }),
            Self::Float(w) => Some(ScalarType::Float {
                width: w.unwrap_or(64) as u32,
            }),
            _ => None,
        }
    }
    /// Implicit conversion used by helper parameters and ghost assignments.
    pub fn accepts(self, actual: Self) -> bool {
        compatible(actual, self)
    }
    pub fn accepts_value(self, actual: Self, expression: &SpecExpr) -> bool {
        self.accepts(actual)
            || (self.boolean()
                && expression.literal().is_some_and(|n| {
                    n == BigRational::from_integer(0.into())
                        || n == BigRational::from_integer(1.into())
                }))
    }
    fn boolean(self) -> bool {
        matches!(self, Self::Bool | Self::Bit)
    }
    fn integer(self) -> bool {
        matches!(self, Self::Int(_) | Self::Uint(_))
    }
    fn numeric(self) -> bool {
        matches!(
            self,
            Self::Int(_) | Self::Uint(_) | Self::Float(_) | Self::Angle(_) | Self::Real
        )
    }
    fn scalar(self) -> bool {
        self.numeric() || self == Self::Complex
    }
    fn quantum(self) -> bool {
        matches!(self, Self::Ket(_) | Self::Bra(_) | Self::Operator(_))
    }
}

fn quantum_width(width: usize) -> Result<usize, FunctionError> {
    if (1..=MAX_QUANTUM_QUBITS).contains(&width) {
        Ok(width)
    } else {
        Err(fail("quantum dimension must be between 1 and 64 qubits"))
    }
}

/// Square operators and vectors only; rectangular maps are not implicit.
fn linear_product(a: SpecType, b: SpecType) -> Option<SpecType> {
    use SpecType::*;
    if a.scalar() && b.quantum() {
        return Some(b);
    }
    if a.quantum() && b.scalar() {
        return Some(a);
    }
    match (a, b) {
        (Operator(n), Ket(m)) if n == m => Some(Ket(n)),
        (Bra(n), Operator(m)) if n == m => Some(Bra(n)),
        (Operator(n), Operator(m)) if n == m => Some(Operator(n)),
        (Bra(n), Ket(m)) if n == m => Some(Complex),
        (Ket(n), Bra(m)) if n == m => Some(Operator(n)),
        _ => None,
    }
}

fn tensor_type(a: SpecType, b: SpecType) -> Result<SpecType, FunctionError> {
    use SpecType::*;
    let (n, m, make): (usize, usize, fn(usize) -> SpecType) = match (a, b) {
        (Ket(n), Ket(m)) => (n, m, Ket),
        (Bra(n), Bra(m)) => (n, m, Bra),
        (Operator(n), Operator(m)) => (n, m, Operator),
        _ => return Err(fail("tensor requires two kets, two bras or two operators")),
    };
    let width = n
        .checked_add(m)
        .ok_or_else(|| fail("quantum dimension overflow"))?;
    Ok(make(quantum_width(width)?))
}

fn compatible(actual: SpecType, expected: SpecType) -> bool {
    if actual == SpecType::Real || expected == SpecType::Real {
        return expected == SpecType::Real
            && matches!(
                actual,
                SpecType::Real | SpecType::Int(_) | SpecType::Uint(_) | SpecType::Float(_)
            );
    }
    actual == expected
        || (actual.boolean() && expected.boolean())
        || (actual.integer() && expected.integer())
        || (actual.numeric() && matches!(expected, SpecType::Float(_) | SpecType::Angle(_)))
}

// Admission of a state predicate only: neither purity nor the equality is proved.
fn state_comparable(a: SpecType, b: SpecType) -> bool {
    use SpecType::*;
    match (a, b) {
        (Qubit, Ket(1)) | (Ket(1), Qubit) => true,
        (QubitRegister(n), Ket(m)) | (Ket(m), QubitRegister(n)) => n == m,
        _ => false,
    }
}

fn join(a: SpecType, b: SpecType) -> Result<SpecType, FunctionError> {
    if a == b && (a.quantum() || a == SpecType::Complex) {
        return Ok(a);
    }
    if a.scalar() && b.scalar() && (a == SpecType::Complex || b == SpecType::Complex) {
        return Ok(SpecType::Complex);
    }
    if a.boolean() && b.boolean() {
        return Ok(SpecType::Bool);
    }
    if !a.numeric() || !b.numeric() {
        return Err(fail(format!(
            "incompatible types or quantum dimensions: {a:?}, {b:?}"
        )));
    }
    use SpecType::*;
    if a == Real || b == Real {
        if matches!(a, Angle(_)) || matches!(b, Angle(_)) {
            return Err(fail("angle and real require an explicit conversion"));
        }
        return Ok(Real);
    }
    let width = |t| match t {
        Int(w) | Uint(w) => w.unwrap_or(32),
        Float(w) => w.unwrap_or(64),
        Angle(w) => w.unwrap_or(32),
        _ => unreachable!(),
    };
    let w = Some(width(a).max(width(b)));
    Ok(match (a, b) {
        (Angle(_), Angle(_)) => Angle(w),
        (Float(_), Float(_)) => Float(w),
        (Float(_), _) => a,
        (_, Float(_)) => b,
        (Angle(_), _) | (_, Angle(_)) => {
            return Err(fail(
                "angle arithmetic requires angles or an explicitly permitted integer operation",
            ));
        }
        (Int(_), Int(_)) => Int(w),
        (Uint(_), Uint(_)) => Uint(w),
        _ => Int(w),
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

/// Resolve names/calls and check sorts and quantum dimensions. Domains, convergence,
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
    if functions.iter().any(|old| old.name == f.name) || matches!(f.name.as_str(), "true" | "false")
    {
        return Err(fail(format!(
            "duplicate or reserved helper name `{}`",
            f.name
        )));
    }
    let mut names = BTreeSet::new();
    for p in &f.parameters {
        if !names.insert(&p.name) || matches!(p.name.as_str(), "true" | "false") {
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
            Err(format!(
                "helper cannot capture `{name}`; declare it as a parameter"
            ))
        },
    };
    let ty = checker.check(&mut f.body, 0)?;
    if !f.result.accepts_value(ty, &f.body) {
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
        use SpecType::Bool;
        const FLOAT: SpecType = SpecType::Float(None);
        const INT: SpecType = SpecType::Int(None);
        const UINT: SpecType = SpecType::Uint(None);
        match e {
            SpecExpr::Cast { ty, operand } => {
                let actual = self.check(operand, depth + 1)?;
                if !ty.accepts_value(actual, operand) {
                    return Err(fail(format!(
                        "invalid implicit conversion from {actual} to {ty}"
                    )));
                }
                Ok(*ty)
            }
            SpecExpr::Number(n) => Ok(if n.is_integer() { INT } else { FLOAT }),
            SpecExpr::Bool(_) => Ok(Bool),
            SpecExpr::ImaginaryUnit => Ok(SpecType::Complex),
            SpecExpr::Ket(factors) => Ok(SpecType::Ket(quantum_width(factors.len())?)),
            SpecExpr::Bra(factors) => Ok(SpecType::Bra(quantum_width(factors.len())?)),
            SpecExpr::Pauli(_) => Ok(SpecType::Operator(1)),
            SpecExpr::Constant(_) | SpecExpr::Infinity => Ok(FLOAT),
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
                if !matches!(resolved.uncast(), SpecExpr::Symbol { id: found, .. } if *found == *id)
                {
                    return Err(fail("symbol does not belong to this scope"));
                }
                Ok(ty)
            }
            SpecExpr::Unary { op, operand } => {
                let t = self.check(operand, depth + 1)?;
                match op {
                    UnaryOp::Not if t.boolean() => Ok(Bool),
                    UnaryOp::Neg if t.quantum() || t == SpecType::Complex => Ok(t),
                    UnaryOp::Neg if t.numeric() => Ok(t),
                    UnaryOp::Factorial if t.integer() => Ok(UINT),
                    _ => Err(fail(format!("invalid operand {t:?} for {op:?}"))),
                }
            }
            SpecExpr::Binary { op, left, right } => {
                let mut a = self.check(left, depth + 1)?;
                let mut b = self.check(right, depth + 1)?;
                if a.numeric() && b.numeric() {
                    if left.literal().is_some() && right.literal().is_none() && b.accepts(a) {
                        a = b;
                    }
                    if right.literal().is_some() && left.literal().is_none() && a.accepts(b) {
                        b = a;
                    }
                    if matches!(op, BinaryOp::Mul | BinaryOp::Div) {
                        if let SpecType::Angle(w) = a
                            && right.literal().is_some_and(|n| n.is_integer())
                        {
                            b = SpecType::Uint(w);
                        }
                        if let SpecType::Angle(w) = b
                            && left.literal().is_some_and(|n| n.is_integer())
                        {
                            a = SpecType::Uint(w);
                        }
                    }
                }
                use BinaryOp::*;
                match op {
                    Tensor => tensor_type(a, b),
                    And | Or | Implies if a.boolean() && b.boolean() => Ok(Bool),
                    Eq | Ne
                        if (a.boolean() && b.boolean())
                            || (a.scalar() && b.scalar())
                            || (a.quantum() && a == b)
                            || state_comparable(a, b)
                            || (a == SpecType::Bit && b.integer())
                            || (b == SpecType::Bit && a.integer()) =>
                    {
                        Ok(Bool)
                    }
                    Lt | Le | Gt | Ge if a.numeric() && b.numeric() => Ok(Bool),
                    Add | Sub if a.quantum() && a == b => Ok(a),
                    Add | Sub | Mul | Div
                        if a.scalar()
                            && b.scalar()
                            && (a == SpecType::Complex || b == SpecType::Complex) =>
                    {
                        Ok(SpecType::Complex)
                    }
                    Mul if a.quantum() || b.quantum() => linear_product(a, b)
                        .ok_or_else(|| fail(format!("invalid linear product: {a:?} * {b:?}"))),
                    Div if a.quantum() && b.scalar() => Ok(a),
                    Pow if a == SpecType::Complex && b.integer() => Ok(SpecType::Complex),
                    Add | Sub | Mul | Div
                        if matches!(a, SpecType::Angle(_)) || matches!(b, SpecType::Angle(_)) =>
                    {
                        use SpecType::{Angle, Uint};
                        match (*op, a, b) {
                            (Add | Sub, Angle(w), Angle(v))
                                if w.unwrap_or(32) == v.unwrap_or(32) =>
                            {
                                Ok(a)
                            }
                            (Div, Angle(w), Angle(v)) if w.unwrap_or(32) == v.unwrap_or(32) => {
                                Ok(Uint(w))
                            }
                            (Mul | Div, Angle(w), Uint(v))
                                if w.unwrap_or(32) == v.unwrap_or(32) =>
                            {
                                Ok(a)
                            }
                            (Mul, Uint(w), Angle(v)) if w.unwrap_or(32) == v.unwrap_or(32) => Ok(b),
                            _ => Err(fail("invalid angle operands or widths")),
                        }
                    }
                    Add | Mul if a.numeric() && b.numeric() => join(a, b),
                    Sub | Div if a.numeric() && b.numeric() => join(a, b),
                    Pow if a.numeric() && b.numeric() => {
                        Ok(if a == SpecType::Real || b == SpecType::Real {
                            SpecType::Real
                        } else if a.integer() && b.integer() {
                            a
                        } else {
                            FLOAT
                        })
                    }
                    Mod if a.integer() && b.integer() => join(a, b),
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
                Ok(preserve_type(e, join(a, b)?))
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
                if matches!(function, Diag | Trace | Normalize) {
                    return Err(fail(
                        "program-state queries and general matrix specification functions are reserved",
                    ));
                }
                let required = if matches!(function, Binomial | TraceDistance) {
                    2
                } else {
                    1
                };
                if (matches!(function, Min | Max) && arguments.len() < 2)
                    || (!matches!(function, Min | Max) && arguments.len() != required)
                {
                    return Err(fail("wrong mathematical function arity"));
                }
                let types = arguments
                    .iter_mut()
                    .map(|a| self.check(a, depth + 1))
                    .collect::<Result<Vec<_>, _>>()?;
                if *function == Real {
                    if !SpecType::Real.accepts(types[0]) {
                        return Err(fail("real expects an int, uint, float or real value"));
                    }
                    *e = arguments[0].clone().cast(types[0]).cast(SpecType::Real);
                    return Ok(SpecType::Real);
                }
                if *function == Factorial {
                    if !types[0].integer() {
                        return Err(fail("factorial expects a nonnegative integer"));
                    }
                    return Ok(SpecType::Real);
                }
                if *function == AvgDensity {
                    return match types[0] {
                        SpecType::Qubit => Ok(SpecType::Operator(1)),
                        SpecType::QubitRegister(n) => Ok(SpecType::Operator(n)),
                        _ => Err(fail("avg_density expects a program quantum reference")),
                    };
                }
                if *function == TraceDistance {
                    return match (types[0], types[1]) {
                        (SpecType::Operator(a), SpecType::Operator(b)) if a == b => {
                            Ok(SpecType::Real)
                        }
                        _ => Err(fail("trace_distance expects same-dimensional operators")),
                    };
                }
                if *function == Adjoint {
                    return match types[0] {
                        SpecType::Ket(n) => Ok(SpecType::Bra(n)),
                        SpecType::Bra(n) => Ok(SpecType::Ket(n)),
                        SpecType::Operator(n) => Ok(SpecType::Operator(n)),
                        t if t.scalar() => Ok(t),
                        _ => Err(fail("adjoint expects a scalar, ket, bra or operator")),
                    };
                }
                if matches!(function, Conjugate | RealPart | ImagPart) {
                    if !types[0].scalar() {
                        return Err(fail("conj/re/im expect a real or complex scalar"));
                    }
                    return Ok(if *function == Conjugate {
                        types[0]
                    } else if types[0] == SpecType::Real {
                        SpecType::Real
                    } else {
                        FLOAT
                    });
                }
                if *function == Abs && types[0] == SpecType::Complex {
                    return Ok(FLOAT);
                }
                if *function == Probability {
                    if !types[0].boolean() {
                        return Err(fail("probability expects a Boolean event"));
                    }
                    return Ok(SpecType::Real);
                }
                if types.iter().any(|t| !t.numeric()) {
                    return Err(fail("mathematical function expects numeric arguments"));
                }
                if *function == Binomial && !types[1].integer() {
                    return Err(fail("binom second argument must be an integer"));
                }
                Ok(match function {
                    Floor | Ceil => INT,
                    Abs => {
                        if types[0] == SpecType::Real {
                            SpecType::Real
                        } else if types[0].integer() {
                            UINT
                        } else {
                            FLOAT
                        }
                    }
                    Min | Max => types.iter().copied().skip(1).try_fold(types[0], join)?,
                    _ if *function == Expectation || types.contains(&SpecType::Real) => {
                        SpecType::Real
                    }
                    _ => FLOAT,
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
                if matches!(variable.name.as_str(), "true" | "false") {
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
                } else if (matches!(kind, BinderKind::Sum) && (ty.scalar() || ty.quantum()))
                    || (matches!(kind, BinderKind::Product) && ty.scalar())
                {
                    Ok(ty)
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
                    Ok(preserve_type(e, ty))
                } else {
                    match self.check(value, depth + 1)? {
                        SpecType::QubitRegister(_) => Ok(SpecType::Qubit),
                        t if t.integer() => Ok(SpecType::Bit),
                        _ => Err(fail(
                            "indexing requires a quantum register, classical integer/bit register or list",
                        )),
                    }
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
            if !parameter.ty.accepts_value(actual, arg) {
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
    let args: Vec<_> = args
        .iter()
        .zip(&f.parameters)
        .map(|(arg, parameter)| arg.clone().cast(parameter.ty))
        .collect();
    substitute(
        &mut body,
        &args,
        &mut BTreeMap::new(),
        &mut next,
        &mut 4096,
        0,
    )?;
    Ok(body.cast(f.result))
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
        SpecExpr::Unary { operand, .. } | SpecExpr::Cast { operand, .. } => vec![operand],
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
        SpecExpr::Unary { operand, .. } | SpecExpr::Cast { operand, .. } => vec![operand],
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
