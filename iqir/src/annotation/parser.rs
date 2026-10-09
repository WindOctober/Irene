//! Pest owns token recognition, grammar and Pratt precedence. This module only
//! translates its parse tree to specification AST nodes; it never evaluates them.
use super::*;
use bigdecimal::{BigDecimal, num_bigint::BigInt};
use num_rational::BigRational;
use pest::{
    Parser,
    iterators::Pair,
    pratt_parser::{Assoc, Op, PrattParser},
};
use std::{str::FromStr, sync::LazyLock};

#[derive(pest_derive::Parser)]
#[grammar = "annotation/spec.pest"]
struct Grammar;

#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("specification at byte {offset}: {message}")]
pub struct AnnotationParseError {
    pub offset: usize,
    pub message: String,
}

fn error(offset: usize, message: impl Into<String>) -> AnnotationParseError {
    AnnotationParseError {
        offset,
        message: message.into(),
    }
}

static PRATT: LazyLock<PrattParser<Rule>> = LazyLock::new(|| {
    use Assoc::{Left, Right};
    use Rule::*;
    PrattParser::new()
        .op(Op::infix(implies, Right))
        .op(Op::infix(or, Left))
        .op(Op::infix(and, Left))
        .op(Op::infix(eq, Left)
            | Op::infix(ne, Left)
            | Op::infix(lt, Left)
            | Op::infix(le, Left)
            | Op::infix(gt, Left)
            | Op::infix(ge, Left))
        .op(Op::infix(add, Left) | Op::infix(sub, Left))
        .op(Op::infix(tensor, Left))
        .op(Op::infix(mul, Left) | Op::infix(div, Left) | Op::infix(modulo, Left))
        .op(Op::prefix(neg) | Op::prefix(pos) | Op::prefix(not))
        .op(Op::infix(pow, Right))
        .op(Op::postfix(factorial) | Op::postfix(index))
});

fn parse(rule: Rule, text: &str) -> Result<Pair<'_, Rule>, AnnotationParseError> {
    // Admission only, not a second lexer. Bound recursive grammar/Pratt work
    // before invoking the library, including unparenthesized ternary/quantifier
    // chains. Every quantifier introduces one semicolon.
    if text.len() > 16384 {
        return Err(error(0, "specification byte budget exceeded"));
    }
    let mut nesting = 0usize;
    let mut conditionals = 0usize;
    let mut quantifiers = 0usize;
    let mut operators = 0usize;
    for (offset, c) in text.char_indices() {
        match c {
            '(' | '[' => nesting += 1,
            ')' | ']' => nesting = nesting.saturating_sub(1),
            '?' => conditionals += 1,
            ';' => quantifiers += 1,
            '+' | '-' | '!' | '*' | '/' | '^' | '%' | '=' | '<' | '>' | '&' | '|' | '\\' | '⊗' => {
                operators += 1
            }
            _ => {}
        }
        if nesting > 48 || conditionals + quantifiers > 32 || operators > 256 {
            return Err(error(offset, "specification complexity budget exceeded"));
        }
    }
    let root = Grammar::parse(rule, text)
        .map_err(|e| {
            let offset = match e.location {
                pest::error::InputLocation::Pos(p) | pest::error::InputLocation::Span((p, _)) => p,
            };
            error(offset, e.to_string())
        })?
        .next()
        .expect("grammar file has one root");
    let mut work = vec![(root.clone(), 0)];
    let mut count = 0;
    while let Some((p, depth)) = work.pop() {
        count += 1;
        if count > 4096 || depth > 128 {
            return Err(error(p.as_span().start(), "parse tree budget exceeded"));
        }
        work.extend(p.into_inner().map(|c| (c, depth + 1)));
    }
    Ok(root)
}

pub fn parse_expression(text: &str) -> Result<SpecExpr, AnnotationParseError> {
    expression(
        parse(Rule::expression_file, text)?
            .into_inner()
            .next()
            .unwrap(),
    )
}

pub fn parse_annotation(text: &str, span: SourceSpan) -> Result<Annotation, AnnotationParseError> {
    let mut fields = parse(Rule::annotation_file, text)?.into_inner();
    let first = fields.next().unwrap();
    if first.as_rule() == Rule::exit_probability {
        let mut parts = first.into_inner();
        parts.next(); // annotation keyword
        let relation = match parts.next().unwrap().as_str() {
            "==" => ProbabilityRelation::Equal,
            ">=" => ProbabilityRelation::AtLeast,
            "<=" => ProbabilityRelation::AtMost,
            _ => unreachable!(),
        };
        return Ok(Annotation {
            kind: AnnotationKind::ExitProbability,
            payload: AnnotationPayload::ExitProbability {
                relation,
                bound: expression(parts.next().unwrap())?,
            },
            span,
        });
    }
    if matches!(
        first.as_rule(),
        Rule::ghost_declaration | Rule::ghost_assignment
    ) {
        let declaration = first.as_rule() == Rule::ghost_declaration;
        let mut parts = first.into_inner();
        parts.next(); // ghost/set keyword
        let name = parts.next().unwrap().as_str().to_owned();
        let (kind, payload) = if declaration {
            let ty = scalar_type(parts.next().unwrap())?;
            if ty == SpecType::Real {
                return Err(error(
                    0,
                    "ghost storage uses OpenQASM types, not mathematical real",
                ));
            }
            let initializer = parts.next().map(expression).transpose()?;
            (
                AnnotationKind::GhostDeclare,
                AnnotationPayload::GhostDeclare {
                    id: None,
                    name,
                    ty,
                    initializer,
                    scoped: false,
                },
            )
        } else {
            (
                AnnotationKind::GhostAssign,
                AnnotationPayload::GhostAssign {
                    id: None,
                    name,
                    value: expression(parts.next().unwrap())?,
                },
            )
        };
        return Ok(Annotation {
            kind,
            payload,
            span,
        });
    }
    let kind = match first.as_str() {
        "assert" => AnnotationKind::Assert,
        "requires" => AnnotationKind::Requires,
        "ensures" => AnnotationKind::Ensures,
        "invariant" => AnnotationKind::Invariant,
        "terminates" => AnnotationKind::Terminates,
        _ => unreachable!(),
    };
    let p = fields.next().unwrap();
    let payload = match (kind, p.as_rule()) {
        (AnnotationKind::Terminates, Rule::termination) => {
            AnnotationPayload::Termination(TerminationKind::AlmostSure)
        }
        (AnnotationKind::Terminates, _) => {
            return Err(error(p.as_span().start(), "expected `almost_sure`"));
        }
        (_, Rule::expression) => AnnotationPayload::Expression(expression(p)?),
        _ => {
            return Err(error(
                p.as_span().start(),
                "expected a predicate expression",
            ));
        }
    };
    Ok(Annotation {
        kind,
        payload,
        span,
    })
}

pub fn parse_function(text: &str, span: SourceSpan) -> Result<SpecFunction, AnnotationParseError> {
    let mut fields = parse(Rule::function_file, text)?.into_inner();
    let name = fields.next().unwrap().as_str().to_owned();
    let mut next = fields.next().unwrap();
    let mut parameters = Vec::new();
    if next.as_rule() == Rule::parameters {
        for p in next.into_inner() {
            let mut parts = p.into_inner();
            parameters.push(Parameter {
                name: parts.next().unwrap().as_str().into(),
                ty: scalar_type(parts.next().unwrap())?,
            });
        }
        next = fields.next().unwrap();
    }
    let result = scalar_type(next)?;
    let body = expression(fields.next().unwrap())?;
    Ok(SpecFunction {
        name,
        parameters,
        result,
        body,
        span,
    })
}

fn scalar_type(p: Pair<'_, Rule>) -> Result<SpecType, AnnotationParseError> {
    let offset = p.as_span().start();
    let text = p.as_str().replace(char::is_whitespace, "");
    let (name, width) = match text.split_once('[') {
        Some((name, width)) => (
            name,
            Some(
                width
                    .trim_end_matches(']')
                    .parse::<usize>()
                    .map_err(|_| error(offset, "invalid type width"))?,
            ),
        ),
        None => (text.as_str(), None),
    };
    if width.is_some_and(|w| w == 0 || w > 64)
        || (name == "float" && width.is_some_and(|w| !matches!(w, 32 | 64)))
        || (matches!(name, "bool" | "bit" | "real") && width.is_some())
    {
        return Err(error(offset, "unsupported scalar type width"));
    }
    Ok(match name {
        "real" => SpecType::Real,
        "bool" => SpecType::Bool,
        "bit" => SpecType::Bit,
        "int" => SpecType::Int(width),
        "uint" => SpecType::Uint(width),
        "float" => SpecType::Float(width),
        "angle" => SpecType::Angle(width),
        _ => unreachable!(),
    })
}

fn expression(p: Pair<'_, Rule>) -> Result<SpecExpr, AnnotationParseError> {
    let mut fields = p.into_inner();
    let first = fields.next().unwrap();
    let mut compared = false;
    for op in first.clone().into_inner() {
        match op.as_rule() {
            Rule::eq | Rule::ne | Rule::lt | Rule::le | Rule::gt | Rule::ge => {
                if compared {
                    return Err(error(
                        op.as_span().start(),
                        "write chained comparisons using &&",
                    ));
                }
                compared = true;
            }
            Rule::and | Rule::or | Rule::implies => compared = false,
            _ => {}
        }
    }
    let condition = PRATT
        .map_primary(primary)
        .map_prefix(|op, e| {
            let operand = Box::new(e?);
            Ok(match op.as_rule() {
                Rule::pos => *operand,
                _ => SpecExpr::Unary {
                    op: if op.as_rule() == Rule::neg {
                        UnaryOp::Neg
                    } else {
                        UnaryOp::Not
                    },
                    operand,
                },
            })
        })
        .map_postfix(|e, op| {
            Ok(match op.as_rule() {
                Rule::factorial => SpecExpr::Unary {
                    op: UnaryOp::Factorial,
                    operand: Box::new(e?),
                },
                Rule::index => SpecExpr::Index {
                    value: Box::new(e?),
                    index: Box::new(expression(op.into_inner().next().unwrap())?),
                },
                _ => unreachable!(),
            })
        })
        .map_infix(|l, op, r| {
            Ok(SpecExpr::Binary {
                op: binary(op.as_rule()),
                left: Box::new(l?),
                right: Box::new(r?),
            })
        })
        .parse(first.into_inner())?;
    if let Some(then_value) = fields.next() {
        Ok(SpecExpr::Conditional {
            condition: Box::new(condition),
            then_value: Box::new(expression(then_value)?),
            else_value: Box::new(expression(fields.next().unwrap())?),
        })
    } else {
        Ok(condition)
    }
}

fn primary(p: Pair<'_, Rule>) -> Result<SpecExpr, AnnotationParseError> {
    let offset = p.as_span().start();
    Ok(match p.as_rule() {
        Rule::expression => expression(p)?,
        Rule::identifier => SpecExpr::Name(p.as_str().into()),
        Rule::boolean => SpecExpr::Bool(p.as_str() == "true"),
        Rule::infinity => SpecExpr::Infinity,
        Rule::constant => SpecExpr::Constant(match p.as_str() {
            r"\pi" => NumericConstant::Pi,
            r"\tau" => NumericConstant::Tau,
            r"\euler" => NumericConstant::Euler,
            _ => unreachable!(),
        }),
        Rule::imaginary => SpecExpr::ImaginaryUnit,
        Rule::pauli => SpecExpr::Pauli(match p.as_str() {
            r"\I" => Pauli::I,
            r"\X" => Pauli::X,
            r"\Y" => Pauli::Y,
            r"\Z" => Pauli::Z,
            _ => unreachable!(),
        }),
        Rule::ket | Rule::bra => {
            let is_ket = p.as_rule() == Rule::ket;
            let factors = state_factors(p)?;
            if is_ket {
                SpecExpr::Ket(factors)
            } else {
                SpecExpr::Bra(factors)
            }
        }
        Rule::inner_product | Rule::outer_product => {
            let is_inner = p.as_rule() == Rule::inner_product;
            let mut fields = p.into_inner();
            let left = fields.next().unwrap();
            let right = fields.next().unwrap();
            let (left, right) = if is_inner {
                (
                    SpecExpr::Bra(state_factors(left)?),
                    SpecExpr::Ket(state_factors(right)?),
                )
            } else {
                (primary(left)?, primary(right)?)
            };
            SpecExpr::Binary {
                op: BinaryOp::Mul,
                left: Box::new(left),
                right: Box::new(right),
            }
        }
        Rule::number => {
            if p.as_str().len() > 128 {
                return Err(error(offset, "numeric literal budget exceeded"));
            }
            let v =
                BigDecimal::from_str(p.as_str()).map_err(|_| error(offset, "invalid number"))?;
            let (digits, scale) = v.as_bigint_and_exponent();
            if scale.unsigned_abs() > 1024 {
                return Err(error(offset, "numeric exponent budget exceeded"));
            }
            let power = BigInt::from(10).pow(scale.unsigned_abs() as u32);
            let value = SpecExpr::Number(if scale >= 0 {
                BigRational::new(digits, power)
            } else {
                BigRational::from_integer(digits * power)
            });
            if p.as_str().contains(['.', 'e', 'E']) {
                SpecExpr::Cast {
                    ty: SpecType::Float(None),
                    operand: Box::new(value),
                }
            } else {
                value
            }
        }
        Rule::call | Rule::builtin_call => {
            let is_builtin = p.as_rule() == Rule::builtin_call;
            let mut fields = p.into_inner();
            let name = fields.next().unwrap().as_str().to_owned();
            let arguments = arguments(fields.next())?;
            if is_builtin {
                let (function, min, max) = builtin(&name[1..]).ok_or_else(|| {
                    error(offset, format!("unknown specification builtin {name}"))
                })?;
                if !(min..=max).contains(&arguments.len()) {
                    return Err(error(offset, format!("wrong argument count for `{name}`")));
                }
                SpecExpr::Call {
                    function,
                    arguments,
                }
            } else {
                SpecExpr::NamedCall { name, arguments }
            }
        }
        Rule::list => SpecExpr::List(arguments(p.into_inner().next())?),
        Rule::binder | Rule::quantifier => {
            let mut f = p.into_inner().filter(|p| p.as_rule() != Rule::in_keyword);
            let kind = match f.next().unwrap().as_str() {
                r"\sum" => BinderKind::Sum,
                r"\product" => BinderKind::Product,
                r"\forall" => BinderKind::Forall,
                r"\exists" => BinderKind::Exists,
                r"\sup" => BinderKind::Sup,
                r"\infimum" => BinderKind::Inf,
                _ => unreachable!(),
            };
            let name = f.next().unwrap().as_str().to_owned();
            let mut lo = f.next().unwrap();
            let ty = if lo.as_rule() == Rule::scalar_type {
                let t = scalar_type(lo)?;
                lo = f.next().unwrap();
                t
            } else {
                SpecType::Int(None)
            };
            let lower = Box::new(expression(lo)?);
            let inclusive = f.next().unwrap().as_str() == "..=";
            let upper = Box::new(expression(f.next().unwrap())?);
            let body = Box::new(expression(f.next().unwrap())?);
            SpecExpr::Binder {
                kind,
                variable: Parameter { name, ty },
                id: None,
                lower,
                upper,
                inclusive,
                body,
            }
        }
        _ => unreachable!("unexpected primary {:?}", p.as_rule()),
    })
}

// Used by both standalone literals and the two labels of a compact inner product.
fn state_factors(p: Pair<'_, Rule>) -> Result<Vec<QubitState>, AnnotationParseError> {
    let offset = p.as_span().start();
    let factors = p
        .into_inner()
        .map(|factor| match factor.as_str() {
            "0" => QubitState::Zero,
            "1" => QubitState::One,
            "+" => QubitState::Plus,
            "-" | "−" => QubitState::Minus,
            "+i" => QubitState::PlusI,
            "-i" | "−i" => QubitState::MinusI,
            _ => unreachable!(),
        })
        .collect::<Vec<_>>();
    if factors.len() > MAX_QUANTUM_QUBITS {
        return Err(error(offset, "quantum dimension budget exceeded"));
    }
    Ok(factors)
}

fn arguments(p: Option<Pair<'_, Rule>>) -> Result<Vec<SpecExpr>, AnnotationParseError> {
    p.map(|p| p.into_inner().map(expression).collect())
        .unwrap_or_else(|| Ok(Vec::new()))
}

fn binary(r: Rule) -> BinaryOp {
    use BinaryOp::*;
    match r {
        Rule::add => Add,
        Rule::sub => Sub,
        Rule::mul => Mul,
        Rule::tensor => Tensor,
        Rule::div => Div,
        Rule::pow => Pow,
        Rule::modulo => Mod,
        Rule::eq => Eq,
        Rule::ne => Ne,
        Rule::lt => Lt,
        Rule::le => Le,
        Rule::gt => Gt,
        Rule::ge => Ge,
        Rule::and => And,
        Rule::or => Or,
        Rule::implies => Implies,
        _ => unreachable!(),
    }
}

fn builtin(name: &str) -> Option<(MathFunction, usize, usize)> {
    use MathFunction::*;
    let f = match name {
        "real" => Real,
        "factorial" => Factorial,
        "abs" => Abs,
        "sqrt" => Sqrt,
        "exp" => Exp,
        "log" | "ln" => Log,
        "sin" => Sin,
        "cos" => Cos,
        "tan" => Tan,
        "sinh" => Sinh,
        "cosh" => Cosh,
        "tanh" => Tanh,
        "asin" => Asin,
        "acos" => Acos,
        "atan" => Atan,
        "floor" => Floor,
        "ceil" => Ceil,
        "conj" => Conjugate,
        "re" => RealPart,
        "im" => ImagPart,
        "adjoint" => Adjoint,
        "expectation" => Expectation,
        "trace" => Trace,
        "normalize" => Normalize,
        "avg_density" => AvgDensity,
        "diagonal" => Diagonal,
        "probability" => Probability,
        "binom" => return Some((Binomial, 2, 2)),
        "trace_distance" => return Some((TraceDistance, 2, 2)),
        "min" => return Some((Min, 2, 256)),
        "max" => return Some((Max, 2, 256)),
        _ => return None,
    };
    Some((f, 1, 1))
}
