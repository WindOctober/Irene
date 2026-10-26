//! Builtin mathematical calls: typed symbolic nodes and certified closed evaluation.
//! Directed MPFR bounds must round to the same IEEE value: never approximate
//! a proof constant with an arbitrary fixed-precision transcendental result.
use super::*;
use crate::{ScalarType, ScalarValue};
use rug::{Float, float::Round};

#[derive(Clone, Copy)]
pub(super) enum Function {
    Sin,
    Cos,
    Tan,
    Asin,
    Acos,
    Atan,
    Sqrt,
    Exp,
    Log,
    Floor,
    Ceiling,
}

impl Lowerer {
    pub(super) fn builtin_math_call(
        &self,
        call: &ast::CallExpr,
    ) -> Result<(Function, Expr), FrontendError> {
        let Some(Expr::Identifier(id)) = call.expr() else {
            return Err(unsupported!("builtin math callee", call));
        };
        let name = id.string();
        // A user declaration must not silently acquire builtin semantics.
        if self.scopes.lookup(&name).is_ok() {
            return Err(unsupported!("shadowed builtin math function", call));
        }
        let function = match name.as_str() {
            "sin" => Function::Sin,
            "cos" => Function::Cos,
            "tan" => Function::Tan,
            "arcsin" => Function::Asin,
            "arccos" => Function::Acos,
            "arctan" => Function::Atan,
            "sqrt" => Function::Sqrt,
            "exp" => Function::Exp,
            "log" => Function::Log,
            "floor" => Function::Floor,
            "ceiling" => Function::Ceiling,
            _ => return Err(unsupported!("builtin math function", call)),
        };
        let arguments: Vec<_> = call
            .arg_list()
            .and_then(|list| list.expression_list())
            .map(|list| list.exprs().collect())
            .unwrap_or_default();
        if arguments.len() != 1 {
            return Err(expected!("exactly one numeric math argument", call));
        }
        Ok((function, arguments.into_iter().next().unwrap()))
    }
}

impl Function {
    pub(super) fn symbolic(self) -> Option<crate::FloatUnary> {
        Some(match self {
            Self::Floor => crate::FloatUnary::Floor,
            Self::Ceiling => crate::FloatUnary::Ceiling,
            Self::Sqrt => crate::FloatUnary::Sqrt,
            Self::Acos => crate::FloatUnary::Acos,
            Self::Sin => crate::FloatUnary::Sin,
            Self::Asin => crate::FloatUnary::Asin,
            Self::Log => crate::FloatUnary::Log,
            _ => return None,
        })
    }

    fn apply(self, value: &mut Float, round: Round) {
        match self {
            Self::Sin => {
                value.sin_round(round);
            }
            Self::Cos => {
                value.cos_round(round);
            }
            Self::Tan => {
                value.tan_round(round);
            }
            Self::Asin => {
                value.asin_round(round);
            }
            Self::Acos => {
                value.acos_round(round);
            }
            Self::Atan => {
                value.atan_round(round);
            }
            Self::Sqrt => {
                value.sqrt_round(round);
            }
            Self::Exp => {
                value.exp_round(round);
            }
            Self::Log => {
                value.ln_round(round);
            }
            Self::Floor => value.floor_mut(),
            Self::Ceiling => value.ceil_mut(),
        }
    }

    pub(super) fn evaluate(self, input: f64, ty: ScalarType) -> Result<ScalarValue, &'static str> {
        if !input.is_finite() {
            return Err("non-finite constant math argument");
        }
        if let Some(operation) = self.symbolic() {
            let input = ScalarValue::Float64(input.to_bits()).to_float(ty)?;
            let result = operation.evaluate(input)?;
            return if result.as_float().unwrap().is_finite() {
                Ok(result)
            } else {
                Err("non-finite constant math result")
            };
        }
        crate::scalar::rounded_float_math(
            ScalarValue::Float64(input.to_bits()).to_float(ty)?,
            |v, round| self.apply(v, round),
        )
    }
}
