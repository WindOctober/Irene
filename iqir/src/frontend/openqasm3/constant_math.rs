//! Builtin mathematical calls: typed symbolic nodes and certified closed evaluation.
//! Directed MPFR bounds must round to the same IEEE value: never approximate
//! a proof constant with an arbitrary fixed-precision transcendental result.
use super::*;
use crate::FloatUnary as Function;

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
