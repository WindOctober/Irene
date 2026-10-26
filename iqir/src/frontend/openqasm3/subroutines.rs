//! Call-site lowering: quantum references and fresh, by-value classical locals.
use super::*;
use crate::{ScalarExpr, ScalarType};

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ValueType {
    Bits(BitType),
    Scalar(ScalarType),
}
#[derive(Clone, Copy)]
pub(super) enum ParameterType {
    Quantum(QuantumType),
    Classical(ValueType),
}
#[derive(Clone)]
pub(super) struct Parameter {
    pub(super) name: String,
    pub(super) ty: ParameterType,
    pub(super) explicit_width: bool,
}
#[derive(Clone)]
pub(super) enum CallTarget {
    Bits(BitOperand),
    Scalar { id: SymbolId, ty: ScalarType },
}
enum Argument {
    Quantum(QuantumOperand),
    Bits(TypedClassicalExpr),
    Scalar(ScalarExpr),
}

impl Lowerer {
    pub(super) fn subroutine_value_type(
        &self,
        ty: &ast::ScalarType,
    ) -> Result<ValueType, FrontendError> {
        if ty.bool_token().is_some() {
            if ty.designator().is_some() {
                return Err(expected!("a scalar bool type", ty));
            }
            Ok(ValueType::Bits(BitType::Bool))
        } else if ty.bit_token().is_some() {
            Ok(ValueType::Bits(self.static_bit_type(
                ty.designator(),
                "a subroutine bit width",
            )?))
        } else if ty.uint_token().is_some() && !self.preserve_uint {
            // Use the same storage choice as mutable declarations, including
            // the whole-source fallback from scalar uint to Boolean words.
            Ok(ValueType::Bits(self.uint_storage_type(ty)?))
        } else {
            Ok(ValueType::Scalar(self.scalar_type(ty)?))
        }
    }

    pub(super) fn is_subroutine_call(&self, call: &ast::CallExpr) -> bool {
        matches!(call.expr(), Some(Expr::Identifier(id)) if matches!(self.scopes.lookup(&id.string()), Ok(Binding { kind: BindingKind::Subroutine { .. }, .. })))
    }

    pub(super) fn lower_scalar_value_assignment(
        &mut self,
        id: SymbolId,
        ty: ScalarType,
        source: Expr,
    ) -> Result<Statement, FrontendError> {
        if let Expr::CallExpr(call) = &source {
            if self.is_subroutine_call(call) {
                return self
                    .lower_subroutine_call(call.clone(), Some(CallTarget::Scalar { id, ty }));
            }
        }
        let value = self.lower_scalar_expr(source, ty)?;
        Ok(self
            .ids
            .node(StatementKind::ScalarAssign { target: id, value }))
    }

    pub(super) fn lower_subroutine_call(
        &mut self,
        call: ast::CallExpr,
        target: Option<CallTarget>,
    ) -> Result<Statement, FrontendError> {
        let Some(Expr::Identifier(id)) = call.expr() else {
            return Err(expected!("a subroutine name", &call));
        };
        let binding = self.scopes.lookup(&id.string()).map_err(scope_error)?;
        let BindingKind::Subroutine { index } = binding.kind else {
            return Err(expected!("a declared subroutine", &call));
        };
        if self.active_subroutines.contains(&index) || self.active_subroutines.len() >= 64 {
            return Err(unsupported!(
                "recursive subroutine call or call depth budget",
                &call
            ));
        }
        self.charge_static_expansion(&call)?;
        self.subroutine_calls_left = self
            .subroutine_calls_left
            .checked_sub(1)
            .ok_or_else(|| unsupported!("subroutine expansion budget", &call))?;
        let template = self.subroutines[index].clone();
        let sources = call
            .arg_list()
            .and_then(|a| a.expression_list())
            .map(|a| a.exprs().collect::<Vec<_>>())
            .unwrap_or_default();
        if sources.len() != template.parameters.len() {
            return Err(expected!(
                "the subroutine's declared number of arguments",
                &call
            ));
        }
        let compatible = match (template.return_type, &target) {
            (None, None) => true,
            (Some(ValueType::Bits(a)), Some(CallTarget::Bits(b))) => {
                bit_types_compatible(a, b.ty())
            }
            (Some(ValueType::Scalar(a)), Some(CallTarget::Scalar { ty: b, .. })) => a == *b,
            _ => false,
        };
        if !compatible {
            return Err(expected!(
                "a call target matching the subroutine return type (void calls have no target)",
                &call
            ));
        }
        // Resolve ALL actuals in the caller before entering the callee scope.
        // Classical expressions are copied before executing any body statement.
        let mut arguments = Vec::new();
        let mut wires = BTreeSet::new();
        for (source, parameter) in sources.into_iter().zip(&template.parameters) {
            let argument = match parameter.ty {
                ParameterType::Quantum(ty) => {
                    let value = self.lower_quantum_argument(source)?;
                    if value.ty() != ty {
                        return Err(expected!("a matching quantum argument shape", &call));
                    }
                    for q in value.cells() {
                        if !wires.insert(q.clone()) {
                            return Err(expected!(
                                "non-overlapping quantum subroutine arguments",
                                &call
                            ));
                        }
                    }
                    Argument::Quantum(value)
                }
                ParameterType::Classical(ValueType::Scalar(ty)) => {
                    Argument::Scalar(self.lower_scalar_expr(source, ty)?)
                }
                ParameterType::Classical(ValueType::Bits(ty)) => {
                    let value = self.lower_word_value(source, ty)?;
                    if value
                        .word_type()
                        .is_none_or(|found| !bit_types_compatible(found, ty))
                    {
                        return Err(expected!(
                            "a classical argument matching its parameter type",
                            &call
                        ));
                    }
                    Argument::Bits(value)
                }
            };
            arguments.push(argument);
        }
        let before = self.known_scalars.clone();
        let bits_before = self.known_bits.clone();
        self.active_subroutines.insert(index);
        self.scopes.enter_definition(binding.id);
        let mut quantum_ids = Vec::new();
        let result = (|| {
            let mut prefix = BlockData::default();
            for (parameter, argument) in template.parameters.iter().zip(arguments) {
                match (parameter.ty, argument) {
                    (ParameterType::Quantum(ty), Argument::Quantum(value)) => {
                        let b = self
                            .scopes
                            .declare(parameter.name.clone(), BindingKind::QuantumParameter(ty))
                            .map_err(scope_error)?;
                        self.quantum_arguments.insert(b.id, value);
                        quantum_ids.push(b.id);
                    }
                    (ParameterType::Classical(ValueType::Scalar(ty)), Argument::Scalar(value)) => {
                        let b = self
                            .scopes
                            .declare(
                                parameter.name.clone(),
                                BindingKind::Scalar {
                                    ty,
                                    explicit_width: parameter.explicit_width,
                                    is_const: false,
                                    assignable: true,
                                    value: None,
                                },
                            )
                            .map_err(scope_error)?;
                        self.known_scalars.declare(b.id, Some(&value))?;
                        prefix
                            .statements
                            .push(self.ids.node(StatementKind::ScalarDeclare {
                                id: b.id,
                                name: parameter.name.clone(),
                                ty,
                                explicit_width: parameter.explicit_width,
                                initializer: Some(value),
                            }));
                    }
                    (ParameterType::Classical(ValueType::Bits(ty)), Argument::Bits(value)) => {
                        let b = self
                            .scopes
                            .declare(parameter.name.clone(), BindingKind::ClassicalBit(ty))
                            .map_err(scope_error)?;
                        prefix.classical_registers.push(self.ids.node(RegisterData {
                            id: b.id,
                            name: parameter.name.clone(),
                            width: ty.width(),
                        }));
                        let assign = self.assign_bit_values(
                            bit_operand(b.id, ty),
                            value,
                            call.syntax().text().to_string(),
                        )?;
                        if let Some(known) = &mut self.known_bits {
                            known.statement(&assign);
                        }
                        prefix.statements.push(assign);
                    }
                    _ => unreachable!("actual argument types checked"),
                }
            }
            let body_result = self.lower_subroutine_body(
                template
                    .definition
                    .body()
                    .ok_or_else(|| expected!("a subroutine body", &template.definition))?,
                template.return_type,
                target,
            );
            let mut body = body_result?;
            prefix.statements.append(&mut body.statements);
            prefix
                .classical_registers
                .append(&mut body.classical_registers);
            body.statements = prefix.statements;
            body.classical_registers = prefix.classical_registers;
            Ok(body)
        })();
        for id in quantum_ids {
            self.quantum_arguments.remove(&id);
        }
        self.scopes.exit();
        self.active_subroutines.remove(&index);
        self.known_scalars = before;
        self.known_bits = bits_before;
        let statement = self.ids.node(StatementKind::Scope(result?));
        self.known_scalars.statement(&statement)?;
        if let Some(known) = &mut self.known_bits {
            known.statement(&statement);
        }
        Ok(statement)
    }

    /// A direct if-call executes once before its branch, not once per use or
    /// once before an entire while. Embedded short-circuit calls stay unsupported.
    pub(super) fn lower_call_condition(
        &mut self,
        call: ast::CallExpr,
    ) -> Result<(Register, Statement, ClassicalExpr), FrontendError> {
        let b = self
            .scopes
            .declare(
                format!("$condition{}", self.ids.clone().node(()).ast_id().index()),
                BindingKind::ClassicalBit(BitType::Bool),
            )
            .map_err(scope_error)?;
        let register = self.ids.node(RegisterData {
            id: b.id,
            name: "$call_condition".into(),
            width: 1,
        });
        let bit = ClassicalBit {
            register: b.id,
            index: 0,
        };
        let mut facts = self.known_bits.clone().unwrap_or_default();
        let statement = self
            .lower_subroutine_call(call, Some(CallTarget::Bits(BitOperand::Bool(bit.clone()))))?;
        // Reuse known-bit analysis for a specialized Boolean return even in
        // programs without pow. Keep the CALL in the prefix: a known result
        // does not make measurements or quantum effects removable.
        facts.statement(&statement);
        let mut condition = self.ids.node(ClassicalExprKind::Bit(bit));
        if let Some(value) = facts.value(&condition) {
            condition.kind = ClassicalExprKind::Bool(value);
        }
        Ok((register, statement, condition))
    }
}
