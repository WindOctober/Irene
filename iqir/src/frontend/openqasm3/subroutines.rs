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
    pub(super) fn declare_annotated_subroutine(
        &mut self, definition: ast::Def, annotations: Vec<crate::annotation::Annotation>,
    ) -> Result<(), FrontendError> {
        self.register_subroutine(definition)?;
        let index = self.subroutines.len() - 1;
        if annotations.iter().all(|a| matches!(a.kind,
            crate::annotation::AnnotationKind::Requires | crate::annotation::AnnotationKind::Ensures)) {
            // Resolve in the callee's definition scope after fresh by-value
            // parameters are installed, never in the caller's lexical scope.
            self.subroutines[index].contracts = annotations;
            return Ok(());
        }
        let template = &self.subroutines[index];
        if template.return_type.is_some() {
            return Err(unsupported!("linear ket summary requires a void quantum subroutine", &template.definition));
        }
        let mut numeric = 0;
        let mut quantum = 0;
        for p in &template.parameters {
            match p.ty {
                ParameterType::Quantum(ty) => quantum += ty.width(),
                ParameterType::Classical(ValueType::Scalar(_)) => numeric += 1,
                _ => return Err(unsupported!("linear summary requires numeric and quantum parameters", &template.definition)),
            }
        }
        let summary = self.callable_summary(annotations, numeric, quantum)?;
        self.subroutines[index].summary = Some(summary);
        Ok(())
    }
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
        let mut ordered_wires = Vec::new();
        let mut summary_arguments = Vec::new();
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
                        ordered_wires.push(q.clone());
                    }
                    Argument::Quantum(value)
                }
                ParameterType::Classical(ValueType::Scalar(ty)) => {
                    let mut value = self.lower_scalar_expr(source, ty)?;
                    if template.summary.is_some() {
                        let constant = self.known_scalars.value(&value)?
                            .ok_or_else(|| unsupported!("linear def summary currently requires known numeric actuals", &call))?;
                        let scalar = self.ids.node(crate::ScalarExprData { ty, kind: constant.expression() });
                        summary_arguments.push(self.ids.node(NumericExprKind::Scalar(Box::new(scalar.clone()))));
                        value = scalar;
                    }
                    Argument::Scalar(value)
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
        // Parameterless quantum templates share the very same IR as gates.
        // Numeric def actuals are specialized with their machine types first;
        // these definitions are intentionally not cached across different values.
        if template.summary.is_some() && summary_arguments.is_empty() {
            if let Some(definition) = self.gate_definitions.get(&binding.id) {
                return Ok(self.ids.node(StatementKind::GateCall {
                    definition: definition.clone(), parameters: Vec::new(), qubits: ordered_wires,
                }));
            }
        }
        let before = self.known_scalars.clone();
        let bits_before = self.known_bits.clone();
        self.active_subroutines.insert(index);
        self.scopes.enter_definition(binding.id);
        let mut quantum_ids = Vec::new();
        let annotations_before = self.annotations.len();
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
            if !template.contracts.is_empty() {
                // The body contract ranges over formal input values, not just
                // this call's currently known actuals. Keep actual evaluation
                // in the prefix, but do not specialize its proof body with
                // caller flow facts. Source const qualification is separate.
                self.known_scalars = Default::default();
                if let Some(known) = &mut self.known_bits { *known = Default::default(); }
            }
            let mut contracts = Vec::new();
            for annotation in template.contracts.clone() {
                // Reuse the Boolean contract checker and quantum-formal mapping.
                let anchor = self.lower_assertion(vec![annotation])?;
                contracts.extend(self.annotations.remove(&anchor.ast_id()).unwrap());
            }
            // A callee's break/continue must never target its caller's loop.
            let caller_controls = std::mem::take(&mut self.loop_controls);
            let body_result = self.lower_subroutine_body(
                template
                    .definition
                    .body()
                    .ok_or_else(|| expected!("a subroutine body", &template.definition))?,
                template.return_type,
                target,
            );
            self.loop_controls = caller_controls;
            let mut body = body_result?;
            if !contracts.is_empty() {
                let boundary = self.ids.node(StatementKind::Scope(body));
                self.annotations.insert(boundary.ast_id(), contracts);
                body = self.ids.node(BlockData { statements: vec![boundary], ..Default::default() });
            }
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
        let body = result?;
        let statement = if let Some(summary) = template.summary {
            if self.annotations.len() != annotations_before {
                return Err(unsupported!("retained loop/contracts in a linear def summary require a contextual callable proof; use an ordinary def with loop contracts", &call));
            }
            let body = self.linear_subroutine_body(&body, &mut Default::default(), &mut BTreeSet::new())?;
            let definition = std::sync::Arc::new(crate::GateDefinition {
                name: id.string(),
                parameters: (0..summary_arguments.len()).map(|i| SymbolId(usize::MAX-i)).collect(),
                qubits: ordered_wires.clone(), body, summary: Some(summary),
            });
            // Validate that no free wires or unsupported effects escaped the
            // extraction. All body numeric expressions have been closed below.
            definition.instantiate(&summary_arguments, &ordered_wires, &mut self.ids)
                .map_err(|_| unsupported!("non-local quantum effect in linear subroutine summary", &call))?;
            if summary_arguments.is_empty() { self.gate_definitions.insert(binding.id, definition.clone()); }
            self.ids.node(StatementKind::GateCall {
                definition, parameters: summary_arguments, qubits: ordered_wires,
            })
        } else { self.ids.node(StatementKind::Scope(body)) };
        self.known_scalars.statement(&statement)?;
        if let Some(known) = &mut self.known_bits {
            known.statement(&statement);
        }
        Ok(statement)
    }

    /// Erase only checked, total, local classical computation. No measurement,
    /// reset, unresolved branch/loop or externally visible classical effect can
    /// be hidden behind a coherent ket summary.
    fn linear_subroutine_body(&mut self, body: &Block,
        known: &mut known_scalars::KnownScalars, locals: &mut BTreeSet<SymbolId>,
    ) -> Result<Block, FrontendError> {
        let error = || FrontendError::Unsupported {
            construct: "linear def summary requires a closed unitary body (retained loops need contextual callable proofs)",
            snippet: "subroutine summary".into(),
        };
        fn closed(e: &NumericExpr) -> bool {
            match &e.kind {
                NumericExprKind::Rational(_) | NumericExprKind::Constant(_) => true,
                NumericExprKind::Scalar(s) => s.constant_value().is_ok_and(|v| v.is_some()),
                NumericExprKind::Neg(a) => closed(a),
                NumericExprKind::Add(a,b) | NumericExprKind::Sub(a,b)
                | NumericExprKind::Mul(a,b) | NumericExprKind::Div(a,b) => closed(a) && closed(b),
                NumericExprKind::Input(_) => false,
            }
        }
        if !body.classical_registers.is_empty() { return Err(error()); }
        let mut statements = Vec::new();
        for s in &body.statements {
            match &s.kind {
                StatementKind::ScalarDeclare { id, initializer: Some(e), .. } => {
                    if known.value(e)?.is_none() { return Err(error()); }
                    known.statement(s)?; locals.insert(*id);
                }
                StatementKind::ScalarAssign { target, value } if locals.contains(target) => {
                    if known.value(value)?.is_none() { return Err(error()); }
                    known.statement(s)?;
                }
                StatementKind::Scope(b) => {
                    let mut local_known = known.clone();
                    let mut local_ids = locals.clone();
                    let b = self.linear_subroutine_body(b, &mut local_known, &mut local_ids)?;
                    statements.extend(b.statements.iter().cloned());
                    known.statement(s)?;
                }
                StatementKind::If { condition, then_branch, else_branch } => {
                    let b = match constants::eval_constant_bit(condition) {
                        Some(true) => then_branch, Some(false) => else_branch, None => return Err(error()),
                    };
                    let b = self.linear_subroutine_body(b, known, locals)?;
                    statements.extend(b.statements.iter().cloned());
                }
                StatementKind::Apply { parameters, .. } | StatementKind::GateCall { parameters, .. }
                    if parameters.iter().all(closed) => statements.push(s.clone()),
                StatementKind::GlobalPhase(p) if closed(p) => statements.push(s.clone()),
                StatementKind::Unitary { controls, power, body } => {
                    let body = self.linear_subroutine_body(body, known, locals)?;
                    statements.push(self.ids.node(StatementKind::Unitary {
                        controls: controls.clone(), power: *power, body,
                    }));
                }
                _ => return Err(error()),
            }
        }
        Ok(self.ids.node(BlockData { statements, ..BlockData::default() }))
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
