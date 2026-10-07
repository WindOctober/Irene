//! Lexical gate macros expanded into phase-exact IQIR. Composite modifiers
//! remain structured, so control and inverse never discard global phase.
use super::*;

#[derive(Clone)]
pub(super) struct CustomGate {
    definition: SymbolId,
    parameters: Vec<String>,
    qubits: Vec<String>,
    body: ast::BlockExpr,
}

fn names(list: Option<ast::ParamList>) -> Vec<String> {
    list.map(|p| p.params().map(|p| p.string()).collect())
        .unwrap_or_default()
}

pub(super) fn charge_work(work: &mut usize) -> Result<(), FrontendError> {
    if *work >= 65536 {
        return Err(FrontendError::Unsupported {
            construct: "custom gate expansion work budget",
            snippet: "gate definition/call expansion".into(),
        });
    }
    *work += 1;
    Ok(())
}

pub(super) fn charge_copy(work: &mut usize, expr: &NumericExpr) -> Result<(), FrontendError> {
    let mut pending = vec![expr];
    while let Some(e) = pending.pop() {
        charge_work(work)?;
        match &e.kind {
            NumericExprKind::Neg(a) => pending.push(a),
            NumericExprKind::Add(a, b)
            | NumericExprKind::Sub(a, b)
            | NumericExprKind::Mul(a, b)
            | NumericExprKind::Div(a, b) => {
                pending.push(a);
                pending.push(b);
            }
            _ => {}
        }
    }
    Ok(())
}

impl Lowerer {
    pub(super) fn is_composite_gate(&self, call: &ast::GateCallExpr) -> bool {
        call.identifier()
            .is_some_and(|id| id.string() == "U" || self.gates.contains_key(&id.string()))
    }

    pub(super) fn declare_custom_gate(&mut self, gate: ast::Gate) -> Result<(), FrontendError> {
        let name = declaration_name(&gate)?;
        let parameters = names(gate.angle_params());
        let qubits = names(gate.qubit_params());
        if qubits.is_empty() {
            return Err(expected!("at least one formal qubit", &gate));
        }
        let mut seen = BTreeSet::new();
        for formal in parameters.iter().chain(&qubits) {
            if !seen.insert(formal) || formal == &name {
                return Err(expected!("distinct gate formal names", &gate));
            }
        }
        let body = gate.body().ok_or_else(|| expected!("gate body", &gate))?;
        let binding = self
            .scopes
            .declare(name.clone(), BindingKind::Gate)
            .map_err(scope_error)?;
        let template = CustomGate {
            definition: binding.id,
            parameters,
            qubits,
            body,
        };
        // Like def, register the signature now and check/lower the body only
        // at a call site. Keep definition-time name visibility in its scope.
        self.gates.insert(name, template);
        Ok(())
    }

    fn expand_custom_gate(
        &mut self,
        gate: &CustomGate,
        arguments: Vec<NumericExpr>,
        qubits: Vec<Qubit>,
    ) -> Result<Block, FrontendError> {
        if self.gate_depth >= 64 {
            return Err(unsupported!("custom gate expansion depth", &gate.body));
        }
        self.gate_depth += 1;
        self.scopes.enter_definition(gate.definition);
        let mut numeric_ids = Vec::new();
        let mut quantum_ids = Vec::new();
        let result = (|| {
            for (name, value) in gate.parameters.iter().zip(arguments) {
                let binding = self
                    .scopes
                    .declare(name, BindingKind::NumericInput(NumericType::Angle(None)))
                    .map_err(scope_error)?;
                numeric_ids.push(binding.id);
                self.numeric_arguments.insert(binding.id, value);
            }
            for (name, qubit) in gate.qubits.iter().zip(qubits) {
                let binding = self
                    .scopes
                    .declare(name, BindingKind::QuantumParameter(QuantumType::Scalar))
                    .map_err(scope_error)?;
                quantum_ids.push(binding.id);
                self.quantum_arguments
                    .insert(binding.id, QuantumOperand::Scalar(qubit));
            }
            let mut statements = Vec::new();
            for statement in gate.body.statements() {
                charge_work(&mut self.gate_work)?;
                match &statement {
                    Stmt::ExprStmt(e)
                        if matches!(
                            e.expr(),
                            Some(
                                Expr::GateCallExpr(_)
                                    | Expr::ModifiedGateCallExpr(_)
                                    | Expr::GPhaseCallExpr(_)
                            )
                        ) => {}
                    Stmt::Barrier(_) => {}
                    _ => {
                        return Err(unsupported!(
                            "non-unitary statement in custom gate",
                            &statement
                        ));
                    }
                }
                statements.push(self.lower_statement(statement)?);
            }
            Ok(self.ids.node(BlockData {
                statements,
                ..BlockData::default()
            }))
        })();
        for id in numeric_ids {
            self.numeric_arguments.remove(&id);
        }
        for id in quantum_ids {
            self.quantum_arguments.remove(&id);
        }
        self.scopes.exit();
        self.gate_depth -= 1;
        result
    }

    pub(super) fn lower_global_phase(
        &mut self,
        call: ast::GPhaseCallExpr,
    ) -> Result<Statement, FrontendError> {
        let value = self.lower_numeric_expr(
            call.arg()
                .ok_or_else(|| expected!("global phase angle", &call))?,
        )?;
        Ok(self.ids.node(StatementKind::GlobalPhase(value)))
    }

    pub(super) fn lower_composite_modified_gate(
        &mut self,
        call: ast::ModifiedGateCallExpr,
    ) -> Result<Statement, FrontendError> {
        let mut controls = 0;
        let mut power = 1_i128;
        for (index, modifier) in call.modifiers().enumerate() {
            if index >= 16 {
                return Err(unsupported!("custom gate modifier budget", &call));
            }
            match modifier {
                ast::Modifier::InvModifier(_) => {
                    power = power
                        .checked_neg()
                        .ok_or_else(|| unsupported!("gate power overflow", &call))?
                }
                ast::Modifier::PowModifier(p) => {
                    let expr = p
                        .paren_expr()
                        .and_then(|e| e.expr())
                        .ok_or_else(|| expected!("static integer gate power", &p))?;
                    let k = self.known_power(expr)?;
                    power = power
                        .checked_mul(k)
                        .ok_or_else(|| unsupported!("gate power overflow", &p))?;
                }
                ast::Modifier::CtrlModifier(c) => {
                    let count = match c.paren_expr() {
                        Some(p) => self.static_index(
                            p.expr().ok_or_else(|| expected!("control count", &c))?,
                            true,
                        )?,
                        None => 1,
                    };
                    if count == 0 || count > 64 || controls > 64 - count {
                        return Err(unsupported!("control count outside 1..64", &c));
                    }
                    controls += count;
                }
                _ => return Err(unsupported!("custom gate modifier", &call)),
            }
        }
        let gate = call
            .gate_call_expr()
            .ok_or_else(|| expected!("modified gate call", &call))?;
        self.lower_composite_gate(gate, controls, power)
    }

    pub(super) fn lower_composite_gate(
        &mut self,
        call: ast::GateCallExpr,
        controls: usize,
        power: i128,
    ) -> Result<Statement, FrontendError> {
        let name = call
            .identifier()
            .ok_or_else(|| expected!("gate name", &call))?
            .string();
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        if !matches!(binding.kind, BindingKind::Gate) {
            return Err(expected!("gate binding", &call));
        }
        let template = self.gates.get(&name).cloned();
        let (np, nq) = template
            .as_ref()
            .map(|g| (g.parameters.len(), g.qubits.len()))
            .unwrap_or((3, 1));
        let sources: Vec<_> = call
            .arg_list()
            .and_then(|a| a.expression_list())
            .map(|a| a.exprs().collect())
            .unwrap_or_default();
        if sources.len() != np {
            return Err(expected!("declared gate parameter arity", &call));
        }
        let parameters = sources
            .into_iter()
            .map(|e| self.lower_numeric_expr(e))
            .collect::<Result<Vec<_>, _>>()?;
        let operands = call
            .qubit_list()
            .ok_or_else(|| expected!("gate operands", &call))?
            .gate_operands()
            .map(|q| self.lower_qubits(q))
            .collect::<Result<Vec<_>, _>>()?;
        if operands.len() != nq + controls {
            return Err(expected!(
                "declared gate qubit arity including controls",
                &call
            ));
        }
        let mut widths = operands.iter().filter_map(|q| match q {
            QuantumOperand::Scalar(_) => None,
            QuantumOperand::Register(q) => Some(q.len()),
        });
        let width = widths.next().unwrap_or(1);
        if widths.any(|w| w != width) {
            return Err(expected!(
                "equal-width or scalar custom gate operands",
                &call
            ));
        }
        let mut statements = Vec::new();
        for lane in 0..width {
            charge_work(&mut self.gate_work)?;
            self.charge_static_expansion(&call)?;
            let wires: Vec<_> = operands.iter().map(|q| q.broadcast_at(lane)).collect();
            if wires.iter().collect::<BTreeSet<_>>().len() != wires.len() {
                return Err(expected!(
                    "distinct custom gate operands including controls",
                    &call
                ));
            }
            for parameter in &parameters {
                charge_copy(&mut self.gate_work, parameter)?;
            }
            let args = parameters
                .iter()
                .map(|p| self.ids.clone_numeric_expr(p))
                .collect();
            let body = if let Some(template) = &template {
                self.expand_custom_gate(template, args, wires[controls..].to_vec())?
            } else {
                self.lower_u_body(args, wires[controls].clone())
            };
            statements.push(if controls == 0 && power == 1 {
                self.ids.node(StatementKind::Scope(body))
            } else {
                self.ids.node(StatementKind::Unitary {
                    controls: wires[..controls].to_vec(),
                    power,
                    body,
                })
            });
        }
        Ok(self.sequence(statements))
    }

    fn lower_u_body(&mut self, parameters: Vec<NumericExpr>, qubit: Qubit) -> Block {
        let [theta, phi, lambda]: [NumericExpr; 3] =
            parameters.try_into().expect("checked U arity");
        let p = self.ids.clone_numeric_expr(&phi);
        let l = self.ids.clone_numeric_expr(&lambda);
        let t = self.ids.clone_numeric_expr(&theta);
        let sum = self
            .ids
            .node(NumericExprKind::Add(Box::new(p), Box::new(l)));
        let sum = self
            .ids
            .node(NumericExprKind::Add(Box::new(t), Box::new(sum)));
        let two = self
            .ids
            .node(NumericExprKind::Rational(BigRational::from_integer(
                2.into(),
            )));
        let phase = self
            .ids
            .node(NumericExprKind::Div(Box::new(sum), Box::new(two)));
        let mut statements = vec![self.ids.node(StatementKind::GlobalPhase(phase))];
        // OpenQASM 3 U = exp(i*(theta+phi+lambda)/2) Rz(phi) Ry(theta) Rz(lambda).
        // The theta/2 phase differs from OpenQASM 2 / Qiskit's U3 convention.
        for (gate, parameter) in [(Gate::Rz, lambda), (Gate::Ry, theta), (Gate::Rz, phi)] {
            statements.push(self.ids.node(StatementKind::Apply {
                gate,
                parameters: vec![parameter],
                qubits: vec![qubit.clone()],
            }));
        }
        self.ids.node(BlockData {
            statements,
            ..BlockData::default()
        })
    }
}
