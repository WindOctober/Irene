//! Lexically scoped OpenQASM 2 gate macros. Definitions are validated even
//! when unused; calls expand only already-declared gates, never recurse.
use super::*;
use oq3_syntax::ast::HasName;

#[derive(Clone)]
pub(super) struct CustomGate {
    pub parameters: Vec<String>,
    pub qubits: Vec<String>,
    body: Vec<Stmt>,
    // None denotes the native gate with this name; Some pins a macro definition.
    gates: BTreeMap<String, Option<Rc<CustomGate>>>,
}

pub(super) struct GateFrame {
    pub parameters: BTreeMap<String, (NumericExpr, ConstantValue)>,
    pub qubits: BTreeMap<String, Qubit>,
    pub gates: BTreeMap<String, Option<Rc<CustomGate>>>,
}

fn formal_names(list: Option<ast::ParamList>) -> Result<Vec<String>, FrontendError> {
    let Some(list) = list else {
        return Ok(Vec::new());
    };
    let names = list
        .params()
        .map(|p| {
            let name = p.string();
            validate_identifier(&name)?;
            Ok(name)
        })
        .collect::<Result<Vec<_>, FrontendError>>()?;
    validate_comma_list(list.syntax(), names.len(), "comma-separated formal names")?;
    Ok(names)
}

fn validate_parameter(expr: Expr, parameters: &[String]) -> Result<(), FrontendError> {
    match expr {
        Expr::Identifier(ref id) if id.string() == "pi" || parameters.contains(&id.string()) => {
            Ok(())
        }
        Expr::Literal(ref lit)
            if matches!(
                lit.kind(),
                ast::LiteralKind::IntNumber(_) | ast::LiteralKind::FloatNumber(_)
            ) =>
        {
            Ok(())
        }
        Expr::ParenExpr(ref e) => validate_parameter(
            e.expr().ok_or_else(|| expected!("numeric expression", e))?,
            parameters,
        ),
        Expr::PrefixExpr(ref e) if matches!(e.op_kind(), Some(ast::UnaryOp::Neg)) => {
            validate_parameter(
                e.expr().ok_or_else(|| expected!("numeric operand", e))?,
                parameters,
            )
        }
        Expr::BinExpr(ref e)
            if matches!(
                e.op_kind(),
                Some(ast::BinaryOp::ArithOp(
                    ast::ArithOp::Add | ast::ArithOp::Sub | ast::ArithOp::Mul | ast::ArithOp::Div
                ))
            ) =>
        {
            validate_parameter(
                e.lhs().ok_or_else(|| expected!("numeric operand", e))?,
                parameters,
            )?;
            validate_parameter(
                e.rhs().ok_or_else(|| expected!("numeric operand", e))?,
                parameters,
            )
        }
        _ => Err(unsupported!(
            "gate parameter expression outside formal scope",
            &expr
        )),
    }
}

impl Lowerer {
    pub(super) fn install_qiskit_extensions(&mut self) -> Result<(), FrontendError> {
        let parsed = oq3_syntax::SourceFile::parse_check_lex(include_str!("qiskit_extensions.inc"));
        assert!(
            parsed.errors().is_empty(),
            "embedded extension library must parse: {:?}",
            parsed.errors()
        );
        for statement in parsed.tree().statements() {
            let Stmt::Gate(gate) = statement else {
                unreachable!("only gate definitions")
            };
            let name = gate.name().unwrap().string();
            self.declare_custom_gate(gate)?;
            self.extension_gates.insert(name);
        }
        Ok(())
    }

    pub(super) fn declare_custom_gate(&mut self, gate: ast::Gate) -> Result<(), FrontendError> {
        let name = gate
            .name()
            .ok_or_else(|| expected!("gate name", &gate))?
            .syntax()
            .text()
            .to_string();
        validate_identifier(&name)?;
        let parameters = formal_names(gate.angle_params())?;
        let qubits = formal_names(gate.qubit_params())?;
        if qubits.is_empty() {
            return Err(expected!("at least one formal qubit", &gate));
        }
        let mut seen = BTreeSet::new();
        for formal in parameters.iter().chain(&qubits) {
            if formal == "pi" || !seen.insert(formal) {
                return Err(expected!("distinct formal names other than pi", &gate));
            }
        }
        let body = gate.body().ok_or_else(|| expected!("gate body", &gate))?;
        if body
            .syntax()
            .children_with_tokens()
            .filter_map(|x| x.into_token())
            .any(|t| t.kind() == SyntaxKind::SEMICOLON)
        {
            return Err(expected!("no empty gate-body statements", &body));
        }
        let statements = body.statements().collect::<Vec<_>>();
        let mut gates = BTreeMap::new();
        for statement in &statements {
            let (operands, arity) = match statement {
                Stmt::Barrier(b) if b.qubit_list().is_none() => continue,
                Stmt::Barrier(b) => (b.qubit_list(), None),
                Stmt::ExprStmt(e) => {
                    let Some(Expr::GateCallExpr(call)) = e.expr() else {
                        return Err(unsupported!("non-gate operation in gate body", statement));
                    };
                    let called = call
                        .identifier()
                        .ok_or_else(|| expected!("gate name", &call))?
                        .string();
                    // Resolve at declaration time: disallow recursion, forward
                    // references, global variables, and formal-name gate calls.
                    if called == name || seen.contains(&called) {
                        return Err(unsupported!("recursive or shadowed gate call", &call));
                    }
                    let binding = self.scopes.lookup(&called).map_err(scope_error)?;
                    if !matches!(binding.kind, BindingKind::Gate) {
                        return Err(expected!("a previously declared gate", &call));
                    }
                    let (np, nq) = if let Some(g) = self.custom_gates.get(&called) {
                        (g.parameters.len(), g.qubits.len())
                    } else {
                        gate_definition(&called)
                            .ok_or_else(|| unsupported!("gate", &call))?
                            .signature()
                    };
                    let args = call.arg_list();
                    if called == "CX" && args.is_some() {
                        return Err(expected!("CX without parentheses", &call));
                    }
                    let mut count = 0;
                    if let Some(args) = args {
                        if let Some(list) = args.expression_list() {
                            let expressions = list.exprs().collect::<Vec<_>>();
                            count = expressions.len();
                            validate_comma_list(list.syntax(), count, "gate parameters")?;
                            for expr in expressions {
                                validate_parameter(expr, &parameters)?;
                            }
                        } else {
                            validate_comma_list(args.syntax(), 0, "empty parameters")?;
                        }
                    }
                    if count != np {
                        return Err(expected!("declared gate parameter arity", &call));
                    }
                    gates.insert(called.clone(), self.custom_gates.get(&called).cloned());
                    (call.qubit_list(), Some(nq))
                }
                _ => {
                    return Err(unsupported!(
                        "non-unitary or declaration statement in gate body",
                        statement
                    ));
                }
            };
            let operands = operands.ok_or_else(|| expected!("formal qubit operands", statement))?;
            let operands_vec = operands.gate_operands().collect::<Vec<_>>();
            validate_comma_list(operands.syntax(), operands_vec.len(), "gate body operands")?;
            if arity.is_some_and(|n| n != operands_vec.len()) {
                return Err(expected!("declared gate operand arity", statement));
            }
            let mut used = BTreeSet::new();
            for operand in operands_vec {
                let GateOperand::Identifier(id) = operand else {
                    return Err(unsupported!(
                        "indexed or physical qubit in gate body",
                        &operand
                    ));
                };
                if !qubits.contains(&id.string()) || (arity.is_some() && !used.insert(id.string()))
                {
                    return Err(expected!("distinct formal qubit operands", &id));
                }
            }
        }
        // ccz is an Irene convenience extension, not a canonical qelib1 gate.
        // An explicit source definition takes precedence over that extension.
        if !self.extension_gates.remove(&name)
            && !(name == "ccz" && self.qelib1_loaded && !self.custom_gates.contains_key(&name))
        {
            self.scopes
                .declare(name.clone(), BindingKind::Gate)
                .map_err(scope_error)?;
        }
        self.custom_gates.insert(
            name,
            Rc::new(CustomGate {
                parameters,
                qubits,
                body: statements,
                gates,
            }),
        );
        Ok(())
    }

    pub(super) fn expand_custom_gate(
        &mut self,
        gate: &CustomGate,
        parameters: Vec<NumericExpr>,
        constants: Vec<ConstantValue>,
        qubits: Vec<Qubit>,
    ) -> Result<Statement, FrontendError> {
        let frame = GateFrame {
            parameters: gate
                .parameters
                .iter()
                .cloned()
                .zip(parameters.into_iter().zip(constants))
                .collect(),
            qubits: gate.qubits.iter().cloned().zip(qubits).collect(),
            gates: gate.gates.clone(),
        };
        let previous = self.gate_frame.replace(frame);
        let result = gate
            .body
            .iter()
            .cloned()
            .map(|s| self.lower_quantum_operation(s))
            .collect::<Result<Vec<_>, _>>();
        self.gate_frame = previous;
        result.map(|statements| self.sequence(statements))
    }
}
