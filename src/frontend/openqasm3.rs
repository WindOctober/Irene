use std::collections::{BTreeSet, HashMap};
use std::path::PathBuf;
use std::str::FromStr;

use bigdecimal::{BigDecimal, num_bigint::BigInt};
use num_rational::BigRational;
use oq3_source_file::{SourceTrait, parse_source_string};
use oq3_syntax::BlockOrStmt;
use oq3_syntax::ast::{
    self, AstNode, Expr, GateOperand, HasArgList, HasName, HasTextNode, IndexKind, Stmt,
};
use thiserror::Error;

use crate::ir::{
    AstIdGenerator, Block, BlockData, ClassicalBit, ClassicalExpr, ClassicalExprKind, Gate,
    NumericExpr, NumericExprKind, NumericInput, NumericInputData, NumericType, OpenQasmVersion,
    Program, ProgramData, Qubit, Register, RegisterData, Statement, StatementKind,
};

use super::scope::{Binding, BindingKind, BitType, QuantumType, ScopeError, ScopeKind, ScopeStack};

#[derive(Debug, Error)]
pub enum FrontendError {
    #[error("OpenQASM parse failed: {0}")]
    Parse(String),
    #[error("unsupported OpenQASM construct: {construct}: {snippet}")]
    Unsupported {
        construct: &'static str,
        snippet: String,
    },
    #[error("identifier `{0}` is already declared in this scope")]
    DuplicateIdentifier(String),
    #[error("identifier `{0}` cannot shadow a gate")]
    CannotShadow(String),
    #[error("{declaration} declarations are not allowed in {scope} scope")]
    IllegalDeclaration {
        declaration: &'static str,
        scope: &'static str,
    },
    #[error("unknown identifier `{0}`")]
    UnknownIdentifier(String),
    #[error("identifier `{name}` is a {actual}, not a {expected}")]
    WrongIdentifierKind {
        name: String,
        expected: &'static str,
        actual: &'static str,
    },
    #[error("index {index} is outside {kind} register `{name}` of width {width}")]
    IndexOutOfBounds {
        kind: &'static str,
        name: String,
        index: usize,
        width: usize,
    },
    #[error("expected {expected}: {snippet}")]
    Expected {
        expected: &'static str,
        snippet: String,
    },
}

macro_rules! unsupported {
    ($construct:expr, $node:expr $(,)?) => {{
        let node = $node;
        FrontendError::Unsupported {
            construct: $construct,
            snippet: node.syntax().text().to_string(),
        }
    }};
}

macro_rules! expected {
    ($expected:expr, $node:expr $(,)?) => {{
        let node = $node;
        FrontendError::Expected {
            expected: $expected,
            snippet: node.syntax().text().to_string(),
        }
    }};
}

pub fn parse_str(source: &str, source_name: &str) -> Result<Program, FrontendError> {
    let parsed = parse_source_string(source, Some(source_name), None::<&[PathBuf]>);
    let syntax = parsed
        .syntax_ast()
        .ok_or_else(|| FrontendError::Parse("OpenQASM source could not be parsed".to_owned()))?;
    if !syntax.errors().is_empty() {
        let diagnostics = syntax
            .errors()
            .iter()
            .map(|error| format!("{} at {:?}", error.message(), error.range()))
            .collect::<Vec<_>>()
            .join("; ");
        return Err(FrontendError::Parse(diagnostics));
    }

    Lowerer::default().lower(syntax.tree())
}

struct Lowerer {
    ids: AstIdGenerator,
    version: Option<OpenQasmVersion>,
    scopes: ScopeStack,
    numeric_inputs: Vec<NumericInput>,
    quantum_registers: Vec<Register>,
    classical_registers: Vec<Register>,
    subroutines: Vec<SubroutineTemplate>,
    quantum_arguments: HashMap<crate::ir::SymbolId, QuantumOperand>,
    active_subroutines: BTreeSet<usize>,
}

#[derive(Clone)]
struct SubroutineTemplate {
    definition: ast::Def,
    parameters: Vec<QuantumParameter>,
    return_type: Option<BitType>,
}

#[derive(Clone)]
struct QuantumParameter {
    name: String,
    ty: QuantumType,
}

/// A resolved quantum operand before OpenQASM register broadcasting is
/// expanded into scalar core-IR operations.
#[derive(Clone)]
enum QuantumOperand {
    Scalar(Qubit),
    Register(Vec<Qubit>),
}

impl QuantumOperand {
    fn cells(&self) -> &[Qubit] {
        match self {
            Self::Scalar(qubit) => std::slice::from_ref(qubit),
            Self::Register(qubits) => qubits,
        }
    }

    fn into_cells(self) -> Vec<Qubit> {
        match self {
            Self::Scalar(qubit) => vec![qubit],
            Self::Register(qubits) => qubits,
        }
    }

    fn broadcast_at(&self, index: usize) -> Qubit {
        match self {
            Self::Scalar(qubit) => qubit.clone(),
            Self::Register(qubits) => qubits[index].clone(),
        }
    }

    fn ty(&self) -> QuantumType {
        match self {
            Self::Scalar(_) => QuantumType::Scalar,
            Self::Register(qubits) => QuantumType::Register {
                width: qubits.len(),
            },
        }
    }
}

/// A resolved classical lvalue or value before scalar/register type checking.
#[derive(Clone)]
enum BitOperand {
    Scalar(ClassicalBit),
    Register(Vec<ClassicalBit>),
}

impl BitOperand {
    fn into_cells(self) -> Vec<ClassicalBit> {
        match self {
            Self::Scalar(bit) => vec![bit],
            Self::Register(bits) => bits,
        }
    }

    fn ty(&self) -> BitType {
        match self {
            Self::Scalar(_) => BitType::Scalar,
            Self::Register(bits) => BitType::Register { width: bits.len() },
        }
    }
}

impl Default for Lowerer {
    fn default() -> Self {
        Self {
            ids: AstIdGenerator::default(),
            version: None,
            scopes: ScopeStack::new(),
            numeric_inputs: Vec::new(),
            quantum_registers: Vec::new(),
            classical_registers: Vec::new(),
            subroutines: Vec::new(),
            quantum_arguments: HashMap::new(),
            active_subroutines: BTreeSet::new(),
        }
    }
}

impl Lowerer {
    fn lower(mut self, source: ast::SourceFile) -> Result<Program, FrontendError> {
        let mut body = self.ids.node(BlockData::default());
        for statement in source.statements() {
            self.lower_top_level(statement, &mut body)?;
        }

        let version = self.version.ok_or_else(|| FrontendError::Expected {
            expected: "an OPENQASM 3 version declaration",
            snippet: "missing OPENQASM declaration".to_owned(),
        })?;
        if version.major != 3 {
            return Err(FrontendError::Unsupported {
                construct: "OpenQASM version",
                snippet: format!("{}.{}", version.major, version.minor),
            });
        }

        let program = ProgramData {
            version,
            numeric_inputs: self.numeric_inputs,
            quantum_registers: self.quantum_registers,
            classical_registers: self.classical_registers,
            body,
        };
        Ok(self.ids.node(program))
    }

    /// Lowers declarations into program metadata and executable statements into the body.
    fn lower_top_level(&mut self, statement: Stmt, body: &mut Block) -> Result<(), FrontendError> {
        match statement {
            // `OPENQASM 3.0;` declares the source-language version.
            Stmt::VersionString(version) => self.lower_version(version),
            // `include "stdgates.inc";` makes the standard gate names visible.
            Stmt::Include(include) => {
                let text = include.syntax().text().to_string();
                if text.contains("\"stdgates.inc\"") {
                    self.scopes.declare_standard_gates().map_err(scope_error)
                } else {
                    Err(unsupported!("include", &include))
                }
            }
            // `input angle[20] theta;` declares a symbolic numeric program input.
            Stmt::IODeclarationStatement(declaration) => {
                let input = self.lower_numeric_input(declaration)?;
                self.numeric_inputs.push(input);
                Ok(())
            }
            // `qubit[4] q;` allocates a four-wire quantum register.
            Stmt::QuantumDeclarationStatement(declaration) => {
                let register = self.lower_quantum_declaration(declaration)?;
                self.quantum_registers.push(register);
                Ok(())
            }
            // `bit[4] c;` allocates a four-bit classical register.
            Stmt::ClassicalDeclarationStatement(declaration) => {
                let register = self.lower_classical_declaration(declaration)?;
                self.classical_registers.push(register);
                Ok(())
            }
            // `def f(qubit q) { ... }` registers a callable template. Calls
            // are specialized into Irene's core IR when encountered.
            Stmt::Def(definition) => self.register_subroutine(definition),
            // Operations such as `h q;`, `c = measure q;`, and `if (...) { ... }`
            // belong to the executable program body.
            other => {
                body.statements.push(self.lower_statement(other)?);
                Ok(())
            }
        }
    }

    fn lower_version(&mut self, version: ast::VersionString) -> Result<(), FrontendError> {
        let text = version.syntax().text().to_string();
        let number = text
            .split_whitespace()
            .nth(1)
            .map(|part| part.trim_end_matches(';'))
            .ok_or_else(|| expected!("an OpenQASM version number", &version))?;
        let (major, minor) = number.split_once('.').unwrap_or((number, "0"));
        let parse = |part: &str| {
            part.parse::<u32>()
                .map_err(|_| expected!("an integer version component", &version))
        };
        self.version = Some(OpenQasmVersion {
            major: parse(major)?,
            minor: parse(minor)?,
        });
        Ok(())
    }

    /// Registers a subroutine signature and retains its parsed body for
    /// call-site specialization.
    ///
    /// Quantum parameters are references to caller-owned wires. The supported
    /// return type is `bit` or `bit[n]`, matching the dynamic-program
    /// benchmarks that return measurement results.
    fn register_subroutine(&mut self, definition: ast::Def) -> Result<(), FrontendError> {
        let name = declaration_name(&definition)?;
        let parameters = definition
            .typed_param_list()
            .ok_or_else(|| expected!("a subroutine parameter list", &definition))?
            .typed_params()
            .map(|parameter| {
                let name = declaration_name(&parameter)?;
                let ast::ParamType::ScalarType(ty) = parameter
                    .param_type()
                    .ok_or_else(|| expected!("a subroutine parameter type", &parameter))?
                else {
                    return Err(unsupported!("array subroutine parameter", &parameter));
                };
                if ty
                    .syntax()
                    .first_token()
                    .is_none_or(|token| token.text() != "qubit")
                {
                    return Err(unsupported!("non-quantum subroutine parameter", &parameter));
                }
                Ok(QuantumParameter {
                    name,
                    ty: quantum_type(ty.designator(), "a quantum parameter width")?,
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let return_type = definition
            .return_signature()
            .map(|signature| {
                let ty = signature
                    .scalar_type()
                    .ok_or_else(|| expected!("a subroutine return type", &signature))?;
                if ty.bit_token().is_none() {
                    return Err(unsupported!("subroutine return type other than bit", &ty));
                }
                bit_type(ty.designator(), "a subroutine return width")
            })
            .transpose()?;
        let index = self.subroutines.len();
        self.scopes
            .declare(name, BindingKind::Subroutine { index })
            .map_err(scope_error)?;
        self.subroutines.push(SubroutineTemplate {
            definition,
            parameters,
            return_type,
        });
        // Irene lowers and checks a body only when the subroutine is called;
        // unreachable definitions are outside the equivalence task.
        Ok(())
    }

    fn lower_quantum_declaration(
        &mut self,
        declaration: ast::QuantumDeclarationStatement,
    ) -> Result<Register, FrontendError> {
        let name = declaration_name(&declaration)?;
        let qubit_type = declaration
            .qubit_type()
            .ok_or_else(|| expected!("a qubit type", &declaration))?;
        let ty = quantum_type(qubit_type.designator(), "a qubit array width")?;
        let binding = self
            .scopes
            .declare(name.clone(), BindingKind::QuantumVariable(ty))
            .map_err(scope_error)?;
        Ok(self.ids.node(RegisterData {
            id: binding.id,
            name,
            width: ty.width(),
        }))
    }

    fn lower_numeric_input(
        &mut self,
        declaration: ast::IODeclarationStatement,
    ) -> Result<NumericInput, FrontendError> {
        if declaration.input_token().is_none() {
            return Err(unsupported!("output declaration", &declaration));
        }
        let name = declaration_name(&declaration)?;
        let scalar_type = declaration
            .scalar_type()
            .ok_or_else(|| expected!("a numeric input type", &declaration))?;
        let ty = numeric_type(&scalar_type)?;
        let binding = self
            .scopes
            .declare(name.clone(), BindingKind::NumericInput(ty))
            .map_err(scope_error)?;
        Ok(self.ids.node(NumericInputData {
            id: binding.id,
            name,
            ty,
        }))
    }

    fn lower_classical_declaration(
        &mut self,
        declaration: ast::ClassicalDeclarationStatement,
    ) -> Result<Register, FrontendError> {
        if declaration.const_token().is_some() {
            return Err(unsupported!("const declaration", &declaration));
        }
        let name = declaration_name(&declaration)?;
        let scalar_type = declaration
            .scalar_type()
            .ok_or_else(|| expected!("a classical scalar type", &declaration))?;
        if scalar_type.bit_token().is_none() {
            return Err(unsupported!("classical type other than bit", &scalar_type));
        }
        let ty = bit_type(scalar_type.designator(), "a bit array width")?;
        if declaration.expr().is_some() {
            return Err(unsupported!("classical initializer", &declaration));
        }
        let binding = self
            .scopes
            .declare(name.clone(), BindingKind::ClassicalBit(ty))
            .map_err(scope_error)?;
        Ok(self.ids.node(RegisterData {
            id: binding.id,
            name,
            width: ty.width(),
        }))
    }

    /// Lowers the executable statement forms currently represented by Irene's IR.
    fn lower_statement(&mut self, statement: Stmt) -> Result<Statement, FrontendError> {
        match statement {
            // `reset q[0];` reinitializes one quantum wire to |0⟩.
            Stmt::Reset(reset) => {
                let operand = reset
                    .gate_operand()
                    .ok_or_else(|| expected!("a reset operand", &reset))?;
                let statements = self
                    .lower_qubits(operand)?
                    .into_cells()
                    .into_iter()
                    .map(|qubit| self.ids.node(StatementKind::Reset(qubit)))
                    .collect();
                Ok(self.sequence(statements))
            }
            // Gate applications such as `h q[0];` are parsed as expression statements.
            Stmt::ExprStmt(expression_statement) => {
                let expression = expression_statement
                    .expr()
                    .ok_or_else(|| expected!("an expression statement", &expression_statement))?;
                match expression {
                    Expr::GateCallExpr(call) => self.lower_gate(call),
                    Expr::CallExpr(call) => self.lower_subroutine_call(call, None),
                    _ => Err(unsupported!("expression statement", &expression_statement)),
                }
            }
            // `c[0] = measure q[0];` is an assignment whose RHS is a measurement.
            Stmt::AssignmentStmt(assignment) => self.lower_assignment(assignment),
            // `if (c[0]) { x q[1]; } else { z q[1]; }` becomes two IR blocks.
            Stmt::IfStmt(if_statement) => self.lower_if(if_statement),
            // Remaining OpenQASM statements do not yet have an Irene IR form.
            other => Err(unsupported!("statement", &other)),
        }
    }

    /// Lowers `name(parameters) qubits;` into a gate kind, exact parameters,
    /// and resolved qubit operands. For example, `rz(pi/4) q[0];` retains
    /// `pi/4` as a [`NumericExpr`] rather than evaluating it as a float.
    fn lower_gate(&mut self, call: ast::GateCallExpr) -> Result<Statement, FrontendError> {
        // Parenthesized expressions before the qubit list are gate parameters.
        let parameters = call
            .arg_list()
            .and_then(|arguments| arguments.expression_list())
            .map(|arguments| {
                arguments
                    .exprs()
                    .map(|expression| self.lower_numeric_expr(expression))
                    .collect::<Result<Vec<_>, _>>()
            })
            .transpose()?
            .unwrap_or_default();
        // Resolve the source name through the current OpenQASM scope first,
        // then map supported standard-library aliases to one IR gate.
        let source_name = call
            .identifier()
            .map(|identifier| identifier.string())
            .ok_or_else(|| expected!("a gate name", &call))?;
        let binding = self.scopes.lookup(&source_name).map_err(scope_error)?;
        if !matches!(binding.kind, BindingKind::Gate) {
            return Err(FrontendError::WrongIdentifierKind {
                name: source_name,
                expected: "gate",
                actual: binding.kind.description(),
            });
        }
        let normalized_name = source_name.to_ascii_lowercase();
        let gate = match normalized_name.as_str() {
            "h" => Gate::H,
            "x" => Gate::X,
            "y" => Gate::Y,
            "z" => Gate::Z,
            "s" => Gate::S,
            "sdg" => Gate::Sdg,
            "t" => Gate::T,
            "tdg" => Gate::Tdg,
            "cx" => Gate::Cx,
            "cy" => Gate::Cy,
            "cz" => Gate::Cz,
            "swap" => Gate::Swap,
            "p" | "phase" | "u1" => Gate::P,
            "rx" => Gate::Rx,
            "ry" => Gate::Ry,
            "rz" => Gate::Rz,
            "cp" | "cphase" => Gate::Cp,
            "crx" => Gate::Crx,
            "cry" => Gate::Cry,
            "crz" => Gate::Crz,
            "ccx" => Gate::Ccx,
            _ => return Err(unsupported!("gate", &call)),
        };
        // Operands after the parameter list identify the quantum wires.
        let operands = call
            .qubit_list()
            .ok_or_else(|| expected!("a gate operand list", &call))?
            .gate_operands()
            .map(|operand| self.lower_qubits(operand))
            .collect::<Result<Vec<_>, _>>()?;
        let expected_arity = match gate {
            Gate::Cx
            | Gate::Cy
            | Gate::Cz
            | Gate::Swap
            | Gate::Cp
            | Gate::Crx
            | Gate::Cry
            | Gate::Crz => 2,
            Gate::Ccx => 3,
            _ => 1,
        };
        if operands.len() != expected_arity {
            return Err(FrontendError::Expected {
                expected: "the gate's standard number of operands",
                snippet: call.syntax().text().to_string(),
            });
        }
        let expected_parameters = match gate {
            Gate::P
            | Gate::Rx
            | Gate::Ry
            | Gate::Rz
            | Gate::Cp
            | Gate::Crx
            | Gate::Cry
            | Gate::Crz => 1,
            _ => 0,
        };
        if parameters.len() != expected_parameters {
            return Err(FrontendError::Expected {
                expected: "the gate's standard number of parameters",
                snippet: call.syntax().text().to_string(),
            });
        }
        let mut register_widths = operands.iter().filter_map(|operand| match operand {
            QuantumOperand::Scalar(_) => None,
            QuantumOperand::Register(qubits) => Some(qubits.len()),
        });
        let width = register_widths.next().unwrap_or(1);
        if register_widths.any(|operand_width| operand_width != width) {
            return Err(FrontendError::Expected {
                expected: "equally sized or scalar gate operands",
                snippet: call.syntax().text().to_string(),
            });
        }
        let expanded_qubits = (0..width)
            .map(|index| {
                operands
                    .iter()
                    .map(|operand| operand.broadcast_at(index))
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        if expanded_qubits
            .iter()
            .any(|qubits| qubits.iter().collect::<BTreeSet<_>>().len() != qubits.len())
        {
            return Err(FrontendError::Expected {
                expected: "distinct qubit operands for each gate application",
                snippet: call.syntax().text().to_string(),
            });
        }
        let statements = expanded_qubits
            .into_iter()
            .enumerate()
            .map(|(index, qubits)| {
                let parameters = if index == 0 {
                    parameters.clone()
                } else {
                    parameters
                        .iter()
                        .map(|parameter| self.clone_numeric_expr(parameter))
                        .collect()
                };
                self.ids.node(StatementKind::Apply {
                    gate,
                    parameters,
                    qubits,
                })
            })
            .collect();
        Ok(self.sequence(statements))
    }

    /// Preserves the structure of an OpenQASM numeric expression while
    /// normalizing finite literals to exact rationals.
    fn lower_numeric_expr(&mut self, expression: Expr) -> Result<NumericExpr, FrontendError> {
        match expression {
            // `7`, `0.1`, and `1e-1` become exact BigRational values.
            Expr::Literal(literal) => match literal.kind() {
                ast::LiteralKind::IntNumber(number) => {
                    let value = exact_integer(number)?;
                    Ok(self.ids.node(NumericExprKind::Rational(value)))
                }
                ast::LiteralKind::FloatNumber(number) => {
                    let value = exact_decimal(number)?;
                    Ok(self.ids.node(NumericExprKind::Rational(value)))
                }
                _ => Err(unsupported!("non-numeric gate parameter", &literal)),
            },
            // `pi` is a built-in constant, while `theta` resolves to an
            // `input angle theta;` or another numeric input declaration.
            Expr::Identifier(identifier) => {
                let name = identifier.string();
                let binding = self.scopes.lookup(&name).map_err(scope_error)?;
                match binding.kind {
                    BindingKind::Constant(constant) => {
                        Ok(self.ids.node(NumericExprKind::Constant(constant)))
                    }
                    BindingKind::NumericInput(_) => {
                        Ok(self.ids.node(NumericExprKind::Input(binding.id)))
                    }
                    actual => Err(FrontendError::WrongIdentifierKind {
                        name,
                        expected: "numeric value",
                        actual: actual.description(),
                    }),
                }
            }
            // Parentheses affect parsing precedence but need no extra IR node:
            // `(pi / 2)` lowers to the same tree as `pi / 2`.
            Expr::ParenExpr(parenthesized) => {
                self.lower_numeric_expr(parenthesized.expr().ok_or_else(|| {
                    expected!("a parenthesized numeric expression", &parenthesized)
                })?)
            }
            // `-theta` preserves negation as a symbolic expression node.
            Expr::PrefixExpr(prefix) => {
                let operand = self.lower_numeric_expr(
                    prefix
                        .expr()
                        .ok_or_else(|| expected!("a numeric prefix operand", &prefix))?,
                )?;
                match prefix.op_kind() {
                    Some(ast::UnaryOp::Neg) => {
                        Ok(self.ids.node(NumericExprKind::Neg(Box::new(operand))))
                    }
                    _ => Err(unsupported!("numeric prefix operator", &prefix)),
                }
            }
            // `theta/2 + pi/4` recursively retains its arithmetic tree.
            Expr::BinExpr(binary) => {
                let left = Box::new(
                    self.lower_numeric_expr(
                        binary
                            .lhs()
                            .ok_or_else(|| expected!("a left numeric operand", &binary))?,
                    )?,
                );
                let right = Box::new(
                    self.lower_numeric_expr(
                        binary
                            .rhs()
                            .ok_or_else(|| expected!("a right numeric operand", &binary))?,
                    )?,
                );
                match binary.op_kind() {
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Add)) => {
                        Ok(self.ids.node(NumericExprKind::Add(left, right)))
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Sub)) => {
                        Ok(self.ids.node(NumericExprKind::Sub(left, right)))
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Mul)) => {
                        Ok(self.ids.node(NumericExprKind::Mul(left, right)))
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Div)) => {
                        Ok(self.ids.node(NumericExprKind::Div(left, right)))
                    }
                    _ => Err(unsupported!("numeric binary operator", &binary)),
                }
            }
            other => Err(unsupported!("numeric gate parameter", &other)),
        }
    }

    /// Lowers measurement, Boolean, and subroutine-result assignments.
    fn lower_assignment(
        &mut self,
        assignment: ast::AssignmentStmt,
    ) -> Result<Statement, FrontendError> {
        let targets = self.lower_assignment_targets(&assignment)?;
        let rhs = assignment
            .rhs()
            .ok_or_else(|| expected!("an assignment value", &assignment))?;
        match rhs {
            Expr::MeasureExpression(measurement) => {
                let operand = measurement
                    .gate_operand()
                    .ok_or_else(|| expected!("a measurement operand", &measurement))?;
                let qubits = self.lower_qubits(operand)?;
                if !measurement_types_match(qubits.ty(), targets.ty()) {
                    return Err(FrontendError::Expected {
                        expected: "matching scalar or register measurement operands",
                        snippet: assignment.syntax().text().to_string(),
                    });
                }
                let statements = qubits
                    .into_cells()
                    .into_iter()
                    .zip(targets.into_cells())
                    .map(|(qubit, target)| self.ids.node(StatementKind::Measure { qubit, target }))
                    .collect();
                Ok(self.sequence(statements))
            }
            Expr::CallExpr(call) => self.lower_subroutine_call(call, Some(targets)),
            expression if matches!(targets, BitOperand::Scalar(_)) => {
                let value = self.lower_classical_expr(expression)?;
                let BitOperand::Scalar(target) = targets else {
                    unreachable!()
                };
                Ok(self.ids.node(StatementKind::Assign { target, value }))
            }
            expression => Err(unsupported!("register-valued assignment", &expression)),
        }
    }

    fn lower_assignment_targets(
        &self,
        assignment: &ast::AssignmentStmt,
    ) -> Result<BitOperand, FrontendError> {
        if let Some(indexed) = assignment.indexed_identifier() {
            return Ok(BitOperand::Scalar(self.lower_classical_indexed(indexed)?));
        }
        let name = assignment
            .identifier()
            .map(|identifier| identifier.string())
            .ok_or_else(|| expected!("an assignment target", assignment))?;
        self.classical_cells(name)
    }

    /// Specializes one subroutine invocation to its concrete quantum
    /// arguments and lowers the resulting body into a lexical core-IR scope.
    ///
    /// This follows OpenQASM's reference semantics: a formal `qubit[2] q`
    /// directly denotes the two caller-owned wires passed at this call site.
    fn lower_subroutine_call(
        &mut self,
        call: ast::CallExpr,
        targets: Option<BitOperand>,
    ) -> Result<Statement, FrontendError> {
        let callee = match call
            .expr()
            .ok_or_else(|| expected!("a subroutine name", &call))?
        {
            Expr::Identifier(identifier) => identifier.string(),
            expression => return Err(unsupported!("subroutine callee", &expression)),
        };
        let binding = self.scopes.lookup(&callee).map_err(scope_error)?;
        let BindingKind::Subroutine { index } = binding.kind else {
            return Err(FrontendError::WrongIdentifierKind {
                name: callee,
                expected: "subroutine",
                actual: binding.kind.description(),
            });
        };
        if self.active_subroutines.contains(&index) {
            return Err(unsupported!("recursive subroutine call", &call));
        }
        let template = self.subroutines[index].clone();
        let arguments = call
            .arg_list()
            .and_then(|arguments| arguments.expression_list())
            .map(|arguments| {
                arguments
                    .exprs()
                    .map(|argument| self.lower_quantum_argument(argument))
                    .collect::<Result<Vec<_>, _>>()
            })
            .transpose()?
            .unwrap_or_default();
        if arguments.len() != template.parameters.len() {
            return Err(FrontendError::Expected {
                expected: "the subroutine's declared number of arguments",
                snippet: call.syntax().text().to_string(),
            });
        }
        for (argument, parameter) in arguments.iter().zip(&template.parameters) {
            if argument.ty() != parameter.ty {
                return Err(FrontendError::Expected {
                    expected: "a subroutine argument matching its parameter type",
                    snippet: call.syntax().text().to_string(),
                });
            }
        }
        let unique_arguments = arguments
            .iter()
            .flat_map(QuantumOperand::cells)
            .cloned()
            .collect::<BTreeSet<_>>();
        if unique_arguments.len()
            != arguments
                .iter()
                .map(|argument| argument.cells().len())
                .sum::<usize>()
        {
            return Err(FrontendError::Expected {
                expected: "non-overlapping quantum subroutine arguments",
                snippet: call.syntax().text().to_string(),
            });
        }
        match (template.return_type, targets.as_ref()) {
            (None, Some(_)) => {
                return Err(FrontendError::Expected {
                    expected: "a value-returning subroutine",
                    snippet: call.syntax().text().to_string(),
                });
            }
            (Some(_), None) => {
                return Err(FrontendError::Expected {
                    expected: "an assignment target for the subroutine return value",
                    snippet: call.syntax().text().to_string(),
                });
            }
            (Some(return_type), Some(targets)) if return_type != targets.ty() => {
                return Err(FrontendError::Expected {
                    expected: "a call target matching the subroutine return type",
                    snippet: call.syntax().text().to_string(),
                });
            }
            _ => {}
        }

        self.active_subroutines.insert(index);
        self.scopes.enter(ScopeKind::Subroutine);
        let mut parameter_ids = Vec::new();
        for (parameter, argument) in template.parameters.iter().zip(arguments) {
            let binding = self
                .scopes
                .declare(
                    parameter.name.clone(),
                    BindingKind::QuantumParameter(parameter.ty),
                )
                .map_err(scope_error)?;
            self.quantum_arguments.insert(binding.id, argument);
            parameter_ids.push(binding.id);
        }
        let result = self.lower_subroutine_body(
            template
                .definition
                .body()
                .ok_or_else(|| expected!("a subroutine body", &template.definition))?,
            template.return_type,
            targets,
        );
        for id in parameter_ids {
            self.quantum_arguments.remove(&id);
        }
        self.scopes.exit();
        self.active_subroutines.remove(&index);
        Ok(self.ids.node(StatementKind::Scope(result?)))
    }

    fn lower_subroutine_body(
        &mut self,
        body: ast::BlockExpr,
        return_type: Option<BitType>,
        targets: Option<BitOperand>,
    ) -> Result<Block, FrontendError> {
        let source_statements = body.statements().collect::<Vec<_>>();
        let mut lowered = self.ids.node(BlockData::default());
        let mut saw_return = false;
        for (index, statement) in source_statements.iter().cloned().enumerate() {
            match statement {
                Stmt::ClassicalDeclarationStatement(declaration) => lowered
                    .classical_registers
                    .push(self.lower_classical_declaration(declaration)?),
                Stmt::QuantumDeclarationStatement(declaration) => {
                    self.lower_quantum_declaration(declaration)?;
                }
                Stmt::ExprStmt(expression_statement) => {
                    let expression = expression_statement.expr().ok_or_else(|| {
                        expected!("a subroutine-body expression", &expression_statement)
                    })?;
                    if let Expr::ReturnExpr(return_expression) = expression {
                        if index + 1 != source_statements.len() {
                            return Err(unsupported!("non-final return", &return_expression));
                        }
                        self.lower_return(
                            return_expression,
                            return_type,
                            targets.as_ref(),
                            &mut lowered,
                        )?;
                        saw_return = true;
                    } else {
                        lowered
                            .statements
                            .push(self.lower_statement(Stmt::ExprStmt(expression_statement))?);
                    }
                }
                statement => lowered.statements.push(self.lower_statement(statement)?),
            }
        }
        if return_type.is_some() && !saw_return {
            return Err(FrontendError::Expected {
                expected: "a final return value",
                snippet: body.syntax().text().to_string(),
            });
        }
        Ok(lowered)
    }

    fn lower_return(
        &mut self,
        return_expression: ast::ReturnExpr,
        return_type: Option<BitType>,
        targets: Option<&BitOperand>,
        body: &mut Block,
    ) -> Result<(), FrontendError> {
        let value = return_expression.expr();
        match (return_type, value) {
            (None, None) => Ok(()),
            (None, Some(_)) => Err(unsupported!(
                "value returned from void subroutine",
                &return_expression
            )),
            (Some(_), None) => Err(expected!("a subroutine return value", &return_expression)),
            (Some(return_type), Some(Expr::MeasureExpression(measurement))) => {
                let qubits =
                    self.lower_qubits(measurement.gate_operand().ok_or_else(|| {
                        expected!("a returned measurement operand", &measurement)
                    })?)?;
                if !measurement_types_match(qubits.ty(), return_type)
                    || targets.is_some_and(|targets| targets.ty() != return_type)
                {
                    return Err(expected!(
                        "a return value matching its declared type",
                        &return_expression
                    ));
                }
                if let Some(targets) = targets {
                    body.statements.extend(
                        qubits
                            .into_cells()
                            .into_iter()
                            .zip(targets.clone().into_cells())
                            .map(|(qubit, target)| {
                                self.ids.node(StatementKind::Measure { qubit, target })
                            }),
                    );
                }
                Ok(())
            }
            (Some(return_type), Some(value)) => {
                let values = self.lower_classical_value(value)?;
                if values.ty() != return_type
                    || targets.is_some_and(|targets| targets.ty() != return_type)
                {
                    return Err(expected!(
                        "a return value matching its declared type",
                        &return_expression
                    ));
                }
                if let Some(targets) = targets {
                    body.statements.extend(
                        values
                            .into_cells()
                            .into_iter()
                            .zip(targets.clone().into_cells())
                            .map(|(value, target)| {
                                let value = self.ids.node(ClassicalExprKind::Bit(value));
                                self.ids.node(StatementKind::Assign { target, value })
                            }),
                    );
                }
                Ok(())
            }
        }
    }

    /// Lowers an `if` statement and gives each branch its own lexical scope.
    fn lower_if(&mut self, statement: ast::IfStmt) -> Result<Statement, FrontendError> {
        let condition = self.lower_classical_expr(
            statement
                .condition()
                .ok_or_else(|| expected!("an if condition", &statement))?,
        )?;
        let mut branches = statement.syntax().children().filter_map(|node| {
            ast::BlockExpr::cast(node.clone())
                .map(BlockOrStmt::BlockExpr)
                .or_else(|| Stmt::cast(node).map(BlockOrStmt::Stmt))
        });
        let then_branch = self.lower_branch(
            branches
                .next()
                .ok_or_else(|| expected!("an if body", &statement))?,
        )?;
        let else_branch = match branches.next() {
            Some(branch) => self.lower_branch(branch)?,
            None => self.ids.node(BlockData::default()),
        };
        Ok(self.ids.node(StatementKind::If {
            condition,
            then_branch,
            else_branch,
        }))
    }

    /// Lowers either legal form of an OpenQASM control-flow body.
    ///
    /// `if (c) x q;` is represented by the same one-statement Irene block as
    /// `if (c) { x q; }`, so the internal IR does not need two branch types.
    fn lower_branch(&mut self, branch: BlockOrStmt) -> Result<Block, FrontendError> {
        match branch {
            BlockOrStmt::BlockExpr(block) => self.lower_block(block),
            BlockOrStmt::Stmt(statement) => {
                let statement = self.lower_statement(statement)?;
                Ok(self.ids.node(BlockData {
                    statements: vec![statement],
                    ..BlockData::default()
                }))
            }
        }
    }

    fn lower_block(&mut self, block: ast::BlockExpr) -> Result<Block, FrontendError> {
        self.scopes.enter(ScopeKind::Block);
        let result = self.lower_block_contents(block);
        self.scopes.exit();
        result
    }

    fn lower_block_contents(&mut self, block: ast::BlockExpr) -> Result<Block, FrontendError> {
        let mut lowered = self.ids.node(BlockData::default());
        for statement in block.statements() {
            match statement {
                // `bit local;` belongs to this block and is removed on scope exit.
                Stmt::ClassicalDeclarationStatement(declaration) => lowered
                    .classical_registers
                    .push(self.lower_classical_declaration(declaration)?),
                // A block-local qubit declaration is forwarded to the common
                // declaration logic, which rejects it according to the language rules.
                Stmt::QuantumDeclarationStatement(declaration) => {
                    self.lower_quantum_declaration(declaration)?;
                }
                // Other block members are executable statements.
                other => lowered.statements.push(self.lower_statement(other)?),
            }
        }
        Ok(lowered)
    }

    /// Lowers the Boolean expression used by classical control flow.
    fn lower_classical_expr(&mut self, expression: Expr) -> Result<ClassicalExpr, FrontendError> {
        match expression {
            // `flag` refers to a scalar bit declaration.
            Expr::Identifier(identifier) => {
                let name = identifier.string();
                let operand = self.classical_cells(name.clone())?;
                let BitOperand::Scalar(bit) = operand else {
                    return Err(FrontendError::WrongIdentifierKind {
                        name,
                        expected: "classical bit",
                        actual: "classical bit register",
                    });
                };
                Ok(self.ids.node(ClassicalExprKind::Bit(bit)))
            }
            // `flags[2]` resolves one bit from a classical register.
            Expr::IndexedIdentifier(indexed) => {
                let bit = self.lower_classical_indexed(indexed)?;
                Ok(self.ids.node(ClassicalExprKind::Bit(bit)))
            }
            // `true` and `false` become Boolean constants.
            Expr::Literal(literal) => match literal.kind() {
                ast::LiteralKind::Bool(value) => Ok(self.ids.node(ClassicalExprKind::Bool(value))),
                _ => Err(unsupported!("non-Boolean condition literal", &literal)),
            },
            // Parentheses only determine precedence in the source expression.
            Expr::ParenExpr(paren) => self.lower_classical_expr(
                paren
                    .expr()
                    .ok_or_else(|| expected!("a parenthesized expression", &paren))?,
            ),
            // `!flag` becomes Boolean negation.
            Expr::PrefixExpr(prefix) => {
                let operand = prefix
                    .expr()
                    .ok_or_else(|| expected!("a prefix operand", &prefix))?;
                match prefix.op_kind() {
                    Some(ast::UnaryOp::LogicNot) => {
                        let operand = self.lower_classical_expr(operand)?;
                        Ok(self.ids.node(ClassicalExprKind::Not(Box::new(operand))))
                    }
                    _ => Err(unsupported!("condition prefix operator", &prefix)),
                }
            }
            // Comparisons and Boolean operators recursively combine their operands;
            // for example, `a && !b` becomes `And(Bit(a), Not(Bit(b)))`.
            Expr::BinExpr(binary) => {
                let left_source = binary
                    .lhs()
                    .ok_or_else(|| expected!("a left operand", &binary))?;
                let right_source = binary
                    .rhs()
                    .ok_or_else(|| expected!("a right operand", &binary))?;
                if matches!(
                    binary.op_kind(),
                    Some(ast::BinaryOp::CmpOp(ast::CmpOp::Eq { negated: false }))
                ) && let Some(expression) =
                    self.lower_integer_register_equality(&left_source, &right_source)?
                {
                    return Ok(expression);
                }
                let left = self.lower_classical_expr(left_source)?;
                let right = self.lower_classical_expr(right_source)?;
                let left = Box::new(left);
                let right = Box::new(right);
                match binary.op_kind() {
                    Some(ast::BinaryOp::CmpOp(ast::CmpOp::Eq { negated: false })) => {
                        Ok(self.ids.node(ClassicalExprKind::Eq(left, right)))
                    }
                    Some(ast::BinaryOp::LogicOp(ast::LogicOp::And)) => {
                        Ok(self.ids.node(ClassicalExprKind::And(left, right)))
                    }
                    Some(ast::BinaryOp::LogicOp(ast::LogicOp::Or)) => {
                        Ok(self.ids.node(ClassicalExprKind::Or(left, right)))
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::BitXor)) => {
                        Ok(self.ids.node(ClassicalExprKind::Xor(left, right)))
                    }
                    _ => Err(unsupported!("condition binary operator", &binary)),
                }
            }
            _ => Err(unsupported!("classical condition", &expression)),
        }
    }

    /// Lowers `int[n](bits) == k` or `uint[n](bits) == k` to individual bit
    /// equalities. OpenQASM bit zero is the least-significant integer bit;
    /// signed integers use two's-complement representation.
    ///
    /// For example, `int[3](bits) == -2` matches the little-endian pattern
    /// `bits[0..3] = 0, 1, 1`, whereas `uint[3](bits) == 6` matches the same
    /// bits but denotes the unsigned value six.
    fn lower_integer_register_equality(
        &mut self,
        left: &Expr,
        right: &Expr,
    ) -> Result<Option<ClassicalExpr>, FrontendError> {
        let (cast, literal) = match (left, right) {
            (Expr::CastExpression(cast), literal) => (cast, literal),
            (literal, Expr::CastExpression(cast)) => (cast, literal),
            _ => return Ok(None),
        };
        let Some(ty) = cast.scalar_type() else {
            return Ok(None);
        };
        let signed = if ty.int_token().is_some() {
            true
        } else if ty.uint_token().is_some() {
            false
        } else {
            return Ok(None);
        };
        let Some(value) = exact_integer_literal(literal)? else {
            return Ok(None);
        };
        let width = ty
            .designator()
            .ok_or_else(|| expected!("an explicitly sized integer cast", cast))?
            .expr()
            .ok_or_else(|| expected!("an integer cast width", cast))
            .and_then(literal_usize)?;
        if width == 0 {
            return Err(expected!("a non-empty integer cast", cast));
        }
        let bits = self.lower_classical_value(
            cast.expr()
                .ok_or_else(|| expected!("an integer cast operand", cast))?,
        )?;
        if bits.ty() != (BitType::Register { width }) {
            return Err(expected!("an integer cast matching its bit width", cast));
        }
        let modulus = BigInt::from(1_u8) << width;
        let bit_pattern = if signed {
            let magnitude = BigInt::from(1_u8) << (width - 1);
            if value < -&magnitude || value >= magnitude {
                return Err(expected!(
                    "a signed integer literal representable at the cast width",
                    literal
                ));
            }
            if value < BigInt::from(0_u8) {
                modulus + value
            } else {
                value
            }
        } else {
            if value < BigInt::from(0_u8) || value >= modulus {
                return Err(expected!(
                    "an unsigned integer literal representable at the cast width",
                    literal
                ));
            }
            value
        };
        let mut terms = bits
            .into_cells()
            .into_iter()
            .enumerate()
            .map(|(index, bit)| {
                let bit = self.ids.node(ClassicalExprKind::Bit(bit));
                let expected_one =
                    ((&bit_pattern >> index) & BigInt::from(1_u8)) == BigInt::from(1_u8);
                if !expected_one {
                    self.ids.node(ClassicalExprKind::Not(Box::new(bit)))
                } else {
                    bit
                }
            })
            .collect::<Vec<_>>()
            .into_iter();
        let mut expression = terms
            .next()
            .ok_or_else(|| expected!("a non-empty integer cast", cast))?;
        for term in terms {
            expression = self
                .ids
                .node(ClassicalExprKind::And(Box::new(expression), Box::new(term)));
        }
        Ok(Some(expression))
    }

    /// Resolves a gate operand without erasing whether it was a scalar qubit or
    /// a register. OpenQASM broadcasting depends on that distinction even when
    /// a register has width one.
    fn lower_qubits(&self, operand: GateOperand) -> Result<QuantumOperand, FrontendError> {
        match operand {
            // `q[2]` names one wire in a quantum register.
            GateOperand::IndexedIdentifier(indexed) => {
                let (name, index) = indexed_name_and_index(indexed)?;
                Ok(QuantumOperand::Scalar(self.checked_qubit(name, index)?))
            }
            // An unindexed name retains its declared scalar/register shape.
            GateOperand::Identifier(identifier) => {
                let name = identifier.string();
                let binding = self.scopes.lookup(&name).map_err(scope_error)?;
                self.quantum_cells(&name, binding)
            }
            // `$3` identifies a hardware qubit, which the logical IR does not yet model.
            GateOperand::HardwareQubit(hardware) => {
                Err(unsupported!("physical qubit operand", &hardware))
            }
        }
    }

    fn lower_quantum_argument(&self, expression: Expr) -> Result<QuantumOperand, FrontendError> {
        match expression {
            Expr::Identifier(identifier) => {
                let name = identifier.string();
                let binding = self.scopes.lookup(&name).map_err(scope_error)?;
                self.quantum_cells(&name, binding)
            }
            Expr::IndexedIdentifier(indexed) => {
                let (name, index) = indexed_name_and_index(indexed)?;
                Ok(QuantumOperand::Scalar(self.checked_qubit(name, index)?))
            }
            expression => Err(unsupported!("quantum subroutine argument", &expression)),
        }
    }

    fn quantum_cells(&self, name: &str, binding: Binding) -> Result<QuantumOperand, FrontendError> {
        match binding.kind {
            BindingKind::QuantumVariable(QuantumType::Scalar) => {
                Ok(QuantumOperand::Scalar(Qubit {
                    register: binding.id,
                    index: 0,
                }))
            }
            BindingKind::QuantumVariable(QuantumType::Register { width }) => {
                Ok(QuantumOperand::Register(
                    (0..width)
                        .map(|index| Qubit {
                            register: binding.id,
                            index,
                        })
                        .collect(),
                ))
            }
            BindingKind::QuantumParameter(_) => Ok(self.quantum_arguments[&binding.id].clone()),
            actual => Err(FrontendError::WrongIdentifierKind {
                name: name.to_owned(),
                expected: "quantum register or parameter",
                actual: actual.description(),
            }),
        }
    }

    fn lower_classical_indexed(
        &self,
        indexed: ast::IndexedIdentifier,
    ) -> Result<ClassicalBit, FrontendError> {
        let (name, index) = indexed_name_and_index(indexed)?;
        self.checked_classical_bit(name, index)
    }

    fn checked_qubit(&self, name: String, index: usize) -> Result<Qubit, FrontendError> {
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        let ty = quantum_type_of(&name, binding.kind)?;
        let QuantumType::Register { width } = ty else {
            return Err(FrontendError::WrongIdentifierKind {
                name,
                expected: "quantum register",
                actual: binding.kind.description(),
            });
        };
        check_index(&name, index, width)?;
        match binding.kind {
            BindingKind::QuantumParameter(_) => {
                let QuantumOperand::Register(qubits) = &self.quantum_arguments[&binding.id] else {
                    unreachable!()
                };
                Ok(qubits[index].clone())
            }
            BindingKind::QuantumVariable(_) => Ok(Qubit {
                register: binding.id,
                index,
            }),
            _ => unreachable!(),
        }
    }

    fn checked_classical_bit(
        &self,
        name: String,
        index: usize,
    ) -> Result<ClassicalBit, FrontendError> {
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        let BindingKind::ClassicalBit(BitType::Register { width }) = binding.kind else {
            return Err(FrontendError::WrongIdentifierKind {
                name,
                expected: "classical bit register",
                actual: binding.kind.description(),
            });
        };
        check_index(&name, index, width)?;
        Ok(ClassicalBit {
            register: binding.id,
            index,
        })
    }

    fn classical_cells(&self, name: String) -> Result<BitOperand, FrontendError> {
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        match binding.kind {
            BindingKind::ClassicalBit(BitType::Scalar) => Ok(BitOperand::Scalar(ClassicalBit {
                register: binding.id,
                index: 0,
            })),
            BindingKind::ClassicalBit(BitType::Register { width }) => Ok(BitOperand::Register(
                (0..width)
                    .map(|index| ClassicalBit {
                        register: binding.id,
                        index,
                    })
                    .collect(),
            )),
            actual => Err(FrontendError::WrongIdentifierKind {
                name,
                expected: "classical bit or register",
                actual: actual.description(),
            }),
        }
    }

    fn lower_classical_value(&self, expression: Expr) -> Result<BitOperand, FrontendError> {
        match expression {
            Expr::Identifier(identifier) => self.classical_cells(identifier.string()),
            Expr::IndexedIdentifier(indexed) => {
                Ok(BitOperand::Scalar(self.lower_classical_indexed(indexed)?))
            }
            expression => Err(unsupported!("subroutine return expression", &expression)),
        }
    }

    fn sequence(&mut self, mut statements: Vec<Statement>) -> Statement {
        if statements.len() == 1 {
            return statements.pop().unwrap();
        }
        let body = self.ids.node(BlockData {
            statements,
            ..BlockData::default()
        });
        self.ids.node(StatementKind::Scope(body))
    }

    fn clone_numeric_expr(&mut self, expression: &NumericExpr) -> NumericExpr {
        let kind = match &expression.kind {
            NumericExprKind::Rational(value) => NumericExprKind::Rational(value.clone()),
            NumericExprKind::Constant(value) => NumericExprKind::Constant(*value),
            NumericExprKind::Input(value) => NumericExprKind::Input(*value),
            NumericExprKind::Neg(inner) => {
                NumericExprKind::Neg(Box::new(self.clone_numeric_expr(inner)))
            }
            NumericExprKind::Add(left, right) => NumericExprKind::Add(
                Box::new(self.clone_numeric_expr(left)),
                Box::new(self.clone_numeric_expr(right)),
            ),
            NumericExprKind::Sub(left, right) => NumericExprKind::Sub(
                Box::new(self.clone_numeric_expr(left)),
                Box::new(self.clone_numeric_expr(right)),
            ),
            NumericExprKind::Mul(left, right) => NumericExprKind::Mul(
                Box::new(self.clone_numeric_expr(left)),
                Box::new(self.clone_numeric_expr(right)),
            ),
            NumericExprKind::Div(left, right) => NumericExprKind::Div(
                Box::new(self.clone_numeric_expr(left)),
                Box::new(self.clone_numeric_expr(right)),
            ),
        };
        self.ids.node(kind)
    }
}

/// Extracts the declared source name shared by register and input declarations.
fn declaration_name<T>(node: &T) -> Result<String, FrontendError>
where
    T: HasName + AstNode,
{
    node.name()
        .map(|name| name.string())
        .ok_or_else(|| expected!("a name", node))
}

/// Splits an indexed identifier such as `q[2]` into `("q", 2)`.
fn indexed_name_and_index(
    indexed: ast::IndexedIdentifier,
) -> Result<(String, usize), FrontendError> {
    let name = indexed
        .identifier()
        .map(|identifier| identifier.string())
        .ok_or_else(|| expected!("an indexed identifier name", &indexed))?;
    let mut operators = indexed.index_operators();
    let operator = operators
        .next()
        .ok_or_else(|| expected!("one index", &indexed))?;
    if operators.next().is_some() {
        return Err(unsupported!("multi-dimensional index", &indexed));
    }
    let Some(IndexKind::ExpressionList(list)) = operator.index_kind() else {
        return Err(unsupported!("index set or range", &operator));
    };
    let mut expressions = list.exprs();
    let expression = expressions
        .next()
        .ok_or_else(|| expected!("one index expression", &list))?;
    if expressions.next().is_some() {
        return Err(unsupported!("multiple indices", &list));
    }
    Ok((name, literal_usize(expression)?))
}

/// Reads a compile-time non-negative integer used as a width or array index.
/// For example, the designator in `qubit[16] q;` becomes `16`.
fn literal_usize(expression: Expr) -> Result<usize, FrontendError> {
    let text = expression.syntax().text().to_string().replace('_', "");
    text.parse::<usize>().map_err(|_| FrontendError::Expected {
        expected: "a non-negative integer literal",
        snippet: text,
    })
}

/// Converts an integer token of any OpenQASM radix into an exact rational.
/// For example, `0xff` becomes `255/1`.
fn exact_integer(number: ast::IntNumber) -> Result<BigRational, FrontendError> {
    Ok(BigRational::from_integer(exact_integer_value(number)?))
}

/// Reads an optionally negated integer literal without applying a finite host
/// integer width. Parentheses are ignored, so `-(0b10)` denotes exactly `-2`.
fn exact_integer_literal(expression: &Expr) -> Result<Option<BigInt>, FrontendError> {
    match expression {
        Expr::Literal(literal) => match literal.kind() {
            ast::LiteralKind::IntNumber(number) => exact_integer_value(number).map(Some),
            _ => Ok(None),
        },
        Expr::ParenExpr(parenthesized) => exact_integer_literal(
            &parenthesized
                .expr()
                .ok_or_else(|| expected!("a parenthesized integer literal", parenthesized))?,
        ),
        Expr::PrefixExpr(prefix) if prefix.op_kind() == Some(ast::UnaryOp::Neg) => {
            exact_integer_literal(
                &prefix
                    .expr()
                    .ok_or_else(|| expected!("an integer prefix operand", prefix))?,
            )
            .map(|value| value.map(|value| -value))
        }
        _ => Ok(None),
    }
}

fn exact_integer_value(number: ast::IntNumber) -> Result<BigInt, FrontendError> {
    let (_, digits, suffix) = number.split_into_parts();
    if !suffix.is_empty() {
        return Err(FrontendError::Expected {
            expected: "an unsuffixed integer literal",
            snippet: number.to_string(),
        });
    }
    let digits = digits.replace('_', "");
    let integer =
        BigInt::parse_bytes(digits.as_bytes(), number.radix() as u32).ok_or_else(|| {
            FrontendError::Expected {
                expected: "an integer literal",
                snippet: number.to_string(),
            }
        })?;
    Ok(integer)
}

/// Converts a finite decimal or scientific token without passing through `f64`.
/// For example, `1.25e-3` becomes exactly `1/800`.
fn exact_decimal(number: ast::FloatNumber) -> Result<BigRational, FrontendError> {
    let (decimal, suffix) = number.split_into_parts();
    if !suffix.is_empty() {
        return Err(FrontendError::Expected {
            expected: "an unsuffixed decimal gate parameter",
            snippet: number.to_string(),
        });
    }
    let decimal =
        BigDecimal::from_str(&decimal.replace('_', "")).map_err(|_| FrontendError::Expected {
            expected: "a finite decimal gate parameter",
            snippet: number.to_string(),
        })?;
    let (digits, exponent) = decimal.into_bigint_and_exponent();
    let magnitude =
        u32::try_from(exponent.unsigned_abs()).map_err(|_| FrontendError::Expected {
            expected: "a representable decimal exponent",
            snippet: number.to_string(),
        })?;
    let power = BigInt::from(10_u8).pow(magnitude);
    if exponent >= 0 {
        Ok(BigRational::new(digits, power))
    } else {
        Ok(BigRational::from_integer(digits * power))
    }
}

/// Preserves both the numeric kind and optional precision of an input type.
/// For example, `angle[20]` becomes `NumericType::Angle(Some(20))`.
fn numeric_type(scalar_type: &ast::ScalarType) -> Result<NumericType, FrontendError> {
    let width = scalar_type
        .designator()
        .map(|_| type_width(scalar_type, "a numeric type width"))
        .transpose()?;
    if scalar_type.int_token().is_some() {
        Ok(NumericType::Int(width))
    } else if scalar_type.uint_token().is_some() {
        Ok(NumericType::Uint(width))
    } else if scalar_type.float_token().is_some() {
        Ok(NumericType::Float(width))
    } else if scalar_type.angle_token().is_some() {
        Ok(NumericType::Angle(width))
    } else {
        Err(unsupported!("non-numeric input type", scalar_type))
    }
}

fn type_width(
    scalar_type: &ast::ScalarType,
    expected_width: &'static str,
) -> Result<usize, FrontendError> {
    scalar_type
        .designator()
        .map(|designator| {
            literal_usize(
                designator
                    .expr()
                    .ok_or_else(|| expected!(expected_width, &designator))?,
            )
        })
        .transpose()
        .map(|width| width.unwrap_or(1))
}

fn quantum_type(
    designator: Option<ast::Designator>,
    expected_width: &'static str,
) -> Result<QuantumType, FrontendError> {
    match designator {
        Some(designator) => Ok(QuantumType::Register {
            width: literal_usize(
                designator
                    .expr()
                    .ok_or_else(|| expected!(expected_width, &designator))?,
            )?,
        }),
        None => Ok(QuantumType::Scalar),
    }
}

fn bit_type(
    designator: Option<ast::Designator>,
    expected_width: &'static str,
) -> Result<BitType, FrontendError> {
    match designator {
        Some(designator) => Ok(BitType::Register {
            width: literal_usize(
                designator
                    .expr()
                    .ok_or_else(|| expected!(expected_width, &designator))?,
            )?,
        }),
        None => Ok(BitType::Scalar),
    }
}

fn measurement_types_match(quantum: QuantumType, classical: BitType) -> bool {
    match (quantum, classical) {
        (QuantumType::Scalar, BitType::Scalar) => true,
        (
            QuantumType::Register {
                width: quantum_width,
            },
            BitType::Register {
                width: classical_width,
            },
        ) => quantum_width == classical_width,
        _ => false,
    }
}

fn quantum_type_of(name: &str, kind: BindingKind) -> Result<QuantumType, FrontendError> {
    match kind {
        BindingKind::QuantumVariable(ty) | BindingKind::QuantumParameter(ty) => Ok(ty),
        actual => Err(FrontendError::WrongIdentifierKind {
            name: name.to_owned(),
            expected: "qubit or quantum register",
            actual: actual.description(),
        }),
    }
}

fn check_index(name: &str, index: usize, width: usize) -> Result<(), FrontendError> {
    if index >= width {
        return Err(FrontendError::IndexOutOfBounds {
            kind: "register",
            name: name.to_owned(),
            index,
            width,
        });
    }
    Ok(())
}

fn scope_error(error: ScopeError) -> FrontendError {
    match error {
        ScopeError::AlreadyDeclared(name) => FrontendError::DuplicateIdentifier(name),
        ScopeError::CannotShadow(name) => FrontendError::CannotShadow(name),
        ScopeError::IllegalDeclaration { declaration, scope } => {
            FrontendError::IllegalDeclaration {
                declaration,
                scope: match scope {
                    ScopeKind::Global => "global",
                    ScopeKind::Block => "block",
                    ScopeKind::Subroutine => "subroutine",
                },
            }
        }
        ScopeError::Unknown(name) => FrontendError::UnknownIdentifier(name),
    }
}
