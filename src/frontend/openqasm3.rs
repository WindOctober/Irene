use std::path::PathBuf;

use oq3_source_file::{SourceTrait, parse_source_string};
use oq3_syntax::ast::{
    self, AstNode, Expr, GateOperand, HasArgList, HasName, HasTextName, IndexKind, Stmt,
};
use thiserror::Error;

use crate::ir::{
    Block, ClassicalBit, ClassicalExpr, Gate, OpenQasmVersion, Program, Qubit, Register, Statement,
};

use super::scope::{BindingKind, ScopeError, ScopeKind, ScopeStack};

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
    let syntax = parsed.syntax_ast();
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
    version: Option<OpenQasmVersion>,
    scopes: ScopeStack,
    quantum_registers: Vec<Register>,
    classical_registers: Vec<Register>,
}

impl Default for Lowerer {
    fn default() -> Self {
        Self {
            version: None,
            scopes: ScopeStack::new(),
            quantum_registers: Vec::new(),
            classical_registers: Vec::new(),
        }
    }
}

impl Lowerer {
    fn lower(mut self, source: ast::SourceFile) -> Result<Program, FrontendError> {
        let mut body = Block::default();
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

        Ok(Program {
            version,
            quantum_registers: self.quantum_registers,
            classical_registers: self.classical_registers,
            body,
        })
    }

    fn lower_top_level(&mut self, statement: Stmt, body: &mut Block) -> Result<(), FrontendError> {
        match statement {
            Stmt::VersionString(version) => self.lower_version(version),
            Stmt::Include(include) => {
                let text = include.syntax().text().to_string();
                if text.contains("\"stdgates.inc\"") {
                    self.scopes.declare_standard_gates().map_err(scope_error)
                } else {
                    Err(unsupported!("include", &include))
                }
            }
            Stmt::QuantumDeclarationStatement(declaration) => {
                let register = self.lower_quantum_declaration(declaration)?;
                self.quantum_registers.push(register);
                Ok(())
            }
            Stmt::ClassicalDeclarationStatement(declaration) => {
                let register = self.lower_classical_declaration(declaration)?;
                self.classical_registers.push(register);
                Ok(())
            }
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

    fn lower_quantum_declaration(
        &mut self,
        declaration: ast::QuantumDeclarationStatement,
    ) -> Result<Register, FrontendError> {
        let name = declaration_name(&declaration)?;
        let qubit_type = declaration
            .qubit_type()
            .ok_or_else(|| expected!("a qubit type", &declaration))?;
        let width = match qubit_type.designator() {
            Some(designator) => literal_usize(
                designator
                    .expr()
                    .ok_or_else(|| expected!("a qubit array width", &designator))?,
            )?,
            None => 1,
        };
        self.declare_register(name, width, true)
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
        let width = match scalar_type.designator() {
            Some(designator) => literal_usize(
                designator
                    .expr()
                    .ok_or_else(|| expected!("a bit array width", &designator))?,
            )?,
            None => 1,
        };
        if declaration.expr().is_some() {
            return Err(unsupported!("classical initializer", &declaration));
        }
        self.declare_register(name, width, false)
    }

    fn declare_register(
        &mut self,
        name: String,
        width: usize,
        quantum: bool,
    ) -> Result<Register, FrontendError> {
        let kind = if quantum {
            BindingKind::QuantumRegister { width }
        } else {
            BindingKind::ClassicalBit { width }
        };
        let binding = self
            .scopes
            .declare(name.clone(), kind)
            .map_err(scope_error)?;
        Ok(Register {
            id: binding.id,
            name,
            width,
        })
    }

    fn lower_statement(&mut self, statement: Stmt) -> Result<Statement, FrontendError> {
        match statement {
            Stmt::Reset(reset) => {
                let operand = reset
                    .gate_operand()
                    .ok_or_else(|| expected!("a reset operand", &reset))?;
                Ok(Statement::Reset(self.lower_qubit(operand)?))
            }
            Stmt::ExprStmt(expression_statement) => {
                let expression = expression_statement
                    .expr()
                    .ok_or_else(|| expected!("an expression statement", &expression_statement))?;
                match expression {
                    Expr::GateCallExpr(call) => self.lower_gate(call),
                    _ => Err(unsupported!("expression statement", &expression_statement)),
                }
            }
            Stmt::AssignmentStmt(assignment) => self.lower_assignment(assignment),
            Stmt::IfStmt(if_statement) => self.lower_if(if_statement),
            other => Err(unsupported!("statement", &other)),
        }
    }

    fn lower_gate(&self, call: ast::GateCallExpr) -> Result<Statement, FrontendError> {
        if call
            .arg_list()
            .and_then(|arguments| arguments.expression_list())
            .is_some_and(|arguments| arguments.exprs().next().is_some())
        {
            return Err(unsupported!("parameterized gate", &call));
        }
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
            _ => return Err(unsupported!("gate", &call)),
        };
        let qubits = call
            .qubit_list()
            .ok_or_else(|| expected!("a gate operand list", &call))?
            .gate_operands()
            .map(|operand| self.lower_qubit(operand))
            .collect::<Result<Vec<_>, _>>()?;
        let expected_arity = match gate {
            Gate::Cx | Gate::Cy | Gate::Cz | Gate::Swap => 2,
            _ => 1,
        };
        if qubits.len() != expected_arity {
            return Err(FrontendError::Expected {
                expected: "the gate's standard number of operands",
                snippet: call.syntax().text().to_string(),
            });
        }
        Ok(Statement::Apply { gate, qubits })
    }

    fn lower_assignment(
        &self,
        assignment: ast::AssignmentStmt,
    ) -> Result<Statement, FrontendError> {
        let target = if let Some(indexed) = assignment.indexed_identifier() {
            self.lower_classical_indexed(indexed)?
        } else {
            let name = assignment
                .identifier()
                .map(|identifier| identifier.string())
                .ok_or_else(|| expected!("an assignment target", &assignment))?;
            self.checked_classical_bit(name, 0)?
        };
        let rhs = assignment
            .rhs()
            .ok_or_else(|| expected!("an assignment value", &assignment))?;
        let Expr::MeasureExpression(measurement) = rhs else {
            return Err(unsupported!(
                "assignment other than measurement",
                &assignment,
            ));
        };
        let operand = measurement
            .gate_operand()
            .ok_or_else(|| expected!("a measurement operand", &measurement))?;
        Ok(Statement::Measure {
            qubit: self.lower_qubit(operand)?,
            target,
        })
    }

    fn lower_if(&mut self, statement: ast::IfStmt) -> Result<Statement, FrontendError> {
        let condition = self.lower_classical_expr(
            statement
                .condition()
                .ok_or_else(|| expected!("an if condition", &statement))?,
        )?;
        let then_branch = self.lower_block(
            statement
                .then_branch()
                .ok_or_else(|| expected!("an if body", &statement))?,
        )?;
        let else_branch = match statement.else_branch() {
            Some(block) => self.lower_block(block)?,
            None => Block::default(),
        };
        Ok(Statement::If {
            condition,
            then_branch,
            else_branch,
        })
    }

    fn lower_block(&mut self, block: ast::BlockExpr) -> Result<Block, FrontendError> {
        self.scopes.enter(ScopeKind::Block);
        let result = self.lower_block_contents(block);
        self.scopes.exit();
        result
    }

    fn lower_block_contents(&mut self, block: ast::BlockExpr) -> Result<Block, FrontendError> {
        let mut lowered = Block::default();
        for statement in block.statements() {
            match statement {
                Stmt::ClassicalDeclarationStatement(declaration) => lowered
                    .classical_registers
                    .push(self.lower_classical_declaration(declaration)?),
                Stmt::QuantumDeclarationStatement(declaration) => {
                    self.lower_quantum_declaration(declaration)?;
                }
                other => lowered.statements.push(self.lower_statement(other)?),
            }
        }
        Ok(lowered)
    }

    fn lower_classical_expr(&self, expression: Expr) -> Result<ClassicalExpr, FrontendError> {
        match expression {
            Expr::Identifier(identifier) => Ok(ClassicalExpr::Bit(
                self.checked_classical_bit(identifier.string(), 0)?,
            )),
            Expr::IndexedIdentifier(indexed) => {
                Ok(ClassicalExpr::Bit(self.lower_classical_indexed(indexed)?))
            }
            Expr::Literal(literal) => match literal.kind() {
                ast::LiteralKind::Bool(value) => Ok(ClassicalExpr::Bool(value)),
                _ => Err(unsupported!("non-Boolean condition literal", &literal)),
            },
            Expr::ParenExpr(paren) => self.lower_classical_expr(
                paren
                    .expr()
                    .ok_or_else(|| expected!("a parenthesized expression", &paren))?,
            ),
            Expr::PrefixExpr(prefix) => {
                let operand = prefix
                    .expr()
                    .ok_or_else(|| expected!("a prefix operand", &prefix))?;
                match prefix.op_kind() {
                    Some(ast::UnaryOp::LogicNot) => Ok(ClassicalExpr::Not(Box::new(
                        self.lower_classical_expr(operand)?,
                    ))),
                    _ => Err(unsupported!("condition prefix operator", &prefix)),
                }
            }
            Expr::BinExpr(binary) => {
                let left = self.lower_classical_expr(
                    binary
                        .lhs()
                        .ok_or_else(|| expected!("a left operand", &binary))?,
                )?;
                let right = self.lower_classical_expr(
                    binary
                        .rhs()
                        .ok_or_else(|| expected!("a right operand", &binary))?,
                )?;
                let left = Box::new(left);
                let right = Box::new(right);
                match binary.op_kind() {
                    Some(ast::BinaryOp::CmpOp(ast::CmpOp::Eq { negated: false })) => {
                        Ok(ClassicalExpr::Eq(left, right))
                    }
                    Some(ast::BinaryOp::LogicOp(ast::LogicOp::And)) => {
                        Ok(ClassicalExpr::And(left, right))
                    }
                    Some(ast::BinaryOp::LogicOp(ast::LogicOp::Or)) => {
                        Ok(ClassicalExpr::Or(left, right))
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::BitXor)) => {
                        Ok(ClassicalExpr::Xor(left, right))
                    }
                    _ => Err(unsupported!("condition binary operator", &binary)),
                }
            }
            _ => Err(unsupported!("classical condition", &expression)),
        }
    }

    fn lower_qubit(&self, operand: GateOperand) -> Result<Qubit, FrontendError> {
        match operand {
            GateOperand::IndexedIdentifier(indexed) => {
                let (name, index) = indexed_name_and_index(indexed)?;
                self.checked_qubit(name, index)
            }
            GateOperand::Identifier(identifier) => {
                let name = identifier.string();
                let binding = self.scopes.lookup(&name).map_err(scope_error)?;
                let width = quantum_width(name.as_str(), binding.kind)?;
                if width != 1 {
                    return Err(FrontendError::Expected {
                        expected: "an indexed qubit operand",
                        snippet: name,
                    });
                }
                self.checked_qubit(name, 0)
            }
            GateOperand::HardwareQubit(hardware) => {
                Err(unsupported!("physical qubit operand", &hardware))
            }
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
        let width = quantum_width(&name, binding.kind)?;
        check_index(&name, index, width)?;
        Ok(Qubit {
            register: binding.id,
            index,
        })
    }

    fn checked_classical_bit(
        &self,
        name: String,
        index: usize,
    ) -> Result<ClassicalBit, FrontendError> {
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        let BindingKind::ClassicalBit { width, .. } = binding.kind else {
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
}

fn declaration_name<T>(node: &T) -> Result<String, FrontendError>
where
    T: HasName + AstNode,
{
    node.name()
        .map(|name| name.string())
        .ok_or_else(|| expected!("a name", node))
}

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

fn literal_usize(expression: Expr) -> Result<usize, FrontendError> {
    let text = expression.syntax().text().to_string().replace('_', "");
    text.parse::<usize>().map_err(|_| FrontendError::Expected {
        expected: "a non-negative integer literal",
        snippet: text,
    })
}

fn quantum_width(name: &str, kind: BindingKind) -> Result<usize, FrontendError> {
    match kind {
        BindingKind::QuantumRegister { width } => Ok(width),
        actual => Err(FrontendError::WrongIdentifierKind {
            name: name.to_owned(),
            expected: "quantum register",
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
                },
            }
        }
        ScopeError::Unknown(name) => FrontendError::UnknownIdentifier(name),
    }
}
