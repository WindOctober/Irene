use std::path::PathBuf;
use std::str::FromStr;

use bigdecimal::{BigDecimal, num_bigint::BigInt};
use num_rational::BigRational;
use oq3_source_file::{SourceTrait, parse_source_string};
use oq3_syntax::ast::{
    self, AstNode, Expr, GateOperand, HasArgList, HasName, HasTextName, IndexKind, Stmt,
};
use thiserror::Error;

use crate::ir::{
    Block, ClassicalBit, ClassicalExpr, Gate, NumericConstant, NumericExpr, NumericInput,
    NumericType, OpenQasmVersion, Program, Qubit, Register, Statement,
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
    numeric_inputs: Vec<NumericInput>,
    quantum_registers: Vec<Register>,
    classical_registers: Vec<Register>,
}

impl Default for Lowerer {
    fn default() -> Self {
        Self {
            version: None,
            scopes: ScopeStack::new(),
            numeric_inputs: Vec::new(),
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
            numeric_inputs: self.numeric_inputs,
            quantum_registers: self.quantum_registers,
            classical_registers: self.classical_registers,
            body,
        })
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
        Ok(NumericInput {
            id: binding.id,
            name,
            ty,
        })
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

    /// Lowers the executable statement forms currently represented by Irene's IR.
    fn lower_statement(&mut self, statement: Stmt) -> Result<Statement, FrontendError> {
        match statement {
            // `reset q[0];` reinitializes one quantum wire to |0⟩.
            Stmt::Reset(reset) => {
                let operand = reset
                    .gate_operand()
                    .ok_or_else(|| expected!("a reset operand", &reset))?;
                Ok(Statement::Reset(self.lower_qubit(operand)?))
            }
            // Gate applications such as `h q[0];` are parsed as expression statements.
            Stmt::ExprStmt(expression_statement) => {
                let expression = expression_statement
                    .expr()
                    .ok_or_else(|| expected!("an expression statement", &expression_statement))?;
                match expression {
                    Expr::GateCallExpr(call) => self.lower_gate(call),
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
    fn lower_gate(&self, call: ast::GateCallExpr) -> Result<Statement, FrontendError> {
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
            _ => return Err(unsupported!("gate", &call)),
        };
        // Operands after the parameter list identify the quantum wires.
        let qubits = call
            .qubit_list()
            .ok_or_else(|| expected!("a gate operand list", &call))?
            .gate_operands()
            .map(|operand| self.lower_qubit(operand))
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
            _ => 1,
        };
        if qubits.len() != expected_arity {
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
        Ok(Statement::Apply {
            gate,
            parameters,
            qubits,
        })
    }

    /// Preserves the structure of an OpenQASM numeric expression while
    /// normalizing finite literals to exact rationals.
    fn lower_numeric_expr(&self, expression: Expr) -> Result<NumericExpr, FrontendError> {
        match expression {
            // `7`, `0.1`, and `1e-1` become exact BigRational values.
            Expr::Literal(literal) => match literal.kind() {
                ast::LiteralKind::IntNumber(number) => {
                    Ok(NumericExpr::Rational(exact_integer(number)?))
                }
                ast::LiteralKind::FloatNumber(number) => {
                    Ok(NumericExpr::Rational(exact_decimal(number)?))
                }
                _ => Err(unsupported!("non-numeric gate parameter", &literal)),
            },
            // `pi` is a built-in constant, while `theta` resolves to an
            // `input angle theta;` or another numeric input declaration.
            Expr::Identifier(identifier) => {
                let name = identifier.string();
                match name.as_str() {
                    "pi" | "π" => Ok(NumericExpr::Constant(NumericConstant::Pi)),
                    "tau" | "τ" => Ok(NumericExpr::Constant(NumericConstant::Tau)),
                    "euler" | "ℇ" => Ok(NumericExpr::Constant(NumericConstant::Euler)),
                    _ => {
                        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
                        if matches!(binding.kind, BindingKind::NumericInput(_)) {
                            Ok(NumericExpr::Input(binding.id))
                        } else {
                            Err(FrontendError::WrongIdentifierKind {
                                name,
                                expected: "numeric input",
                                actual: binding.kind.description(),
                            })
                        }
                    }
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
                    Some(ast::UnaryOp::Neg) => Ok(NumericExpr::Neg(Box::new(operand))),
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
                        Ok(NumericExpr::Add(left, right))
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Sub)) => {
                        Ok(NumericExpr::Sub(left, right))
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Mul)) => {
                        Ok(NumericExpr::Mul(left, right))
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Div)) => {
                        Ok(NumericExpr::Div(left, right))
                    }
                    _ => Err(unsupported!("numeric binary operator", &binary)),
                }
            }
            other => Err(unsupported!("numeric gate parameter", &other)),
        }
    }

    /// Lowers the currently supported assignment form, for example
    /// `result = measure q[0];`.
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

    /// Lowers an `if` statement and gives each branch its own lexical scope.
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
    fn lower_classical_expr(&self, expression: Expr) -> Result<ClassicalExpr, FrontendError> {
        match expression {
            // `flag` refers to a scalar bit declaration.
            Expr::Identifier(identifier) => Ok(ClassicalExpr::Bit(
                self.checked_classical_bit(identifier.string(), 0)?,
            )),
            // `flags[2]` resolves one bit from a classical register.
            Expr::IndexedIdentifier(indexed) => {
                Ok(ClassicalExpr::Bit(self.lower_classical_indexed(indexed)?))
            }
            // `true` and `false` become Boolean constants.
            Expr::Literal(literal) => match literal.kind() {
                ast::LiteralKind::Bool(value) => Ok(ClassicalExpr::Bool(value)),
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
                    Some(ast::UnaryOp::LogicNot) => Ok(ClassicalExpr::Not(Box::new(
                        self.lower_classical_expr(operand)?,
                    ))),
                    _ => Err(unsupported!("condition prefix operator", &prefix)),
                }
            }
            // Comparisons and Boolean operators recursively combine their operands;
            // for example, `a && !b` becomes `And(Bit(a), Not(Bit(b)))`.
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

    /// Resolves one gate operand to an IR qubit.
    fn lower_qubit(&self, operand: GateOperand) -> Result<Qubit, FrontendError> {
        match operand {
            // `q[2]` names one wire in a quantum register.
            GateOperand::IndexedIdentifier(indexed) => {
                let (name, index) = indexed_name_and_index(indexed)?;
                self.checked_qubit(name, index)
            }
            // `q` is accepted without an index only when its declared width is one.
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
            // `$3` identifies a hardware qubit, which the logical IR does not yet model.
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
    let (_, digits, suffix) = number.split_into_parts();
    if !suffix.is_empty() {
        return Err(FrontendError::Expected {
            expected: "an unsuffixed integer gate parameter",
            snippet: number.to_string(),
        });
    }
    let digits = digits.replace('_', "");
    let integer =
        BigInt::parse_bytes(digits.as_bytes(), number.radix() as u32).ok_or_else(|| {
            FrontendError::Expected {
                expected: "an integer gate parameter",
                snippet: number.to_string(),
            }
        })?;
    Ok(BigRational::from_integer(integer))
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
        .map(|designator| {
            literal_usize(
                designator
                    .expr()
                    .ok_or_else(|| expected!("a numeric type width", &designator))?,
            )
        })
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
