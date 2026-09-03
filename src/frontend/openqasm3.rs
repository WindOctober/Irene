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
    Program, ProgramData, Qubit, Register, RegisterData, Statement, StatementKind, SymbolId,
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

/// Parses one OpenQASM 3 source file and lowers its supported subset to Irene IR.
///
/// `source_name` is used only in parser diagnostics. Includes other than
/// `stdgates.inc` are not followed, so the returned [`Program`] is always
/// derived from this source string alone.
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

/// Mutable context shared by one source-to-IR lowering pass.
///
/// It owns the lexical symbol table and the single [`AstIdGenerator`] used by
/// all emitted nodes. Subroutine definitions remain as syntax until a call is
/// specialized to concrete caller-owned qubits.
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

/// Parsed information retained for lowering a later subroutine call.
///
/// For example, `def reset_one(qubit q) { reset q; }` stores the formal `q`
/// and its body; calling `reset_one(data[2])` lowers that body for `data[2]`.
#[derive(Clone)]
struct SubroutineTemplate {
    definition: ast::Def,
    parameters: Vec<QuantumParameter>,
    return_type: Option<BitType>,
}

/// Name and scalar/register shape of a quantum subroutine parameter.
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
    /// Views either operand shape as the quantum wires it denotes.
    fn cells(&self) -> &[Qubit] {
        match self {
            Self::Scalar(qubit) => std::slice::from_ref(qubit),
            Self::Register(qubits) => qubits,
        }
    }

    /// Consumes the source shape after an operation has been scalarized.
    fn into_cells(self) -> Vec<Qubit> {
        match self {
            Self::Scalar(qubit) => vec![qubit],
            Self::Register(qubits) => qubits,
        }
    }

    /// Selects one wire while expanding a register-wide gate call.
    ///
    /// In `cx control, targets`, a scalar `control` is reused for every index,
    /// while a register operand contributes its wire at `index`.
    fn broadcast_at(&self, index: usize) -> Qubit {
        match self {
            Self::Scalar(qubit) => qubit.clone(),
            Self::Register(qubits) => qubits[index].clone(),
        }
    }

    /// Recovers the source-level scalar/register distinction.
    fn ty(&self) -> QuantumType {
        match self {
            Self::Scalar(_) => QuantumType::Scalar,
            Self::Register(qubits) => QuantumType::Register {
                width: qubits.len(),
            },
        }
    }
}

/// A resolved classical storage operand before scalar/register type checking.
///
/// `bit result` denotes one [`ClassicalBit`], while `bit[n] results` denotes
/// every cell of a register. Computed values such as `results ^ mask` use
/// [`TypedClassicalExpr`] instead.
#[derive(Clone)]
enum BitOperand {
    Bool(ClassicalBit),
    Bit(ClassicalBit),
    Register(Vec<ClassicalBit>),
}

impl BitOperand {
    /// Consumes the operand after shape checking and returns its storage cells.
    fn into_cells(self) -> Vec<ClassicalBit> {
        match self {
            Self::Bool(bit) | Self::Bit(bit) => vec![bit],
            Self::Register(bits) => bits,
        }
    }

    /// Returns whether the source operand was `bool`, `bit`, or `bit[n]`.
    fn ty(&self) -> BitType {
        match self {
            Self::Bool(_) => BitType::Bool,
            Self::Bit(_) => BitType::Bit,
            Self::Register(bits) => BitType::Register { width: bits.len() },
        }
    }
}

/// A typed classical expression before it is lowered to Boolean core IR.
///
/// Bit registers and integer casts share the same little-endian Boolean cells,
/// but integer values additionally retain signedness. Integer literals remain
/// exact until an operation supplies the width and signedness needed to encode
/// them. For example, `int[3](bits)` is a signed three-cell `Integer`, while
/// `-2` remains `IntegerLiteral(-2)` until the comparison is lowered. After
/// type checking, scalar `bool` and `bit` intentionally share the Boolean IR.
enum TypedClassicalExpr {
    Bool(ClassicalExpr),
    Bit(ClassicalExpr),
    Register(Vec<ClassicalExpr>),
    Integer {
        bits: Vec<ClassicalExpr>,
        signedness: Signedness,
    },
    IntegerLiteral(BigInt),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Signedness {
    Signed,
    Unsigned,
}

impl TypedClassicalExpr {
    /// Returns the source storage type when this is a bool/bit value.
    fn bit_type(&self) -> Option<BitType> {
        match self {
            Self::Bool(_) => Some(BitType::Bool),
            Self::Bit(_) => Some(BitType::Bit),
            Self::Register(values) => Some(BitType::Register {
                width: values.len(),
            }),
            Self::Integer { .. } | Self::IntegerLiteral(_) => None,
        }
    }

    /// Consumes a value already checked to be scalar or register bits.
    fn into_bit_cells(self) -> Option<Vec<ClassicalExpr>> {
        match self {
            Self::Bool(value) | Self::Bit(value) => Some(vec![value]),
            Self::Register(values) => Some(values),
            Self::Integer { .. } | Self::IntegerLiteral(_) => None,
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
    /// Lowers the complete source and assembles declarations plus executable body.
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
                let path = include
                    .file()
                    .and_then(|path| path.to_string())
                    .ok_or_else(|| expected!("an include path", &include))?;
                if path == "stdgates.inc" {
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
            // `bit[4] c;` records the register; `bit c = true;` additionally
            // emits an assignment that initializes its storage at this point.
            Stmt::ClassicalDeclarationStatement(declaration) => {
                let (register, initializer) = self.lower_classical_declaration(declaration)?;
                self.classical_registers.push(register);
                if let Some(initializer) = initializer {
                    body.statements.push(initializer);
                }
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

    /// Records `OPENQASM 3.x;`; the completed program later rejects other majors.
    fn lower_version(&mut self, version: ast::VersionString) -> Result<(), FrontendError> {
        let typed_number = version
            .version()
            .map(|number| number.syntax().text().to_string());
        // The current parser may represent the complete header as one
        // VERSION_STRING token instead of exposing the generated Version child.
        let fallback_number = || {
            version
                .syntax()
                .text()
                .to_string()
                .strip_prefix("OPENQASM")
                .and_then(|text| text.strip_suffix(';'))
                .map(str::trim)
                .map(str::to_owned)
        };
        let text = typed_number
            .or_else(fallback_number)
            .ok_or_else(|| expected!("an OpenQASM version number", &version))?;
        let (major, minor) = text.split_once('.').unwrap_or((&text, "0"));
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
    /// return type is `bool`, `bit`, or `bit[n]`, matching the dynamic-program
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
                if ty.bool_token().is_some() {
                    if ty.designator().is_some() {
                        return Err(expected!("a scalar bool return type", &ty));
                    }
                    Ok(BitType::Bool)
                } else if ty.bit_token().is_some() {
                    bit_type(ty.designator(), "a subroutine return width")
                } else {
                    Err(unsupported!(
                        "subroutine return type other than bool or bit",
                        &ty
                    ))
                }
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

    /// Declares `qubit q;` or `qubit[n] q;` and allocates its IR register.
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

    /// Declares a symbolic numeric input such as `input angle theta;`.
    ///
    /// Output declarations and nonnumeric input types are outside the current
    /// frontend subset.
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

    /// Declares `bool`, `bit`, or `bit[n]` and lowers an optional initializer.
    ///
    /// For `bit c = true;`, the register metadata is returned together with
    /// `Some(Assign(c, true))`; `bit c;` has no executable initializer.
    fn lower_classical_declaration(
        &mut self,
        declaration: ast::ClassicalDeclarationStatement,
    ) -> Result<(Register, Option<Statement>), FrontendError> {
        if declaration.const_token().is_some() {
            return Err(unsupported!("const declaration", &declaration));
        }
        let name = declaration_name(&declaration)?;
        let scalar_type = declaration
            .scalar_type()
            .ok_or_else(|| expected!("a classical scalar type", &declaration))?;
        let ty = if scalar_type.bool_token().is_some() {
            if scalar_type.designator().is_some() {
                return Err(expected!("a scalar bool type", &scalar_type));
            }
            BitType::Bool
        } else if scalar_type.bit_token().is_some() {
            bit_type(scalar_type.designator(), "a bit array width")?
        } else {
            return Err(unsupported!(
                "classical type other than bool or bit",
                &scalar_type
            ));
        };
        let binding = self
            .scopes
            .declare(name.clone(), BindingKind::ClassicalBit(ty))
            .map_err(scope_error)?;
        let register = self.ids.node(RegisterData {
            id: binding.id,
            name,
            width: ty.width(),
        });
        let initializer = declaration
            .expr()
            .map(|expression| {
                self.lower_assigned_value(
                    bit_operand(binding.id, ty),
                    expression,
                    declaration.syntax().text().to_string(),
                )
            })
            .transpose()?;
        Ok((register, initializer))
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
                    Expr::BinExpr(binary)
                        if matches!(binary.op_kind(), Some(ast::BinaryOp::Assignment { .. })) =>
                    {
                        self.lower_compound_assignment(binary)
                    }
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
                    let value = BigRational::from_integer(exact_integer_value(number)?);
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

    /// Lowers measurement, classical-expression, and subroutine-result assignments.
    fn lower_assignment(
        &mut self,
        assignment: ast::AssignmentStmt,
    ) -> Result<Statement, FrontendError> {
        let targets = self.lower_assignment_targets(&assignment)?;
        let rhs = assignment
            .rhs()
            .ok_or_else(|| expected!("an assignment value", &assignment))?;
        self.lower_assigned_value(targets, rhs, assignment.syntax().text().to_string())
    }

    fn lower_assigned_value(
        &mut self,
        targets: BitOperand,
        rhs: Expr,
        snippet: String,
    ) -> Result<Statement, FrontendError> {
        match rhs {
            // `c = measure q;` produces a quantum measurement for each
            // matching scalar/register cell rather than a classical Assign.
            Expr::MeasureExpression(measurement) => {
                let operand = measurement
                    .gate_operand()
                    .ok_or_else(|| expected!("a measurement operand", &measurement))?;
                let qubits = self.lower_qubits(operand)?;
                if !measurement_types_match(qubits.ty(), targets.ty()) {
                    return Err(FrontendError::Expected {
                        expected: "matching scalar or register measurement operands",
                        snippet,
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
            // `c = parity(q);` binds the subroutine's classical return value
            // directly to `c` while specializing its quantum parameters.
            Expr::CallExpr(call) => self.lower_subroutine_call(call, Some(targets)),
            // `c = a ^ b;` lowers the RHS as a typed bit value, then checks
            // that its scalar/register shape matches the assignment target.
            expression => {
                let values = self.lower_bit_expr(expression)?;
                self.assign_bit_values(targets, values, snippet)
            }
        }
    }

    /// Expands a shape-compatible classical assignment into scalar IR writes.
    ///
    /// For example, `dst = src ^ "01";` on two-bit registers becomes two
    /// [`StatementKind::Assign`] nodes, one for each register index.
    fn assign_bit_values(
        &mut self,
        targets: BitOperand,
        values: TypedClassicalExpr,
        snippet: String,
    ) -> Result<Statement, FrontendError> {
        if values
            .bit_type()
            .is_none_or(|value_type| !bit_types_compatible(targets.ty(), value_type))
        {
            return Err(FrontendError::Expected {
                expected: "matching scalar or register assignment operands",
                snippet,
            });
        }
        let statements = targets
            .into_cells()
            .into_iter()
            .zip(values.into_bit_cells().expect("checked bit value"))
            .map(|(target, value)| self.ids.node(StatementKind::Assign { target, value }))
            .collect();
        Ok(self.sequence(statements))
    }

    /// Lowers bitwise compound assignment to an ordinary read-modify-write.
    /// For example, `flag ^= measured` becomes `flag = flag ^ measured`.
    fn lower_compound_assignment(
        &mut self,
        assignment: ast::BinExpr,
    ) -> Result<Statement, FrontendError> {
        let operation = match assignment.op_kind() {
            Some(ast::BinaryOp::Assignment {
                op: Some(ast::ArithOp::BitAnd),
            }) => ast::ArithOp::BitAnd,
            Some(ast::BinaryOp::Assignment {
                op: Some(ast::ArithOp::BitOr),
            }) => ast::ArithOp::BitOr,
            Some(ast::BinaryOp::Assignment {
                op: Some(ast::ArithOp::BitXor),
            }) => ast::ArithOp::BitXor,
            _ => return Err(unsupported!("classical compound assignment", &assignment)),
        };
        let target_expression = assignment
            .lhs()
            .ok_or_else(|| expected!("a compound-assignment target", &assignment))?;
        let targets = self.lower_bit_operand(target_expression)?;
        let values = self.lower_bit_expr(
            assignment
                .rhs()
                .ok_or_else(|| expected!("a compound-assignment value", &assignment))?,
        )?;
        if values
            .bit_type()
            .is_none_or(|value_type| !bit_types_compatible(targets.ty(), value_type))
        {
            return Err(expected!(
                "matching scalar or register compound-assignment operands",
                &assignment
            ));
        }
        let statements = targets
            .into_cells()
            .into_iter()
            .zip(values.into_bit_cells().expect("checked bit value"))
            .map(|(target, right)| {
                let left = self.ids.node(ClassicalExprKind::Bit(target.clone()));
                let value = self.bitwise_scalar(operation, left, right);
                self.ids.node(StatementKind::Assign { target, value })
            })
            .collect();
        Ok(self.sequence(statements))
    }

    /// Resolves an assignment destination such as `flag` or `bits[2]`.
    fn lower_assignment_targets(
        &self,
        assignment: &ast::AssignmentStmt,
    ) -> Result<BitOperand, FrontendError> {
        if let Some(indexed) = assignment.indexed_identifier() {
            return Ok(BitOperand::Bit(self.lower_classical_indexed(indexed)?));
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
        // Resolve `prepare(q)` to the previously registered definition.
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
        // Quantum arguments preserve scalar/register shape, so `qubit q` and
        // `qubit[1] q` cannot be interchanged merely because both have width one.
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
        // The same physical qubit cannot occupy two formal parameters because
        // that would alias operands within the specialized body.
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
        // Calls returning classical data must appear with a compatible
        // assignment target; void calls must not have one.
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
            (Some(return_type), Some(targets))
                if !bit_types_compatible(return_type, targets.ty()) =>
            {
                return Err(FrontendError::Expected {
                    expected: "a call target matching the subroutine return type",
                    snippet: call.syntax().text().to_string(),
                });
            }
            _ => {}
        }

        // Bind formal quantum names to caller wires, lower the body, and then
        // restore the surrounding lexical environment.
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

    /// Lowers a called subroutine body in its call-site parameter environment.
    ///
    /// A final `return` writes into `targets`; local classical declarations are
    /// retained in this block. Definitions that are never called never reach
    /// this function.
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
                Stmt::ClassicalDeclarationStatement(declaration) => {
                    let (register, initializer) = self.lower_classical_declaration(declaration)?;
                    lowered.classical_registers.push(register);
                    if let Some(initializer) = initializer {
                        lowered.statements.push(initializer);
                    }
                }
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

    /// Connects a subroutine's classical return value to the caller target.
    ///
    /// `return measure q;` emits measurement statements. A classical
    /// expression such as `return left ^ right;` is evaluated and copied into
    /// the caller target. Quantum state is returned through referenced qubit
    /// parameters, never through an OpenQASM return value.
    fn lower_return(
        &mut self,
        return_expression: ast::ReturnExpr,
        return_type: Option<BitType>,
        targets: Option<&BitOperand>,
        body: &mut Block,
    ) -> Result<(), FrontendError> {
        let value = return_expression.expr();
        match (return_type, value) {
            // `return;` is the only valid return from a void subroutine.
            (None, None) => Ok(()),
            (None, Some(_)) => Err(unsupported!(
                "value returned from void subroutine",
                &return_expression
            )),
            (Some(_), None) => Err(expected!("a subroutine return value", &return_expression)),
            // `return measure q;` writes measurement results directly into
            // the caller's assignment target.
            (Some(return_type), Some(Expr::MeasureExpression(measurement))) => {
                let qubits =
                    self.lower_qubits(measurement.gate_operand().ok_or_else(|| {
                        expected!("a returned measurement operand", &measurement)
                    })?)?;
                if !measurement_types_match(qubits.ty(), return_type)
                    || targets
                        .is_some_and(|targets| !bit_types_compatible(targets.ty(), return_type))
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
            // Evaluate a classical return expression and copy it into the
            // caller-provided target.
            (Some(return_type), Some(value)) => {
                let snippet = return_expression.syntax().text().to_string();
                let values = self.lower_bit_expr(value)?;
                if values
                    .bit_type()
                    .is_none_or(|value_type| !bit_types_compatible(return_type, value_type))
                    || targets
                        .is_some_and(|targets| !bit_types_compatible(targets.ty(), return_type))
                {
                    return Err(expected!(
                        "a return value matching its declared type",
                        &return_expression
                    ));
                }
                if let Some(targets) = targets {
                    body.statements.push(self.assign_bit_values(
                        targets.clone(),
                        values,
                        snippet,
                    )?);
                }
                Ok(())
            }
        }
    }

    /// Lowers an `if` statement and gives each branch its own lexical scope.
    fn lower_if(&mut self, statement: ast::IfStmt) -> Result<Statement, FrontendError> {
        let condition = self.lower_scalar_bit_expression(
            statement
                .condition()
                .ok_or_else(|| expected!("an if condition", &statement))?,
        )?;
        let then_branch = self.lower_branch(statement.true_body_block_or_stmt())?;
        let else_branch = match statement.false_body_block_or_stmt() {
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

    /// Lowers a braced block inside a fresh lexical scope.
    fn lower_block(&mut self, block: ast::BlockExpr) -> Result<Block, FrontendError> {
        self.scopes.enter(ScopeKind::Block);
        let result = self.lower_block_contents(block);
        self.scopes.exit();
        result
    }

    /// Lowers declarations and statements after the caller has entered a scope.
    fn lower_block_contents(&mut self, block: ast::BlockExpr) -> Result<Block, FrontendError> {
        let mut lowered = self.ids.node(BlockData::default());
        for statement in block.statements() {
            match statement {
                // `bit local;` belongs to this block and is removed on scope exit.
                Stmt::ClassicalDeclarationStatement(declaration) => {
                    let (register, initializer) = self.lower_classical_declaration(declaration)?;
                    lowered.classical_registers.push(register);
                    if let Some(initializer) = initializer {
                        lowered.statements.push(initializer);
                    }
                }
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

    /// Lowers a scalar Boolean expression used by control flow.
    fn lower_scalar_bit_expression(
        &mut self,
        expression: Expr,
    ) -> Result<ClassicalExpr, FrontendError> {
        let snippet = expression.syntax().text().to_string();
        let expression = match self.lower_bit_expr(expression)? {
            TypedClassicalExpr::Bool(expression) | TypedClassicalExpr::Bit(expression) => {
                expression
            }
            _ => {
                return Err(FrontendError::Expected {
                    expected: "a scalar Boolean or bit expression",
                    snippet,
                });
            }
        };
        Ok(expression)
    }

    /// Lowers a value used in a bool/bit context, including the literals 0 and 1.
    fn lower_bit_expr(&mut self, expression: Expr) -> Result<TypedClassicalExpr, FrontendError> {
        let snippet = expression.syntax().text().to_string();
        let value = self.lower_typed_classical_expr(expression)?;
        self.coerce_bit_expr(value, snippet)
    }

    /// Retains the expression's source type before operator dispatch.
    fn lower_typed_classical_expr(
        &mut self,
        expression: Expr,
    ) -> Result<TypedClassicalExpr, FrontendError> {
        match expression {
            // An unindexed name preserves its declared type and shape:
            // `bool ready` and `bit flag` are scalar; `bit[n] bits` is a register.
            Expr::Identifier(identifier) => {
                let name = identifier.string();
                let operand = self.classical_cells(name)?;
                Ok(self.bit_operand_expr(operand))
            }
            // `bits[2]` selects one checked cell and is therefore scalar `bit`.
            Expr::IndexedIdentifier(indexed) => {
                let bit = self.lower_classical_indexed(indexed)?;
                Ok(TypedClassicalExpr::Bit(
                    self.ids.node(ClassicalExprKind::Bit(bit)),
                ))
            }
            Expr::Literal(literal) => match literal.kind() {
                // `true` and `false` are scalar Boolean values.
                ast::LiteralKind::Bool(value) => Ok(TypedClassicalExpr::Bool(
                    self.ids.node(ClassicalExprKind::Bool(value)),
                )),
                // Integer literals retain arbitrary precision until a bit or
                // integer operation supplies the required type and width.
                ast::LiteralKind::IntNumber(number) => Ok(TypedClassicalExpr::IntegerLiteral(
                    exact_integer_value(number)?,
                )),
                // A bit string such as `"101"` is a width-three register
                // value. Reverse source order gives the IR its bit-zero-first
                // convention: `[true, false, true]`.
                ast::LiteralKind::BitString(value) => {
                    let bits = value
                        .str()
                        .ok_or_else(|| expected!("a bit-string literal", &literal))?
                        .chars()
                        .filter(|character| *character != '_')
                        .rev()
                        .map(|bit| {
                            self.ids.node(ClassicalExprKind::Bool(match bit {
                                '0' => false,
                                '1' => true,
                                _ => unreachable!(),
                            }))
                        })
                        .collect();
                    Ok(TypedClassicalExpr::Register(bits))
                }
                _ => Err(unsupported!("classical bit literal", &literal)),
            },
            // Parentheses affect parsing precedence but do not add an IR node:
            // `(a ^ b)` has the same lowered form as `a ^ b`.
            Expr::ParenExpr(paren) => self.lower_typed_classical_expr(
                paren
                    .expr()
                    .ok_or_else(|| expected!("a parenthesized expression", &paren))?,
            ),
            // Casts produce typed expressions before any surrounding comparison.
            // Thus both sides of `int[3](a) == int[3](b)` lower uniformly.
            Expr::CastExpression(cast) => self.lower_classical_cast(cast),
            Expr::PrefixExpr(prefix) => {
                let operand = prefix
                    .expr()
                    .ok_or_else(|| expected!("a prefix operand", &prefix))?;
                match prefix.op_kind() {
                    // Logical `!flag` requires one scalar truth value.
                    Some(ast::UnaryOp::LogicNot) => {
                        let operand = match self.lower_bit_expr(operand)? {
                            TypedClassicalExpr::Bool(operand)
                            | TypedClassicalExpr::Bit(operand) => operand,
                            _ => return Err(expected!("a scalar logical-not operand", &prefix)),
                        };
                        Ok(TypedClassicalExpr::Bool(
                            self.ids.node(ClassicalExprKind::Not(Box::new(operand))),
                        ))
                    }
                    // Bitwise `~value` applies Not to one scalar or to every
                    // cell of a register, e.g. `~"001"` becomes `"110"`.
                    Some(ast::UnaryOp::Not) => {
                        let operand = self.lower_typed_classical_expr(operand)?;
                        self.negate_classical_expr(operand, &prefix)
                    }
                    // A leading minus is retained on an integer literal so a
                    // later typed comparison can encode it in two's complement.
                    Some(ast::UnaryOp::Neg) => match self.lower_typed_classical_expr(operand)? {
                        TypedClassicalExpr::IntegerLiteral(value) => {
                            Ok(TypedClassicalExpr::IntegerLiteral(-value))
                        }
                        _ => Err(unsupported!("non-literal integer negation", &prefix)),
                    },
                    _ => Err(unsupported!("classical prefix operator", &prefix)),
                }
            }
            Expr::BinExpr(binary) => {
                let left_source = binary
                    .lhs()
                    .ok_or_else(|| expected!("a left operand", &binary))?;
                let right_source = binary
                    .rhs()
                    .ok_or_else(|| expected!("a right operand", &binary))?;
                let left = self.lower_typed_classical_expr(left_source)?;
                let right = self.lower_typed_classical_expr(right_source)?;
                match binary.op_kind() {
                    // Equality dispatches after both operand types are known.
                    Some(ast::BinaryOp::CmpOp(ast::CmpOp::Eq { negated })) => {
                        let equality = self.lower_classical_equality(left, right, &binary)?;
                        if negated {
                            Ok(TypedClassicalExpr::Bool(
                                self.ids.node(ClassicalExprKind::Not(Box::new(equality))),
                            ))
                        } else {
                            Ok(TypedClassicalExpr::Bool(equality))
                        }
                    }
                    // Ordering uses unsigned order for bits and the retained
                    // signedness for integer casts.
                    Some(ast::BinaryOp::CmpOp(ast::CmpOp::Ord { ordering, strict })) => {
                        Ok(TypedClassicalExpr::Bool(self.lower_classical_order(
                            left, right, ordering, strict, &binary,
                        )?))
                    }
                    // Logical `a && b` accepts scalar truth values only.
                    Some(ast::BinaryOp::LogicOp(ast::LogicOp::And)) => {
                        let (left, right) = self.scalar_operands(left, right, &binary)?;
                        Ok(TypedClassicalExpr::Bool(self.ids.node(
                            ClassicalExprKind::And(Box::new(left), Box::new(right)),
                        )))
                    }
                    // Logical `a || b` likewise rejects register operands.
                    Some(ast::BinaryOp::LogicOp(ast::LogicOp::Or)) => {
                        let (left, right) = self.scalar_operands(left, right, &binary)?;
                        Ok(TypedClassicalExpr::Bool(self.ids.node(
                            ClassicalExprKind::Or(Box::new(left), Box::new(right)),
                        )))
                    }
                    // Bitwise operations preserve the common typed shape.
                    Some(ast::BinaryOp::ArithOp(
                        operation @ (ast::ArithOp::BitAnd
                        | ast::ArithOp::BitOr
                        | ast::ArithOp::BitXor),
                    )) => self.lower_bitwise_expr(operation, left, right, &binary),
                    _ => Err(unsupported!("classical binary operator", &binary)),
                }
            }
            // Arithmetic, shifts, concatenation, and other classical value
            // forms require IR semantics beyond the current Boolean subset.
            _ => Err(unsupported!("classical bit expression", &expression)),
        }
    }

    /// Turns storage cells into read expressions without changing their shape.
    ///
    /// For example, reading `bit[2] c` produces `[Bit(c[0]), Bit(c[1])]`.
    fn bit_operand_expr(&mut self, operand: BitOperand) -> TypedClassicalExpr {
        match operand {
            BitOperand::Bool(bit) => {
                TypedClassicalExpr::Bool(self.ids.node(ClassicalExprKind::Bit(bit)))
            }
            BitOperand::Bit(bit) => {
                TypedClassicalExpr::Bit(self.ids.node(ClassicalExprKind::Bit(bit)))
            }
            BitOperand::Register(bits) => TypedClassicalExpr::Register(
                bits.into_iter()
                    .map(|bit| self.ids.node(ClassicalExprKind::Bit(bit)))
                    .collect(),
            ),
        }
    }

    /// Lowers a bool, bit, int, or uint cast to one typed expression.
    ///
    /// For example, `bool(bit[3](bits))` is true exactly when at least one
    /// source bit is one; `int[3](bits)` retains the same cells as signed data.
    fn lower_classical_cast(
        &mut self,
        cast: ast::CastExpression,
    ) -> Result<TypedClassicalExpr, FrontendError> {
        let ty = cast
            .scalar_type()
            .ok_or_else(|| expected!("a classical cast type", &cast))?;
        let operand = cast
            .expr()
            .ok_or_else(|| expected!("a classical cast operand", &cast))?;

        if ty.int_token().is_some() || ty.uint_token().is_some() {
            let signedness = if ty.int_token().is_some() {
                Signedness::Signed
            } else {
                Signedness::Unsigned
            };
            let width = ty
                .designator()
                .ok_or_else(|| expected!("an explicitly sized integer cast", &cast))?
                .expr()
                .ok_or_else(|| expected!("an integer cast width", &cast))
                .and_then(literal_usize)?;
            if width == 0 {
                return Err(expected!("a non-empty integer cast", &cast));
            }
            let value = self.lower_typed_classical_expr(operand)?;
            let bits = match value {
                TypedClassicalExpr::Register(bits) | TypedClassicalExpr::Integer { bits, .. }
                    if bits.len() == width =>
                {
                    bits
                }
                _ => return Err(expected!("an integer cast matching its bit width", &cast)),
            };
            return Ok(TypedClassicalExpr::Integer { bits, signedness });
        }

        if ty.bool_token().is_some() {
            if ty.designator().is_some() {
                return Err(expected!("a scalar bool cast type", &cast));
            }
            let value = self.lower_typed_classical_expr(operand)?;
            return Ok(TypedClassicalExpr::Bool(self.truth_expr(value)));
        }

        if ty.bit_token().is_some() {
            let value = self.lower_typed_classical_expr(operand)?;
            if let Some(designator) = ty.designator() {
                let width = designator
                    .expr()
                    .ok_or_else(|| expected!("a bit cast width", &designator))
                    .and_then(literal_usize)?;
                let bits = match value {
                    TypedClassicalExpr::Register(bits)
                    | TypedClassicalExpr::Integer { bits, .. }
                        if bits.len() == width =>
                    {
                        bits
                    }
                    TypedClassicalExpr::Bool(value) | TypedClassicalExpr::Bit(value)
                        if width == 1 =>
                    {
                        vec![value]
                    }
                    _ => return Err(expected!("a bit cast matching its width", &cast)),
                };
                return Ok(TypedClassicalExpr::Register(bits));
            };
            let value = self.coerce_bit_expr(value, cast.syntax().text().to_string())?;
            return match value {
                TypedClassicalExpr::Bool(value) | TypedClassicalExpr::Bit(value) => {
                    Ok(TypedClassicalExpr::Bit(value))
                }
                _ => Err(expected!("a scalar bool or bit cast operand", &cast)),
            };
        }

        Err(unsupported!("classical cast type", &ty))
    }

    /// Accepts a bool/bit value and converts the untyped literals `0` and `1`
    /// to scalar bits. Other integer literals still need an explicit cast.
    fn coerce_bit_expr(
        &mut self,
        value: TypedClassicalExpr,
        snippet: String,
    ) -> Result<TypedClassicalExpr, FrontendError> {
        match value {
            TypedClassicalExpr::Bool(_)
            | TypedClassicalExpr::Bit(_)
            | TypedClassicalExpr::Register(_) => Ok(value),
            TypedClassicalExpr::IntegerLiteral(value)
                if value == BigInt::from(0_u8) || value == BigInt::from(1_u8) =>
            {
                Ok(TypedClassicalExpr::Bit(self.ids.node(
                    ClassicalExprKind::Bool(value == BigInt::from(1_u8)),
                )))
            }
            TypedClassicalExpr::IntegerLiteral(_) => Err(FrontendError::Expected {
                expected: "the scalar bit literal 0 or 1",
                snippet,
            }),
            TypedClassicalExpr::Integer { .. } => Err(FrontendError::Expected {
                expected: "a bit value",
                snippet,
            }),
        }
    }

    /// Extracts two scalar operands for `&&` and `||`.
    fn scalar_operands(
        &mut self,
        left: TypedClassicalExpr,
        right: TypedClassicalExpr,
        source: &ast::BinExpr,
    ) -> Result<(ClassicalExpr, ClassicalExpr), FrontendError> {
        let snippet = source.syntax().text().to_string();
        match (
            self.coerce_bit_expr(left, snippet.clone())?,
            self.coerce_bit_expr(right, snippet)?,
        ) {
            (
                TypedClassicalExpr::Bool(left) | TypedClassicalExpr::Bit(left),
                TypedClassicalExpr::Bool(right) | TypedClassicalExpr::Bit(right),
            ) => Ok((left, right)),
            _ => Err(expected!("scalar logical operands", source)),
        }
    }

    /// Converts a scalar bool/bit, bit register, or integer to one Boolean.
    ///
    /// A multi-bit value follows `value != 0`: `bool(bits)` becomes the OR of
    /// all cells, while a scalar `bool` or `bit` is already a truth value.
    fn truth_expr(&mut self, value: TypedClassicalExpr) -> ClassicalExpr {
        match value {
            TypedClassicalExpr::Bool(value) | TypedClassicalExpr::Bit(value) => value,
            TypedClassicalExpr::Register(bits) | TypedClassicalExpr::Integer { bits, .. } => {
                let mut bits = bits.into_iter();
                let Some(mut value) = bits.next() else {
                    return self.ids.node(ClassicalExprKind::Bool(false));
                };
                for bit in bits {
                    value = self
                        .ids
                        .node(ClassicalExprKind::Or(Box::new(value), Box::new(bit)));
                }
                value
            }
            TypedClassicalExpr::IntegerLiteral(value) => self
                .ids
                .node(ClassicalExprKind::Bool(value != BigInt::from(0_u8))),
        }
    }

    /// Applies bitwise complement while preserving bit shape or integer type.
    fn negate_classical_expr<T: AstNode>(
        &mut self,
        value: TypedClassicalExpr,
        source: &T,
    ) -> Result<TypedClassicalExpr, FrontendError> {
        let negate =
            |this: &mut Self, value| this.ids.node(ClassicalExprKind::Not(Box::new(value)));
        match value {
            TypedClassicalExpr::Bool(value) | TypedClassicalExpr::Bit(value) => {
                Ok(TypedClassicalExpr::Bit(negate(self, value)))
            }
            TypedClassicalExpr::Register(values) => Ok(TypedClassicalExpr::Register(
                values
                    .into_iter()
                    .map(|value| negate(self, value))
                    .collect(),
            )),
            TypedClassicalExpr::Integer { bits, signedness } => Ok(TypedClassicalExpr::Integer {
                bits: bits.into_iter().map(|value| negate(self, value)).collect(),
                signedness,
            }),
            TypedClassicalExpr::IntegerLiteral(_) => {
                Err(expected!("a width-bearing bitwise-not operand", source))
            }
        }
    }

    /// Lowers shape-compatible `&`, `|`, or `^` after resolving operand types.
    ///
    /// `a ^ b` on `bit[2]` values becomes the pair `a[0] ^ b[0]` and
    /// `a[1] ^ b[1]`; scalar/register mixing is rejected.
    fn lower_bitwise_expr(
        &mut self,
        operation: ast::ArithOp,
        left: TypedClassicalExpr,
        right: TypedClassicalExpr,
        source: &ast::BinExpr,
    ) -> Result<TypedClassicalExpr, FrontendError> {
        if matches!(&left, TypedClassicalExpr::Integer { .. })
            || matches!(&right, TypedClassicalExpr::Integer { .. })
        {
            return match (left, right) {
                (
                    TypedClassicalExpr::Integer {
                        bits: left,
                        signedness: left_signedness,
                    },
                    TypedClassicalExpr::Integer {
                        bits: right,
                        signedness: right_signedness,
                    },
                ) if left_signedness == right_signedness && left.len() == right.len() => {
                    Ok(TypedClassicalExpr::Integer {
                        bits: left
                            .into_iter()
                            .zip(right)
                            .map(|(left, right)| self.bitwise_scalar(operation, left, right))
                            .collect(),
                        signedness: left_signedness,
                    })
                }
                _ => Err(expected!(
                    "integer bitwise operands with matching type and width",
                    source
                )),
            };
        }

        let snippet = source.syntax().text().to_string();
        let left = self.coerce_bit_expr(left, snippet.clone())?;
        let right = self.coerce_bit_expr(right, snippet)?;
        match (left, right) {
            (
                TypedClassicalExpr::Bool(left) | TypedClassicalExpr::Bit(left),
                TypedClassicalExpr::Bool(right) | TypedClassicalExpr::Bit(right),
            ) => Ok(TypedClassicalExpr::Bit(
                self.bitwise_scalar(operation, left, right),
            )),
            (TypedClassicalExpr::Register(left), TypedClassicalExpr::Register(right))
                if left.len() == right.len() =>
            {
                Ok(TypedClassicalExpr::Register(
                    left.into_iter()
                        .zip(right)
                        .map(|(left, right)| self.bitwise_scalar(operation, left, right))
                        .collect(),
                ))
            }
            _ => Err(expected!(
                "matching scalar or register bitwise operands",
                source
            )),
        }
    }

    /// Constructs one scalar Boolean node for a bitwise operator.
    fn bitwise_scalar(
        &mut self,
        operation: ast::ArithOp,
        left: ClassicalExpr,
        right: ClassicalExpr,
    ) -> ClassicalExpr {
        let left = Box::new(left);
        let right = Box::new(right);
        match operation {
            ast::ArithOp::BitAnd => self.ids.node(ClassicalExprKind::And(left, right)),
            ast::ArithOp::BitOr => self.ids.node(ClassicalExprKind::Or(left, right)),
            ast::ArithOp::BitXor => self.ids.node(ClassicalExprKind::Xor(left, right)),
            _ => unreachable!(),
        }
    }

    /// Compares two typed expressions after resolving literal width and signedness.
    fn lower_classical_equality(
        &mut self,
        left: TypedClassicalExpr,
        right: TypedClassicalExpr,
        source: &ast::BinExpr,
    ) -> Result<ClassicalExpr, FrontendError> {
        if let (
            TypedClassicalExpr::IntegerLiteral(left),
            TypedClassicalExpr::IntegerLiteral(right),
        ) = (&left, &right)
        {
            return Ok(self.ids.node(ClassicalExprKind::Bool(left == right)));
        }
        let integer_comparison = matches!(&left, TypedClassicalExpr::Integer { .. })
            || matches!(&right, TypedClassicalExpr::Integer { .. });
        let (left, right) = if integer_comparison {
            let (left, right, _) = self.integer_operands(left, right, source)?;
            (left, right)
        } else {
            self.bit_operands(
                left,
                right,
                source,
                "matching scalar or register equality operands",
            )?
        };
        Ok(self.equal_cells(left, right))
    }

    /// Conjoins equality of two equally sized little-endian cell vectors.
    fn equal_cells(
        &mut self,
        left: Vec<ClassicalExpr>,
        right: Vec<ClassicalExpr>,
    ) -> ClassicalExpr {
        let mut equalities = Vec::with_capacity(left.len());
        for (left, right) in left.into_iter().zip(right) {
            equalities.push(
                self.ids
                    .node(ClassicalExprKind::Eq(Box::new(left), Box::new(right))),
            );
        }
        let mut equalities = equalities.into_iter();
        let Some(mut equality) = equalities.next() else {
            return self.ids.node(ClassicalExprKind::Bool(true));
        };
        for next in equalities {
            equality = self
                .ids
                .node(ClassicalExprKind::And(Box::new(equality), Box::new(next)));
        }
        equality
    }

    /// Orders bit values as unsigned and integer casts according to signedness.
    ///
    /// Bits are visited from low to high. A newly visited bit therefore takes
    /// precedence when it differs; only equal bits preserve the comparison of
    /// the lower suffix. For `<`, the recurrence is
    /// `less = (!left & right) | ((left == right) & less)`.
    fn lower_classical_order(
        &mut self,
        left: TypedClassicalExpr,
        right: TypedClassicalExpr,
        ordering: ast::Ordering,
        strict: bool,
        source: &ast::BinExpr,
    ) -> Result<ClassicalExpr, FrontendError> {
        if let (
            TypedClassicalExpr::IntegerLiteral(left),
            TypedClassicalExpr::IntegerLiteral(right),
        ) = (&left, &right)
        {
            let result = match (ordering, strict) {
                (ast::Ordering::Less, true) => left < right,
                (ast::Ordering::Less, false) => left <= right,
                (ast::Ordering::Greater, true) => left > right,
                (ast::Ordering::Greater, false) => left >= right,
            };
            return Ok(self.ids.node(ClassicalExprKind::Bool(result)));
        }
        let integer_comparison = matches!(&left, TypedClassicalExpr::Integer { .. })
            || matches!(&right, TypedClassicalExpr::Integer { .. });
        let (mut left, mut right, signedness) = if integer_comparison {
            self.integer_operands(left, right, source)?
        } else {
            let (left, right) = self.bit_operands(
                left,
                right,
                source,
                "matching scalar or register comparison operands",
            )?;
            (left, right, Signedness::Unsigned)
        };

        // Flipping the sign bit maps two's-complement order to unsigned order.
        if signedness == Signedness::Signed {
            let left_sign = left.pop().expect("integer width is nonzero");
            let right_sign = right.pop().expect("integer width is nonzero");
            left.push(self.ids.node(ClassicalExprKind::Not(Box::new(left_sign))));
            right.push(self.ids.node(ClassicalExprKind::Not(Box::new(right_sign))));
        }
        Ok(self.order_cells(left, right, ordering, strict))
    }

    /// Applies unsigned lexicographic order to little-endian Boolean cells.
    fn order_cells(
        &mut self,
        left: Vec<ClassicalExpr>,
        right: Vec<ClassicalExpr>,
        ordering: ast::Ordering,
        strict: bool,
    ) -> ClassicalExpr {
        let ordering = if strict {
            ordering
        } else {
            match ordering {
                ast::Ordering::Less => ast::Ordering::Greater,
                ast::Ordering::Greater => ast::Ordering::Less,
            }
        };
        let mut ordered = self.ids.node(ClassicalExprKind::Bool(false));
        for (left, right) in left.into_iter().zip(right) {
            let equal_left = self.clone_classical_expr(&left);
            let equal_right = self.clone_classical_expr(&right);
            let preferred = match ordering {
                ast::Ordering::Less => {
                    let left = self.ids.node(ClassicalExprKind::Not(Box::new(left)));
                    self.ids
                        .node(ClassicalExprKind::And(Box::new(left), Box::new(right)))
                }
                ast::Ordering::Greater => {
                    let right = self.ids.node(ClassicalExprKind::Not(Box::new(right)));
                    self.ids
                        .node(ClassicalExprKind::And(Box::new(left), Box::new(right)))
                }
            };
            let bit_equal = self.ids.node(ClassicalExprKind::Eq(
                Box::new(equal_left),
                Box::new(equal_right),
            ));
            let lower_ordered = self.ids.node(ClassicalExprKind::And(
                Box::new(bit_equal),
                Box::new(ordered),
            ));
            ordered = self.ids.node(ClassicalExprKind::Or(
                Box::new(preferred),
                Box::new(lower_ordered),
            ));
        }
        if strict {
            ordered
        } else {
            self.ids.node(ClassicalExprKind::Not(Box::new(ordered)))
        }
    }

    /// Aligns two scalar/register bit values and checks their source shape.
    fn bit_operands(
        &mut self,
        left: TypedClassicalExpr,
        right: TypedClassicalExpr,
        source: &ast::BinExpr,
        expected: &'static str,
    ) -> Result<(Vec<ClassicalExpr>, Vec<ClassicalExpr>), FrontendError> {
        let snippet = source.syntax().text().to_string();
        let left = self.coerce_bit_expr(left, snippet.clone())?;
        let right = self.coerce_bit_expr(right, snippet)?;
        match (left, right) {
            (
                TypedClassicalExpr::Bool(left) | TypedClassicalExpr::Bit(left),
                TypedClassicalExpr::Bool(right) | TypedClassicalExpr::Bit(right),
            ) => Ok((vec![left], vec![right])),
            (TypedClassicalExpr::Register(left), TypedClassicalExpr::Register(right))
                if left.len() == right.len() =>
            {
                Ok((left, right))
            }
            _ => Err(expected!(expected, source)),
        }
    }

    /// Aligns typed integers, encoding one literal at the other operand's type.
    fn integer_operands(
        &mut self,
        left: TypedClassicalExpr,
        right: TypedClassicalExpr,
        source: &ast::BinExpr,
    ) -> Result<(Vec<ClassicalExpr>, Vec<ClassicalExpr>, Signedness), FrontendError> {
        match (left, right) {
            (
                TypedClassicalExpr::Integer {
                    bits: left,
                    signedness: left_signedness,
                },
                TypedClassicalExpr::Integer {
                    bits: right,
                    signedness: right_signedness,
                },
            ) if left_signedness == right_signedness && left.len() == right.len() => {
                Ok((left, right, left_signedness))
            }
            (
                TypedClassicalExpr::Integer { bits, signedness },
                TypedClassicalExpr::IntegerLiteral(value),
            ) => {
                let literal = self.integer_literal_bits(value, bits.len(), signedness, source)?;
                Ok((bits, literal, signedness))
            }
            (
                TypedClassicalExpr::IntegerLiteral(value),
                TypedClassicalExpr::Integer { bits, signedness },
            ) => {
                let literal = self.integer_literal_bits(value, bits.len(), signedness, source)?;
                Ok((literal, bits, signedness))
            }
            _ => Err(expected!(
                "integer operands with matching signedness and width",
                source
            )),
        }
    }

    /// Encodes an exact literal using the target integer's little-endian bits.
    ///
    /// For example, `-2` at type `int[3]` becomes `[0, 1, 1]`, with the least
    /// significant bit first.
    fn integer_literal_bits(
        &mut self,
        value: BigInt,
        width: usize,
        signedness: Signedness,
        source: &ast::BinExpr,
    ) -> Result<Vec<ClassicalExpr>, FrontendError> {
        let modulus = BigInt::from(1_u8) << width;
        let bit_pattern = if signedness == Signedness::Signed {
            let magnitude = BigInt::from(1_u8) << (width - 1);
            if value < -&magnitude || value >= magnitude {
                return Err(FrontendError::Expected {
                    expected: "a signed integer literal representable at the cast width",
                    snippet: source.syntax().text().to_string(),
                });
            }
            if value < BigInt::from(0_u8) {
                modulus + value
            } else {
                value
            }
        } else {
            if value < BigInt::from(0_u8) || value >= modulus {
                return Err(FrontendError::Expected {
                    expected: "an unsigned integer literal representable at the cast width",
                    snippet: source.syntax().text().to_string(),
                });
            }
            value
        };
        Ok((0..width)
            .map(|index| {
                let value = ((&bit_pattern >> index) & BigInt::from(1_u8)) == BigInt::from(1_u8);
                self.ids.node(ClassicalExprKind::Bool(value))
            })
            .collect())
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

    /// Resolves a subroutine argument such as `q` or `q[2]` to caller wires.
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

    /// Expands a quantum binding into the concrete wires visible at this call site.
    ///
    /// Global variables use their own symbol ID. A formal parameter instead
    /// resolves through `quantum_arguments` to the caller-owned operand.
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

    /// Resolves and bounds-checks one indexed classical operand such as `c[1]`.
    fn lower_classical_indexed(
        &self,
        indexed: ast::IndexedIdentifier,
    ) -> Result<ClassicalBit, FrontendError> {
        let (name, index) = indexed_name_and_index(indexed)?;
        self.checked_classical_bit(name, index)
    }

    /// Resolves `name[index]`, rejecting scalar bindings and out-of-range indices.
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

    /// Resolves a cell of a declared `bit[n]` register.
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

    /// Resolves an unindexed classical name while preserving its type and shape.
    fn classical_cells(&self, name: String) -> Result<BitOperand, FrontendError> {
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        match binding.kind {
            BindingKind::ClassicalBit(BitType::Bool) => Ok(BitOperand::Bool(ClassicalBit {
                register: binding.id,
                index: 0,
            })),
            BindingKind::ClassicalBit(BitType::Bit) => Ok(BitOperand::Bit(ClassicalBit {
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

    /// Lowers a classical storage operand, not a computed expression.
    ///
    /// Thus `c` and `c[0]` are accepted, while `c ^ d` is handled by
    /// [`Lowerer::lower_typed_classical_expr`] instead.
    fn lower_bit_operand(&self, expression: Expr) -> Result<BitOperand, FrontendError> {
        match expression {
            Expr::Identifier(identifier) => self.classical_cells(identifier.string()),
            Expr::IndexedIdentifier(indexed) => {
                Ok(BitOperand::Bit(self.lower_classical_indexed(indexed)?))
            }
            expression => Err(unsupported!("classical bit operand", &expression)),
        }
    }

    /// Represents zero or many scalarized operations through one statement API.
    ///
    /// A scalar operation is returned directly. Register-wide lowering such as
    /// `dst = src` produces one assignment per cell and groups them in
    /// [`StatementKind::Scope`]; that wrapper need not introduce declarations.
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

    /// Copies an expression while allocating fresh AST IDs for every new node.
    ///
    /// Ordinary `Clone` would duplicate IDs; this form is used when register
    /// broadcasting emits the same gate parameter into multiple IR statements.
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

    /// Copies a classical expression with fresh AST IDs for the copied tree.
    fn clone_classical_expr(&mut self, expression: &ClassicalExpr) -> ClassicalExpr {
        let kind = match &expression.kind {
            ClassicalExprKind::Bool(value) => ClassicalExprKind::Bool(*value),
            ClassicalExprKind::Bit(bit) => ClassicalExprKind::Bit(bit.clone()),
            ClassicalExprKind::Not(inner) => {
                ClassicalExprKind::Not(Box::new(self.clone_classical_expr(inner)))
            }
            ClassicalExprKind::Eq(left, right) => ClassicalExprKind::Eq(
                Box::new(self.clone_classical_expr(left)),
                Box::new(self.clone_classical_expr(right)),
            ),
            ClassicalExprKind::And(left, right) => ClassicalExprKind::And(
                Box::new(self.clone_classical_expr(left)),
                Box::new(self.clone_classical_expr(right)),
            ),
            ClassicalExprKind::Or(left, right) => ClassicalExprKind::Or(
                Box::new(self.clone_classical_expr(left)),
                Box::new(self.clone_classical_expr(right)),
            ),
            ClassicalExprKind::Xor(left, right) => ClassicalExprKind::Xor(
                Box::new(self.clone_classical_expr(left)),
                Box::new(self.clone_classical_expr(right)),
            ),
        };
        self.ids.node(kind)
    }
}

/// Constructs every addressable cell belonging to a declared classical symbol.
fn bit_operand(register: SymbolId, ty: BitType) -> BitOperand {
    match ty {
        BitType::Bool => BitOperand::Bool(ClassicalBit { register, index: 0 }),
        BitType::Bit => BitOperand::Bit(ClassicalBit { register, index: 0 }),
        BitType::Register { width } => BitOperand::Register(
            (0..width)
                .map(|index| ClassicalBit { register, index })
                .collect(),
        ),
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

/// Parses an unsuffixed integer token exactly in its declared radix.
///
/// For example, `0b1010`, `0xa`, and `10` all produce the same arbitrary-size
/// integer without first passing through a machine-width value.
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

/// Preserves the distinction between `qubit` and `qubit[n]`.
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

/// Preserves the distinction between scalar `bit` and register `bit[n]`.
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
        None => Ok(BitType::Bit),
    }
}

/// Checks the scalar/register shape required by `target = measure source`.
///
/// `qubit q` may be measured into scalar `bool` or `bit`; `qubit[n] q`
/// requires an exactly matching `bit[n]`, including when `n` is one.
fn measurement_types_match(quantum: QuantumType, classical: BitType) -> bool {
    match (quantum, classical) {
        (QuantumType::Scalar, BitType::Bool | BitType::Bit) => true,
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

/// OpenQASM keeps `bool` and scalar `bit` as distinct storage types, but permits
/// either in an r-value context expecting the other. Registers retain exact shape.
fn bit_types_compatible(left: BitType, right: BitType) -> bool {
    left == right
        || matches!(
            (left, right),
            (BitType::Bool, BitType::Bit) | (BitType::Bit, BitType::Bool)
        )
}

/// Extracts the quantum type from a resolved binding or reports a kind error.
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

/// Checks one compile-time register index against its declared width.
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

/// Translates scope-layer errors into the frontend's public diagnostic type.
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
