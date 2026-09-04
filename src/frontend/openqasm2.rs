//! OpenQASM 2.0 parsing and lowering into Irene's shared core IR.
//!
//! The syntax dependency accepts parts of both OpenQASM 2 and 3.  This module
//! therefore treats its AST as an untrusted parse tree and performs the
//! version-specific name, type, shape, arity, and bounds checks itself.

use std::collections::BTreeSet;
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::str::FromStr;

use bigdecimal::{BigDecimal, num_bigint::BigInt};
use num_rational::BigRational;
use oq3_syntax::ast::{self, Expr, GateOperand, HasArgList, HasTextNode, IndexKind, Stmt};
use oq3_syntax::{AstNode as _, SyntaxKind};
use thiserror::Error;

use crate::ir::{
    AstIdGenerator, BlockData, ClassicalBit, ClassicalExpr, ClassicalExprKind, Gate, NumericExpr,
    NumericExprKind, OpenQasmVersion, Program, ProgramData, Qubit, RegisterData, Statement,
    StatementKind,
};

use super::scope::{BindingKind, BitType, QuantumType, ScopeError, ScopeStack};

const MAX_REGISTER_WIDTH: usize = 1_000_000;
const MAX_SOURCE_BYTES: usize = 64 * 1024 * 1024;
const MAX_STATEMENT_BYTES: usize = 2_048;
const MAX_DELIMITER_DEPTH: usize = 128;
const MAX_DECIMAL_EXPONENT: u32 = 100_000;

#[derive(Debug, Error)]
pub enum FrontendError {
    #[error("OpenQASM parse failed: {0}")]
    Parse(String),
    #[error("unsupported OpenQASM 2 construct: {construct}: {snippet}")]
    Unsupported {
        construct: &'static str,
        snippet: String,
    },
    #[error("identifier `{0}` is already declared in this scope")]
    DuplicateIdentifier(String),
    #[error("identifier `{0}` cannot shadow a gate")]
    CannotShadow(String),
    #[error("invalid OpenQASM 2 identifier `{0}`")]
    InvalidIdentifier(String),
    #[error("unknown identifier `{0}`")]
    UnknownIdentifier(String),
    #[error("identifier `{name}` is a {actual}, not a {expected}")]
    WrongIdentifierKind {
        name: String,
        expected: &'static str,
        actual: &'static str,
    },
    #[error("index {index} is outside register `{name}` of width {width}")]
    IndexOutOfBounds {
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

/// Parses one self-contained OpenQASM 2.0 source and lowers it to shared IR.
///
/// `qelib1.inc` is an intrinsic library.  No include path is read, which keeps
/// this entry point deterministic and prevents parser-side include recursion.
pub fn parse_str(source: &str, _source_name: &str) -> Result<Program, FrontendError> {
    preflight_source(source)?;
    catch_unwind(AssertUnwindSafe(|| parse_str_inner(source))).unwrap_or_else(|_| {
        Err(FrontendError::Parse(
            "the syntax parser failed while handling malformed source".to_owned(),
        ))
    })
}

/// Rejects inputs that are outside OpenQASM 2's lexical surface or large
/// enough to overflow the recursive third-party parser before invoking it.
fn preflight_source(source: &str) -> Result<(), FrontendError> {
    if source.len() > MAX_SOURCE_BYTES {
        return Err(source_limit_error("source size", source));
    }

    #[derive(Clone, Copy)]
    enum State {
        Normal,
        LineComment,
        String { escaped: bool },
    }

    let bytes = source.as_bytes();
    let mut state = State::Normal;
    let mut offset = 0;
    let mut statement_bytes = 0;
    let mut delimiter_depth = 0_usize;
    while offset < bytes.len() {
        let byte = bytes[offset];
        match state {
            State::Normal => {
                if byte == b'/' && bytes.get(offset + 1) == Some(&b'/') {
                    state = State::LineComment;
                    offset += 2;
                    continue;
                }
                if byte == b'/' && bytes.get(offset + 1) == Some(&b'*') {
                    return Err(FrontendError::Unsupported {
                        construct: "block comment",
                        snippet: source_snippet(source),
                    });
                }
                statement_bytes += 1;
                match byte {
                    b'"' => state = State::String { escaped: false },
                    b'(' | b'[' | b'{' => {
                        delimiter_depth += 1;
                        if delimiter_depth > MAX_DELIMITER_DEPTH {
                            return Err(source_limit_error("delimiter nesting", source));
                        }
                    }
                    b')' | b']' | b'}' => delimiter_depth = delimiter_depth.saturating_sub(1),
                    b';' => statement_bytes = 0,
                    _ => {}
                }
            }
            State::LineComment => {
                if byte == b'\n' || byte == b'\r' {
                    state = State::Normal;
                }
            }
            State::String { escaped } => {
                statement_bytes += 1;
                if escaped {
                    state = State::String { escaped: false };
                } else if byte == b'\\' {
                    state = State::String { escaped: true };
                } else if byte == b'"' {
                    state = State::Normal;
                }
            }
        }
        if statement_bytes > MAX_STATEMENT_BYTES {
            return Err(source_limit_error("statement size", source));
        }
        offset += 1;
    }
    Ok(())
}

fn source_limit_error(limit: &'static str, source: &str) -> FrontendError {
    FrontendError::Unsupported {
        construct: "source exceeding frontend resource limit",
        snippet: format!("{limit}: {}", source_snippet(source)),
    }
}

fn source_snippet(source: &str) -> String {
    let snippet = source.chars().take(160).collect::<String>();
    if snippet.trim().is_empty() {
        "empty source".to_owned()
    } else {
        snippet
    }
}

fn parse_str_inner(source: &str) -> Result<Program, FrontendError> {
    let parsed = oq3_syntax::SourceFile::parse_check_lex(source);
    if !parsed.errors().is_empty() {
        let diagnostics = parsed
            .errors()
            .iter()
            .map(|error| format!("{} at {:?}", error.message(), error.range()))
            .collect::<Vec<_>>()
            .join("; ");
        return Err(FrontendError::Parse(diagnostics));
    }
    if !parsed.have_parse() {
        return Err(FrontendError::Parse(
            "OpenQASM source could not be parsed".to_owned(),
        ));
    }
    Lowerer::default().lower(parsed.tree())
}

#[derive(Clone)]
enum QuantumOperand {
    Scalar(Qubit),
    Register(Vec<Qubit>),
}

impl QuantumOperand {
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

    fn width_if_register(&self) -> Option<usize> {
        match self {
            Self::Scalar(_) => None,
            Self::Register(qubits) => Some(qubits.len()),
        }
    }
}

enum ClassicalOperand {
    Scalar(ClassicalBit),
    Register(Vec<ClassicalBit>),
}

/// Exact rational function in the transcendental constant pi.  A normalized
/// rational-coefficient polynomial is zero at pi exactly when all of its
/// coefficients are zero, so this representation detects undefined division
/// without approximating source angles.
#[derive(Clone)]
struct ConstantValue {
    numerator: Vec<BigRational>,
    denominator: Vec<BigRational>,
}

impl ConstantValue {
    fn rational(value: BigRational) -> Self {
        Self {
            numerator: normalize_polynomial(vec![value]),
            denominator: vec![BigRational::from_integer(1.into())],
        }
    }

    fn pi() -> Self {
        Self {
            numerator: vec![BigRational::default(), BigRational::from_integer(1.into())],
            denominator: vec![BigRational::from_integer(1.into())],
        }
    }

    fn is_zero(&self) -> bool {
        self.numerator.is_empty()
    }

    fn negate(mut self) -> Self {
        for coefficient in &mut self.numerator {
            *coefficient = -coefficient.clone();
        }
        self
    }

    fn add(self, right: Self) -> Self {
        let numerator = polynomial_add(
            polynomial_multiply(&self.numerator, &right.denominator),
            polynomial_multiply(&right.numerator, &self.denominator),
        );
        let denominator = polynomial_multiply(&self.denominator, &right.denominator);
        Self {
            numerator,
            denominator,
        }
    }

    fn subtract(self, right: Self) -> Self {
        self.add(right.negate())
    }

    fn multiply(self, right: Self) -> Self {
        Self {
            numerator: polynomial_multiply(&self.numerator, &right.numerator),
            denominator: polynomial_multiply(&self.denominator, &right.denominator),
        }
    }

    fn divide(self, right: Self) -> Self {
        debug_assert!(!right.is_zero());
        Self {
            numerator: polynomial_multiply(&self.numerator, &right.denominator),
            denominator: polynomial_multiply(&self.denominator, &right.numerator),
        }
    }
}

impl ClassicalOperand {
    fn into_cells(self) -> Vec<ClassicalBit> {
        match self {
            Self::Scalar(bit) => vec![bit],
            Self::Register(bits) => bits,
        }
    }

    fn width_if_register(&self) -> Option<usize> {
        match self {
            Self::Scalar(_) => None,
            Self::Register(bits) => Some(bits.len()),
        }
    }
}

#[derive(Clone, Copy)]
enum GateDefinition {
    Native(Gate),
    Universal,
    UniversalQiskit,
    U2,
    Identity { timed: bool },
    Sx { inverse: bool },
    Ch,
    Cswap,
    Cu3,
}

impl GateDefinition {
    fn signature(self) -> (usize, usize) {
        match self {
            Self::Native(gate) => {
                let parameters = usize::from(matches!(
                    gate,
                    Gate::P
                        | Gate::Rx
                        | Gate::Ry
                        | Gate::Rz
                        | Gate::Cp
                        | Gate::Crx
                        | Gate::Cry
                        | Gate::Crz
                ));
                let qubits = match gate {
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
                (parameters, qubits)
            }
            Self::Universal | Self::UniversalQiskit => (3, 1),
            Self::U2 => (2, 1),
            Self::Identity { timed } => (usize::from(timed), 1),
            Self::Sx { .. } => (0, 1),
            Self::Ch => (0, 2),
            Self::Cswap => (0, 3),
            Self::Cu3 => (3, 2),
        }
    }
}

struct Lowerer {
    ids: AstIdGenerator,
    scopes: ScopeStack,
    quantum_registers: Vec<crate::ir::Register>,
    classical_registers: Vec<crate::ir::Register>,
    qelib1_loaded: bool,
}

impl Default for Lowerer {
    fn default() -> Self {
        Self {
            ids: AstIdGenerator::default(),
            scopes: ScopeStack::new_openqasm2(),
            quantum_registers: Vec::new(),
            classical_registers: Vec::new(),
            qelib1_loaded: false,
        }
    }
}

impl Lowerer {
    fn lower(mut self, source: ast::SourceFile) -> Result<Program, FrontendError> {
        if source
            .syntax()
            .children_with_tokens()
            .filter_map(|element| element.into_token())
            .any(|token| token.kind() == SyntaxKind::SEMICOLON)
        {
            return Err(FrontendError::Expected {
                expected: "no empty top-level statements",
                snippet: ";".to_owned(),
            });
        }
        let mut statements = source.statements();
        let Some(first) = statements.next() else {
            return Err(FrontendError::Expected {
                expected: "OPENQASM 2.0 as the first non-comment statement",
                snippet: "empty source".to_owned(),
            });
        };
        let Stmt::VersionString(version) = first else {
            return Err(expected!(
                "OPENQASM 2.0 as the first non-comment statement",
                &first
            ));
        };
        self.lower_version(version)?;

        let mut body = self.ids.node(BlockData::default());
        for statement in statements {
            if matches!(statement, Stmt::VersionString(_)) {
                return Err(expected!(
                    "exactly one OpenQASM version declaration",
                    &statement
                ));
            }
            self.lower_top_level(statement, &mut body)?;
        }

        let program = ProgramData {
            version: OpenQasmVersion { major: 2, minor: 0 },
            numeric_inputs: Vec::new(),
            quantum_registers: self.quantum_registers,
            classical_registers: self.classical_registers,
            body,
        };
        Ok(self.ids.node(program))
    }

    fn lower_version(&self, version: ast::VersionString) -> Result<(), FrontendError> {
        let raw = version.syntax().text().to_string();
        let uncommented = raw
            .lines()
            .map(|line| line.split_once("//").map_or(line, |(prefix, _)| prefix))
            .collect::<String>();
        let compact = uncommented
            .chars()
            .filter(|character| !character.is_ascii_whitespace())
            .collect::<String>();
        if compact != "OPENQASM2.0;" {
            return Err(unsupported!("OpenQASM version other than 2.0", &version));
        }
        Ok(())
    }

    fn lower_top_level(
        &mut self,
        statement: Stmt,
        body: &mut crate::ir::Block,
    ) -> Result<(), FrontendError> {
        match statement {
            Stmt::Include(include) => self.lower_include(include),
            Stmt::OldStyleDeclarationStatement(declaration) => {
                self.lower_declaration(declaration, body)
            }
            Stmt::Reset(_)
            | Stmt::ExprStmt(_)
            | Stmt::Measure(_)
            | Stmt::IfStmt(_)
            | Stmt::Barrier(_) => {
                body.statements.push(self.lower_statement(statement)?);
                Ok(())
            }
            Stmt::Gate(gate) => Err(unsupported!("custom gate declaration", &gate)),
            other => Err(unsupported!("statement", &other)),
        }
    }

    fn lower_include(&mut self, include: ast::Include) -> Result<(), FrontendError> {
        let file = include
            .file()
            .ok_or_else(|| expected!("an include path", &include))?;
        if file.syntax().text() != "\"qelib1.inc\"" {
            return Err(unsupported!("include path syntax", &include));
        }
        let path = file
            .to_string()
            .ok_or_else(|| expected!("an include path", &include))?;
        if path != "qelib1.inc" {
            return Err(unsupported!("include other than qelib1.inc", &include));
        }
        if self.qelib1_loaded {
            return Err(expected!(
                "qelib1.inc to be included at most once",
                &include
            ));
        }
        self.scopes.declare_qelib1_gates().map_err(scope_error)?;
        self.qelib1_loaded = true;
        Ok(())
    }

    fn lower_declaration(
        &mut self,
        declaration: ast::OldStyleDeclarationStatement,
        body: &mut crate::ir::Block,
    ) -> Result<(), FrontendError> {
        let parameter = declaration
            .old_typed_param()
            .ok_or_else(|| expected!("a qreg or creg declaration", &declaration))?;
        let name = old_declaration_name(&parameter)?;
        validate_identifier(&name)?;
        let width = old_declaration_width(&parameter)?;
        if width == 0 {
            return Err(expected!("a positive register width", &declaration));
        }
        if width > MAX_REGISTER_WIDTH {
            return Err(unsupported!(
                "register exceeding frontend width limit",
                &declaration
            ));
        }

        let is_quantum = parameter.qreg_token().is_some();
        let is_classical = parameter.creg_token().is_some();
        if is_quantum == is_classical {
            return Err(expected!("exactly one of qreg or creg", &parameter));
        }
        let kind = if is_quantum {
            BindingKind::QuantumVariable(QuantumType::Register { width })
        } else {
            BindingKind::ClassicalBit(BitType::Register { width })
        };
        let binding = self
            .scopes
            .declare(name.clone(), kind)
            .map_err(scope_error)?;
        let register = self.ids.node(RegisterData {
            id: binding.id,
            name,
            width,
        });

        if is_quantum {
            self.quantum_registers.push(register);
        } else {
            let assignments = (0..width)
                .map(|index| {
                    let value = self.ids.node(ClassicalExprKind::Bool(false));
                    self.ids.node(StatementKind::Assign {
                        target: ClassicalBit {
                            register: binding.id,
                            index,
                        },
                        value,
                    })
                })
                .collect();
            self.classical_registers.push(register);
            body.statements.push(self.sequence(assignments));
        }
        Ok(())
    }

    fn lower_statement(&mut self, statement: Stmt) -> Result<Statement, FrontendError> {
        match statement {
            Stmt::IfStmt(statement) => self.lower_if(statement),
            other => self.lower_quantum_operation(other),
        }
    }

    fn lower_quantum_operation(&mut self, statement: Stmt) -> Result<Statement, FrontendError> {
        match statement {
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
            Stmt::ExprStmt(expression_statement) => {
                let expression = expression_statement
                    .expr()
                    .ok_or_else(|| expected!("a gate call", &expression_statement))?;
                let Expr::GateCallExpr(call) = expression else {
                    return Err(unsupported!("expression statement", &expression_statement));
                };
                self.lower_gate(call)
            }
            Stmt::Measure(measurement) => self.lower_measurement(measurement),
            Stmt::Barrier(barrier) => self.lower_barrier(barrier),
            other => Err(unsupported!("quantum operation", &other)),
        }
    }

    fn lower_measurement(&mut self, measurement: ast::Measure) -> Result<Statement, FrontendError> {
        if measurement.thin_arrow_token().is_none() {
            return Err(expected!("`->` and a measurement target", &measurement));
        }
        let qubits = self.lower_quantum_expression(
            measurement
                .qubit()
                .ok_or_else(|| expected!("a measurement operand", &measurement))?,
        )?;
        let targets = self.lower_classical_expression(
            measurement
                .target()
                .ok_or_else(|| expected!("a measurement target", &measurement))?,
        )?;
        let matching = match (qubits.width_if_register(), targets.width_if_register()) {
            (None, None) => true,
            (Some(left), Some(right)) => left == right,
            _ => false,
        };
        if !matching {
            return Err(expected!(
                "matching indexed cells or equal-width registers for measurement",
                &measurement
            ));
        }
        let statements = qubits
            .into_cells()
            .into_iter()
            .zip(targets.into_cells())
            .map(|(qubit, target)| self.ids.node(StatementKind::Measure { qubit, target }))
            .collect();
        Ok(self.sequence(statements))
    }

    fn lower_barrier(&mut self, barrier: ast::Barrier) -> Result<Statement, FrontendError> {
        let operands = barrier
            .qubit_list()
            .ok_or_else(|| expected!("at least one barrier operand", &barrier))?;
        let gate_operands = operands.gate_operands().collect::<Vec<_>>();
        validate_comma_list(
            operands.syntax(),
            gate_operands.len(),
            "a comma-separated barrier operand list without a trailing comma",
        )?;
        for operand in gate_operands.iter().cloned() {
            self.lower_qubits(operand)?;
        }
        if gate_operands.is_empty() {
            return Err(expected!("at least one barrier operand", &barrier));
        }
        Ok(self.sequence(Vec::new()))
    }

    fn lower_if(&mut self, statement: ast::IfStmt) -> Result<Statement, FrontendError> {
        if statement.else_token().is_some()
            || statement.else_branch_block().is_some()
            || statement.else_branch_stmt().is_some()
        {
            return Err(unsupported!("else branch", &statement));
        }
        if statement.then_branch_block().is_some() {
            return Err(unsupported!("braced if body", &statement));
        }
        let condition = self.lower_condition(
            statement
                .condition()
                .ok_or_else(|| expected!("a classical-register comparison", &statement))?,
        )?;
        let operation = statement
            .then_branch_stmt()
            .ok_or_else(|| expected!("a single quantum operation after if", &statement))?;
        if matches!(operation, Stmt::Barrier(_)) {
            return Err(unsupported!(
                "barrier in a classical conditional",
                &operation
            ));
        }
        let operation = self.lower_quantum_operation(operation)?;
        let then_branch = self.ids.node(BlockData {
            classical_registers: Vec::new(),
            statements: vec![operation],
        });
        let else_branch = self.ids.node(BlockData::default());
        Ok(self.ids.node(StatementKind::If {
            condition,
            then_branch,
            else_branch,
        }))
    }

    fn lower_condition(&mut self, expression: Expr) -> Result<ClassicalExpr, FrontendError> {
        let Expr::BinExpr(binary) = expression else {
            return Err(unsupported!(
                "if condition other than creg == integer",
                &expression
            ));
        };
        if !matches!(
            binary.op_kind(),
            Some(ast::BinaryOp::CmpOp(ast::CmpOp::Eq { negated: false }))
        ) {
            return Err(unsupported!("if comparison operator", &binary));
        }
        let left = binary
            .lhs()
            .ok_or_else(|| expected!("a classical register on the left of ==", &binary))?;
        let Expr::Identifier(identifier) = left else {
            return Err(expected!("an unindexed classical register", &left));
        };
        let name = identifier.string();
        validate_identifier(&name)?;
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        let BindingKind::ClassicalBit(BitType::Register { width }) = binding.kind else {
            return Err(FrontendError::WrongIdentifierKind {
                name,
                expected: "classical register",
                actual: binding.kind.description(),
            });
        };
        let right = binary
            .rhs()
            .ok_or_else(|| expected!("a non-negative integer on the right of ==", &binary))?;
        let value = condition_integer(right)?;
        let limit = BigInt::from(1_u8) << width;
        if value >= limit {
            return Ok(self.ids.node(ClassicalExprKind::Bool(false)));
        }

        let mut equalities = Vec::with_capacity(width);
        for index in 0..width {
            let actual = self.ids.node(ClassicalExprKind::Bit(ClassicalBit {
                register: binding.id,
                index,
            }));
            let expected_value = ((&value >> index) & BigInt::from(1_u8)) == BigInt::from(1_u8);
            let expected = self.ids.node(ClassicalExprKind::Bool(expected_value));
            equalities.push(
                self.ids
                    .node(ClassicalExprKind::Eq(Box::new(actual), Box::new(expected))),
            );
        }
        let mut layer = equalities;
        while layer.len() > 1 {
            let mut next = Vec::with_capacity(layer.len().div_ceil(2));
            let mut expressions = layer.into_iter();
            while let Some(left) = expressions.next() {
                if let Some(right) = expressions.next() {
                    next.push(
                        self.ids
                            .node(ClassicalExprKind::And(Box::new(left), Box::new(right))),
                    );
                } else {
                    next.push(left);
                }
            }
            layer = next;
        }
        layer
            .pop()
            .ok_or_else(|| expected!("a nonempty classical register", &binary))
    }

    fn lower_gate(&mut self, call: ast::GateCallExpr) -> Result<Statement, FrontendError> {
        let source_name = call
            .identifier()
            .map(|identifier| identifier.string())
            .ok_or_else(|| expected!("a gate name", &call))?;
        if source_name != "U" && source_name != "CX" {
            validate_identifier(&source_name)?;
        }
        let binding = self.scopes.lookup(&source_name).map_err(scope_error)?;
        if !matches!(binding.kind, BindingKind::Gate) {
            return Err(FrontendError::WrongIdentifierKind {
                name: source_name,
                expected: "gate",
                actual: binding.kind.description(),
            });
        }
        let definition =
            gate_definition(&source_name).ok_or_else(|| FrontendError::Unsupported {
                construct: "gate",
                snippet: call.syntax().text().to_string(),
            })?;
        let argument_list = call.arg_list();
        if source_name == "CX" && argument_list.is_some() {
            return Err(expected!(
                "the primitive CX syntax without parentheses",
                &call
            ));
        }
        let parameter_expressions = match argument_list {
            Some(arguments) => match arguments.expression_list() {
                Some(expressions) => {
                    let parameters = expressions.exprs().collect::<Vec<_>>();
                    validate_comma_list(
                        expressions.syntax(),
                        parameters.len(),
                        "a comma-separated parameter list without a trailing comma",
                    )?;
                    parameters
                }
                None => {
                    validate_comma_list(
                        arguments.syntax(),
                        0,
                        "an empty parameter list without a comma",
                    )?;
                    Vec::new()
                }
            },
            None => Vec::new(),
        };
        let (parameter_arity, qubit_arity) = definition.signature();
        if parameter_expressions.len() != parameter_arity {
            return Err(expected!("the gate's declared number of parameters", &call));
        }
        for expression in parameter_expressions.iter().cloned() {
            self.validate_constant_expression(expression)?;
        }

        let operand_list = call
            .qubit_list()
            .ok_or_else(|| expected!("a gate operand list", &call))?;
        let gate_operands = operand_list.gate_operands().collect::<Vec<_>>();
        validate_comma_list(
            operand_list.syntax(),
            gate_operands.len(),
            "a comma-separated gate operand list without a trailing comma",
        )?;
        let operands = gate_operands
            .into_iter()
            .map(|operand| self.lower_qubits(operand))
            .collect::<Result<Vec<_>, _>>()?;
        if operands.len() != qubit_arity {
            return Err(expected!("the gate's declared number of operands", &call));
        }

        let mut register_widths = operands
            .iter()
            .filter_map(QuantumOperand::width_if_register);
        let width = register_widths.next().unwrap_or(1);
        if register_widths.any(|operand_width| operand_width != width) {
            return Err(expected!("equally sized or indexed gate operands", &call));
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
            return Err(expected!(
                "distinct qubit operands for each gate application",
                &call
            ));
        }

        if matches!(definition, GateDefinition::Identity { .. }) {
            return Ok(self.sequence(Vec::new()));
        }

        let snippet = call.syntax().text().to_string();
        let mut statements = Vec::new();
        for qubits in expanded_qubits {
            let parameters = parameter_expressions
                .iter()
                .cloned()
                .map(|expression| self.lower_numeric_expr(expression))
                .collect::<Result<Vec<_>, _>>()?;
            statements.extend(self.expand_gate(definition, parameters, qubits, &snippet)?);
        }
        Ok(self.sequence(statements))
    }

    fn expand_gate(
        &mut self,
        definition: GateDefinition,
        parameters: Vec<NumericExpr>,
        qubits: Vec<Qubit>,
        snippet: &str,
    ) -> Result<Vec<Statement>, FrontendError> {
        match definition {
            GateDefinition::Native(gate) => Ok(vec![self.apply(gate, parameters, qubits)]),
            GateDefinition::Universal | GateDefinition::UniversalQiskit => {
                let [theta, phi, lambda] = parameter_array(parameters, snippet)?;
                let [qubit] = qubit_array(qubits, snippet)?;
                let phase_gate = if matches!(definition, GateDefinition::Universal) {
                    Gate::Rz
                } else {
                    Gate::P
                };
                Ok(vec![
                    self.apply(phase_gate, vec![lambda], vec![qubit.clone()]),
                    self.apply(Gate::Ry, vec![theta], vec![qubit.clone()]),
                    self.apply(phase_gate, vec![phi], vec![qubit]),
                ])
            }
            GateDefinition::U2 => {
                let [phi, lambda] = parameter_array(parameters, snippet)?;
                let [qubit] = qubit_array(qubits, snippet)?;
                let theta = self.pi_over_two();
                Ok(vec![
                    self.apply(Gate::P, vec![lambda], vec![qubit.clone()]),
                    self.apply(Gate::Ry, vec![theta], vec![qubit.clone()]),
                    self.apply(Gate::P, vec![phi], vec![qubit]),
                ])
            }
            GateDefinition::Sx { inverse } => {
                let [qubit] = qubit_array(qubits, snippet)?;
                let phase = if inverse { Gate::Sdg } else { Gate::S };
                Ok(vec![
                    self.apply(Gate::H, Vec::new(), vec![qubit.clone()]),
                    self.apply(phase, Vec::new(), vec![qubit.clone()]),
                    self.apply(Gate::H, Vec::new(), vec![qubit]),
                ])
            }
            GateDefinition::Ch => {
                let [control, target] = qubit_array(qubits, snippet)?;
                Ok(vec![
                    self.apply(Gate::S, Vec::new(), vec![target.clone()]),
                    self.apply(Gate::H, Vec::new(), vec![target.clone()]),
                    self.apply(Gate::T, Vec::new(), vec![target.clone()]),
                    self.apply(Gate::Cx, Vec::new(), vec![control, target.clone()]),
                    self.apply(Gate::Tdg, Vec::new(), vec![target.clone()]),
                    self.apply(Gate::H, Vec::new(), vec![target.clone()]),
                    self.apply(Gate::Sdg, Vec::new(), vec![target]),
                ])
            }
            GateDefinition::Cswap => {
                let [control, left, right] = qubit_array(qubits, snippet)?;
                Ok(vec![
                    self.apply(Gate::Cx, Vec::new(), vec![right.clone(), left.clone()]),
                    self.apply(
                        Gate::Ccx,
                        Vec::new(),
                        vec![control, left.clone(), right.clone()],
                    ),
                    self.apply(Gate::Cx, Vec::new(), vec![right, left]),
                ])
            }
            GateDefinition::Cu3 => {
                let [theta, phi, lambda] = parameter_array(parameters, snippet)?;
                let [control, target] = qubit_array(qubits, snippet)?;

                let fourth_lambda = self.clone_numeric_expr(&lambda);
                let second_phi = self.clone_numeric_expr(&phi);
                let fourth_phi = self.clone_numeric_expr(&phi);
                let fifth_theta = self.clone_numeric_expr(&theta);

                let difference = self
                    .ids
                    .node(NumericExprKind::Sub(Box::new(lambda), Box::new(second_phi)));
                let second = self.half(difference);
                let fourth_sum = self.ids.node(NumericExprKind::Add(
                    Box::new(fourth_phi),
                    Box::new(fourth_lambda),
                ));
                let fourth_half = self.half(fourth_sum);
                let fourth = self.negate_numeric(fourth_half);
                let fifth_half = self.half(fifth_theta);
                let fifth = self.negate_numeric(fifth_half);
                let seventh = self.half(theta);

                Ok(vec![
                    self.apply(Gate::P, vec![second], vec![target.clone()]),
                    self.apply(Gate::Cx, Vec::new(), vec![control.clone(), target.clone()]),
                    self.apply(Gate::P, vec![fourth], vec![target.clone()]),
                    self.apply(Gate::Ry, vec![fifth], vec![target.clone()]),
                    self.apply(Gate::Cx, Vec::new(), vec![control, target.clone()]),
                    self.apply(Gate::Ry, vec![seventh], vec![target.clone()]),
                    self.apply(Gate::P, vec![phi], vec![target]),
                ])
            }
            GateDefinition::Identity { .. } => Ok(Vec::new()),
        }
    }

    fn apply(&mut self, gate: Gate, parameters: Vec<NumericExpr>, qubits: Vec<Qubit>) -> Statement {
        self.ids.node(StatementKind::Apply {
            gate,
            parameters,
            qubits,
        })
    }

    fn pi_over_two(&mut self) -> NumericExpr {
        let pi = self
            .ids
            .node(NumericExprKind::Constant(crate::ir::NumericConstant::Pi));
        self.half(pi)
    }

    fn half(&mut self, expression: NumericExpr) -> NumericExpr {
        let two = self
            .ids
            .node(NumericExprKind::Rational(BigRational::from_integer(
                2.into(),
            )));
        self.ids
            .node(NumericExprKind::Div(Box::new(expression), Box::new(two)))
    }

    fn negate_numeric(&mut self, expression: NumericExpr) -> NumericExpr {
        self.ids.node(NumericExprKind::Neg(Box::new(expression)))
    }

    fn lower_numeric_expr(&mut self, expression: Expr) -> Result<NumericExpr, FrontendError> {
        match expression {
            Expr::Literal(literal) => match literal.kind() {
                ast::LiteralKind::IntNumber(number) => {
                    let value = BigRational::from_integer(exact_decimal_integer(&number)?);
                    Ok(self.ids.node(NumericExprKind::Rational(value)))
                }
                ast::LiteralKind::FloatNumber(number) => {
                    let value = exact_decimal(&number)?;
                    Ok(self.ids.node(NumericExprKind::Rational(value)))
                }
                _ => Err(unsupported!("non-numeric gate parameter", &literal)),
            },
            Expr::Identifier(identifier) => {
                let name = identifier.string();
                validate_identifier(&name)?;
                let binding = self.scopes.lookup(&name).map_err(scope_error)?;
                match binding.kind {
                    BindingKind::Constant(constant) => {
                        Ok(self.ids.node(NumericExprKind::Constant(constant)))
                    }
                    actual => Err(FrontendError::WrongIdentifierKind {
                        name,
                        expected: "numeric constant",
                        actual: actual.description(),
                    }),
                }
            }
            Expr::ParenExpr(parenthesized) => {
                self.lower_numeric_expr(parenthesized.expr().ok_or_else(|| {
                    expected!("a parenthesized numeric expression", &parenthesized)
                })?)
            }
            Expr::PrefixExpr(prefix) => {
                if !matches!(prefix.op_kind(), Some(ast::UnaryOp::Neg)) {
                    return Err(unsupported!("numeric prefix operator", &prefix));
                }
                let operand = self.lower_numeric_expr(
                    prefix
                        .expr()
                        .ok_or_else(|| expected!("a numeric prefix operand", &prefix))?,
                )?;
                Ok(self.ids.node(NumericExprKind::Neg(Box::new(operand))))
            }
            Expr::BinExpr(binary) => {
                let left = self.lower_numeric_expr(
                    binary
                        .lhs()
                        .ok_or_else(|| expected!("a left numeric operand", &binary))?,
                )?;
                let right = self.lower_numeric_expr(
                    binary
                        .rhs()
                        .ok_or_else(|| expected!("a right numeric operand", &binary))?,
                )?;
                let kind = match binary.op_kind() {
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Add)) => {
                        NumericExprKind::Add(Box::new(left), Box::new(right))
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Sub)) => {
                        NumericExprKind::Sub(Box::new(left), Box::new(right))
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Mul)) => {
                        NumericExprKind::Mul(Box::new(left), Box::new(right))
                    }
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Div)) => {
                        NumericExprKind::Div(Box::new(left), Box::new(right))
                    }
                    _ => return Err(unsupported!("numeric binary operator", &binary)),
                };
                Ok(self.ids.node(kind))
            }
            other => Err(unsupported!("numeric gate parameter", &other)),
        }
    }

    /// Validates a source parameter exactly without consuming an AST ID.  This
    /// also covers `u0`, whose timing parameter has no node in the untimed IR.
    fn validate_constant_expression(
        &self,
        expression: Expr,
    ) -> Result<ConstantValue, FrontendError> {
        match expression {
            Expr::Literal(literal) => match literal.kind() {
                ast::LiteralKind::IntNumber(number) => Ok(ConstantValue::rational(
                    BigRational::from_integer(exact_decimal_integer(&number)?),
                )),
                ast::LiteralKind::FloatNumber(number) => {
                    Ok(ConstantValue::rational(exact_decimal(&number)?))
                }
                _ => Err(unsupported!("non-numeric gate parameter", &literal)),
            },
            Expr::Identifier(identifier) => {
                let name = identifier.string();
                validate_identifier(&name)?;
                let binding = self.scopes.lookup(&name).map_err(scope_error)?;
                match binding.kind {
                    BindingKind::Constant(crate::ir::NumericConstant::Pi) => {
                        Ok(ConstantValue::pi())
                    }
                    BindingKind::Constant(_) => Err(FrontendError::Unsupported {
                        construct: "OpenQASM 3 numeric constant",
                        snippet: name,
                    }),
                    actual => Err(FrontendError::WrongIdentifierKind {
                        name,
                        expected: "numeric constant",
                        actual: actual.description(),
                    }),
                }
            }
            Expr::ParenExpr(parenthesized) => {
                self.validate_constant_expression(parenthesized.expr().ok_or_else(|| {
                    expected!("a parenthesized numeric expression", &parenthesized)
                })?)
            }
            Expr::PrefixExpr(prefix) => {
                if !matches!(prefix.op_kind(), Some(ast::UnaryOp::Neg)) {
                    return Err(unsupported!("numeric prefix operator", &prefix));
                }
                Ok(self
                    .validate_constant_expression(
                        prefix
                            .expr()
                            .ok_or_else(|| expected!("a numeric prefix operand", &prefix))?,
                    )?
                    .negate())
            }
            Expr::BinExpr(binary) => {
                let operation = binary.op_kind();
                let left = self.validate_constant_expression(
                    binary
                        .lhs()
                        .ok_or_else(|| expected!("a left numeric operand", &binary))?,
                )?;
                let right = self.validate_constant_expression(
                    binary
                        .rhs()
                        .ok_or_else(|| expected!("a right numeric operand", &binary))?,
                )?;
                match operation {
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Add)) => Ok(left.add(right)),
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Sub)) => Ok(left.subtract(right)),
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Mul)) => Ok(left.multiply(right)),
                    Some(ast::BinaryOp::ArithOp(ast::ArithOp::Div)) => {
                        if right.is_zero() {
                            Err(expected!("a nonzero numeric divisor", &binary))
                        } else {
                            Ok(left.divide(right))
                        }
                    }
                    _ => Err(unsupported!("numeric binary operator", &binary)),
                }
            }
            other => Err(unsupported!("numeric gate parameter", &other)),
        }
    }

    fn lower_qubits(&self, operand: GateOperand) -> Result<QuantumOperand, FrontendError> {
        match operand {
            GateOperand::Identifier(identifier) => self.quantum_register(identifier.string()),
            GateOperand::IndexedIdentifier(indexed) => {
                let (name, index) = indexed_name_and_index(indexed)?;
                Ok(QuantumOperand::Scalar(self.checked_qubit(name, index)?))
            }
            GateOperand::HardwareQubit(hardware) => {
                Err(unsupported!("physical qubit operand", &hardware))
            }
        }
    }

    fn lower_quantum_expression(&self, expression: Expr) -> Result<QuantumOperand, FrontendError> {
        match expression {
            Expr::Identifier(identifier) => self.quantum_register(identifier.string()),
            Expr::IndexedIdentifier(indexed) => {
                let (name, index) = indexed_name_and_index(indexed)?;
                Ok(QuantumOperand::Scalar(self.checked_qubit(name, index)?))
            }
            other => Err(unsupported!("quantum operand", &other)),
        }
    }

    fn quantum_register(&self, name: String) -> Result<QuantumOperand, FrontendError> {
        validate_identifier(&name)?;
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        let BindingKind::QuantumVariable(QuantumType::Register { width }) = binding.kind else {
            return Err(FrontendError::WrongIdentifierKind {
                name,
                expected: "quantum register",
                actual: binding.kind.description(),
            });
        };
        Ok(QuantumOperand::Register(
            (0..width)
                .map(|index| Qubit {
                    register: binding.id,
                    index,
                })
                .collect(),
        ))
    }

    fn checked_qubit(&self, name: String, index: usize) -> Result<Qubit, FrontendError> {
        validate_identifier(&name)?;
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        let BindingKind::QuantumVariable(QuantumType::Register { width }) = binding.kind else {
            return Err(FrontendError::WrongIdentifierKind {
                name,
                expected: "quantum register",
                actual: binding.kind.description(),
            });
        };
        check_index(&name, index, width)?;
        Ok(Qubit {
            register: binding.id,
            index,
        })
    }

    fn lower_classical_expression(
        &self,
        expression: Expr,
    ) -> Result<ClassicalOperand, FrontendError> {
        match expression {
            Expr::Identifier(identifier) => self.classical_register(identifier.string()),
            Expr::IndexedIdentifier(indexed) => {
                let (name, index) = indexed_name_and_index(indexed)?;
                Ok(ClassicalOperand::Scalar(
                    self.checked_classical_bit(name, index)?,
                ))
            }
            other => Err(unsupported!("classical measurement target", &other)),
        }
    }

    fn classical_register(&self, name: String) -> Result<ClassicalOperand, FrontendError> {
        validate_identifier(&name)?;
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        let BindingKind::ClassicalBit(BitType::Register { width }) = binding.kind else {
            return Err(FrontendError::WrongIdentifierKind {
                name,
                expected: "classical register",
                actual: binding.kind.description(),
            });
        };
        Ok(ClassicalOperand::Register(
            (0..width)
                .map(|index| ClassicalBit {
                    register: binding.id,
                    index,
                })
                .collect(),
        ))
    }

    fn checked_classical_bit(
        &self,
        name: String,
        index: usize,
    ) -> Result<ClassicalBit, FrontendError> {
        validate_identifier(&name)?;
        let binding = self.scopes.lookup(&name).map_err(scope_error)?;
        let BindingKind::ClassicalBit(BitType::Register { width }) = binding.kind else {
            return Err(FrontendError::WrongIdentifierKind {
                name,
                expected: "classical register",
                actual: binding.kind.description(),
            });
        };
        check_index(&name, index, width)?;
        Ok(ClassicalBit {
            register: binding.id,
            index,
        })
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

    fn sequence(&mut self, mut statements: Vec<Statement>) -> Statement {
        if statements.len() == 1 {
            return statements.remove(0);
        }
        let block = self.ids.node(BlockData {
            classical_registers: Vec::new(),
            statements,
        });
        self.ids.node(StatementKind::Scope(block))
    }
}

fn gate_definition(name: &str) -> Option<GateDefinition> {
    let definition = match name {
        "U" => GateDefinition::Universal,
        "CX" | "cx" => GateDefinition::Native(Gate::Cx),
        // Qiskit's historical OpenQASM 2 aliases use the phase-gate
        // representative of U3.  The uppercase language primitive above keeps
        // the normative SU(2) representative instead.
        "u" | "u3" => GateDefinition::UniversalQiskit,
        "u2" => GateDefinition::U2,
        "u1" | "p" => GateDefinition::Native(Gate::P),
        "id" => GateDefinition::Identity { timed: false },
        "u0" => GateDefinition::Identity { timed: true },
        "x" => GateDefinition::Native(Gate::X),
        "y" => GateDefinition::Native(Gate::Y),
        "z" => GateDefinition::Native(Gate::Z),
        "h" => GateDefinition::Native(Gate::H),
        "s" => GateDefinition::Native(Gate::S),
        "sdg" => GateDefinition::Native(Gate::Sdg),
        "t" => GateDefinition::Native(Gate::T),
        "tdg" => GateDefinition::Native(Gate::Tdg),
        "rx" => GateDefinition::Native(Gate::Rx),
        "ry" => GateDefinition::Native(Gate::Ry),
        "rz" => GateDefinition::Native(Gate::Rz),
        "sx" => GateDefinition::Sx { inverse: false },
        "sxdg" => GateDefinition::Sx { inverse: true },
        "cy" => GateDefinition::Native(Gate::Cy),
        "cz" => GateDefinition::Native(Gate::Cz),
        "swap" => GateDefinition::Native(Gate::Swap),
        "ch" => GateDefinition::Ch,
        "ccx" => GateDefinition::Native(Gate::Ccx),
        "cswap" => GateDefinition::Cswap,
        "crx" => GateDefinition::Native(Gate::Crx),
        "cry" => GateDefinition::Native(Gate::Cry),
        "crz" => GateDefinition::Native(Gate::Crz),
        "cu1" | "cp" => GateDefinition::Native(Gate::Cp),
        "cu3" => GateDefinition::Cu3,
        _ => return None,
    };
    Some(definition)
}

fn parameter_array<const N: usize>(
    parameters: Vec<NumericExpr>,
    snippet: &str,
) -> Result<[NumericExpr; N], FrontendError> {
    parameters.try_into().map_err(|_| FrontendError::Expected {
        expected: "the gate's declared number of parameters",
        snippet: snippet.to_owned(),
    })
}

fn qubit_array<const N: usize>(
    qubits: Vec<Qubit>,
    snippet: &str,
) -> Result<[Qubit; N], FrontendError> {
    qubits.try_into().map_err(|_| FrontendError::Expected {
        expected: "the gate's declared number of operands",
        snippet: snippet.to_owned(),
    })
}

fn validate_comma_list(
    syntax: &oq3_syntax::SyntaxNode,
    item_count: usize,
    expectation: &'static str,
) -> Result<(), FrontendError> {
    let commas = syntax
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .filter(|token| token.kind() == SyntaxKind::COMMA)
        .count();
    if commas == item_count.saturating_sub(1) {
        Ok(())
    } else {
        Err(FrontendError::Expected {
            expected: expectation,
            snippet: syntax.text().to_string(),
        })
    }
}

fn old_declaration_name(parameter: &ast::OldTypedParam) -> Result<String, FrontendError> {
    parameter
        .syntax()
        .children_with_tokens()
        .filter_map(|element| element.into_token())
        .find(|token| token.kind() == SyntaxKind::IDENT)
        .map(|token| token.text().to_owned())
        .ok_or_else(|| expected!("a register name", parameter))
}

fn old_declaration_width(parameter: &ast::OldTypedParam) -> Result<usize, FrontendError> {
    let mut operators = parameter
        .syntax()
        .children()
        .filter_map(ast::IndexOperator::cast);
    let operator = operators
        .next()
        .ok_or_else(|| expected!("one register width", parameter))?;
    if operators.next().is_some() {
        return Err(unsupported!("multiple register dimensions", parameter));
    }
    index_operator_value(operator)
}

fn indexed_name_and_index(
    indexed: ast::IndexedIdentifier,
) -> Result<(String, usize), FrontendError> {
    let name = indexed
        .identifier()
        .map(|identifier| identifier.string())
        .ok_or_else(|| expected!("an indexed identifier name", &indexed))?;
    validate_identifier(&name)?;
    let mut operators = indexed.index_operators();
    let operator = operators
        .next()
        .ok_or_else(|| expected!("one register index", &indexed))?;
    if operators.next().is_some() {
        return Err(unsupported!("multi-dimensional register index", &indexed));
    }
    Ok((name, index_operator_value(operator)?))
}

fn index_operator_value(operator: ast::IndexOperator) -> Result<usize, FrontendError> {
    let Some(IndexKind::ExpressionList(list)) = operator.index_kind() else {
        return Err(unsupported!("index set or range", &operator));
    };
    let expressions = list.exprs().collect::<Vec<_>>();
    validate_comma_list(
        list.syntax(),
        expressions.len(),
        "one integer index without a comma",
    )?;
    let expression = expressions
        .first()
        .cloned()
        .ok_or_else(|| expected!("one non-negative integer index", &list))?;
    if expressions.len() != 1 {
        return Err(unsupported!("multiple register indices", &list));
    }
    literal_usize(expression)
}

fn literal_usize(expression: Expr) -> Result<usize, FrontendError> {
    let Expr::Literal(literal) = expression else {
        return Err(expected!(
            "a non-negative decimal integer literal",
            &expression
        ));
    };
    let ast::LiteralKind::IntNumber(number) = literal.kind() else {
        return Err(expected!(
            "a non-negative decimal integer literal",
            &literal
        ));
    };
    let value = exact_decimal_integer(&number)?;
    usize::try_from(value).map_err(|_| FrontendError::Expected {
        expected: "a register width or index representable by this platform",
        snippet: number.to_string(),
    })
}

fn condition_integer(expression: Expr) -> Result<BigInt, FrontendError> {
    let Expr::Literal(literal) = expression else {
        return Err(expected!(
            "a non-negative decimal integer literal",
            &expression
        ));
    };
    let ast::LiteralKind::IntNumber(number) = literal.kind() else {
        return Err(expected!(
            "a non-negative decimal integer literal",
            &literal
        ));
    };
    exact_decimal_integer(&number)
}

fn exact_decimal_integer(number: &ast::IntNumber) -> Result<BigInt, FrontendError> {
    let (_, digits, suffix) = number.split_into_parts();
    if number.radix() != ast::Radix::Decimal
        || !suffix.is_empty()
        || digits.is_empty()
        || !digits.bytes().all(|byte| byte.is_ascii_digit())
        || (digits.len() > 1 && digits.starts_with('0'))
    {
        return Err(FrontendError::Expected {
            expected: "an unsuffixed decimal integer literal",
            snippet: number.to_string(),
        });
    }
    BigInt::parse_bytes(digits.as_bytes(), 10).ok_or_else(|| FrontendError::Expected {
        expected: "a decimal integer literal",
        snippet: number.to_string(),
    })
}

fn exact_decimal(number: &ast::FloatNumber) -> Result<BigRational, FrontendError> {
    let (decimal, suffix) = number.split_into_parts();
    if !suffix.is_empty() || decimal.contains('_') {
        return Err(FrontendError::Expected {
            expected: "an unsuffixed decimal gate parameter",
            snippet: number.to_string(),
        });
    }
    let decimal = BigDecimal::from_str(decimal).map_err(|_| FrontendError::Expected {
        expected: "a finite decimal gate parameter",
        snippet: number.to_string(),
    })?;
    let (digits, exponent) = decimal.into_bigint_and_exponent();
    let magnitude =
        u32::try_from(exponent.unsigned_abs()).map_err(|_| FrontendError::Expected {
            expected: "a representable decimal exponent",
            snippet: number.to_string(),
        })?;
    if magnitude > MAX_DECIMAL_EXPONENT {
        return Err(FrontendError::Unsupported {
            construct: "decimal exponent exceeding frontend resource limit",
            snippet: number.to_string(),
        });
    }
    let power = BigInt::from(10_u8).pow(magnitude);
    if exponent >= 0 {
        Ok(BigRational::new(digits, power))
    } else {
        Ok(BigRational::from_integer(digits * power))
    }
}

fn normalize_polynomial(mut polynomial: Vec<BigRational>) -> Vec<BigRational> {
    while polynomial
        .last()
        .is_some_and(|coefficient| coefficient == &BigRational::default())
    {
        polynomial.pop();
    }
    polynomial
}

fn polynomial_add(mut left: Vec<BigRational>, right: Vec<BigRational>) -> Vec<BigRational> {
    left.resize(left.len().max(right.len()), BigRational::default());
    for (index, coefficient) in right.into_iter().enumerate() {
        left[index] += coefficient;
    }
    normalize_polynomial(left)
}

fn polynomial_multiply(left: &[BigRational], right: &[BigRational]) -> Vec<BigRational> {
    if left.is_empty() || right.is_empty() {
        return Vec::new();
    }
    let mut product = vec![BigRational::default(); left.len() + right.len() - 1];
    for (left_degree, left_coefficient) in left.iter().enumerate() {
        for (right_degree, right_coefficient) in right.iter().enumerate() {
            product[left_degree + right_degree] += left_coefficient * right_coefficient;
        }
    }
    normalize_polynomial(product)
}

fn validate_identifier(name: &str) -> Result<(), FrontendError> {
    let mut characters = name.chars();
    let valid = characters
        .next()
        .is_some_and(|character| character.is_ascii_lowercase())
        && characters.all(|character| character.is_ascii_alphanumeric() || character == '_');
    if valid {
        Ok(())
    } else {
        Err(FrontendError::InvalidIdentifier(name.to_owned()))
    }
}

fn check_index(name: &str, index: usize, width: usize) -> Result<(), FrontendError> {
    if index < width {
        Ok(())
    } else {
        Err(FrontendError::IndexOutOfBounds {
            name: name.to_owned(),
            index,
            width,
        })
    }
}

fn scope_error(error: ScopeError) -> FrontendError {
    match error {
        ScopeError::AlreadyDeclared(name) => FrontendError::DuplicateIdentifier(name),
        ScopeError::CannotShadow(name) => FrontendError::CannotShadow(name),
        ScopeError::Unknown(name) => FrontendError::UnknownIdentifier(name),
        ScopeError::IllegalDeclaration { declaration, scope } => FrontendError::Expected {
            expected: "a legal global OpenQASM 2 declaration",
            snippet: format!("{declaration} declaration in {scope:?} scope"),
        },
    }
}
