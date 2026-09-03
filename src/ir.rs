use std::cmp::Ordering;
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, DerefMut};

use num_rational::BigRational;

/// Program-local identity shared by every owned IR node.
///
/// IDs are dense, allocated monotonically, and used only for indexing side
/// tables such as slicing or data-flow results. They do not participate in
/// the semantic equality, ordering, or hashing of a node.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AstId(pub(crate) usize);

impl AstId {
    pub fn index(self) -> usize {
        self.0
    }
}

/// An IR node with identity separated from semantic content.
#[derive(Debug, Clone)]
pub struct AstNode<T> {
    pub(crate) ast_id: AstId,
    pub kind: T,
}

impl<T> AstNode<T> {
    pub(crate) fn new(ast_id: AstId, kind: T) -> Self {
        Self { ast_id, kind }
    }

    pub fn ast_id(&self) -> AstId {
        self.ast_id
    }
}

impl<T> Deref for AstNode<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.kind
    }
}

impl<T> DerefMut for AstNode<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.kind
    }
}

impl<T: PartialEq> PartialEq for AstNode<T> {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl<T: Eq> Eq for AstNode<T> {}

impl<T: PartialOrd> PartialOrd for AstNode<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.kind.partial_cmp(&other.kind)
    }
}

impl<T: Ord> Ord for AstNode<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.kind.cmp(&other.kind)
    }
}

impl<T: Hash> Hash for AstNode<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.kind.hash(state);
    }
}

/// Monotone allocator for the unified program-local AST-ID namespace.
#[derive(Debug, Default)]
pub(crate) struct AstIdGenerator {
    next: usize,
}

impl AstIdGenerator {
    pub(crate) fn starting_at(next: usize) -> Self {
        Self { next }
    }

    /// Allocates one node in the shared namespace.
    pub(crate) fn node<T>(&mut self, kind: T) -> AstNode<T> {
        let node = AstNode::new(AstId(self.next), kind);
        self.next += 1;
        node
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OpenQasmVersion {
    pub major: u32,
    pub minor: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RegisterData {
    pub id: SymbolId,
    pub name: String,
    pub width: usize,
}

pub type Register = AstNode<RegisterData>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SymbolId(pub usize);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Qubit {
    pub register: SymbolId,
    pub index: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ClassicalBit {
    pub register: SymbolId,
    pub index: usize,
}

/// Numeric types accepted as OpenQASM program inputs and gate parameters.
/// The optional width distinguishes declarations such as `angle theta` and
/// `angle[20] theta` without choosing a host-language representation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NumericType {
    Int(Option<usize>),
    Uint(Option<usize>),
    Float(Option<usize>),
    Angle(Option<usize>),
}

/// A numeric input declared with OpenQASM's `input` modifier.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NumericInputData {
    pub id: SymbolId,
    pub name: String,
    pub ty: NumericType,
}

pub type NumericInput = AstNode<NumericInputData>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NumericConstant {
    Pi,
    Tau,
    Euler,
}

/// Numeric expression used as a parameter to a gate.
///
/// Finite integer, decimal, and scientific literals are normalized exactly:
/// `0.1`, `0.100`, and `1e-1` all become the same rational expression. The
/// enclosing [`AstNode`] retains source identity without affecting this
/// semantic equality. Expressions such as `-theta / 2 + pi/4` retain their
/// symbolic structure instead of being converted to floating point.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NumericExprKind {
    Rational(BigRational),
    Constant(NumericConstant),
    Input(SymbolId),
    Neg(Box<NumericExpr>),
    Add(Box<NumericExpr>, Box<NumericExpr>),
    Sub(Box<NumericExpr>, Box<NumericExpr>),
    Mul(Box<NumericExpr>, Box<NumericExpr>),
    Div(Box<NumericExpr>, Box<NumericExpr>),
}

pub type NumericExpr = AstNode<NumericExprKind>;

impl fmt::Display for AstNode<NumericExprKind> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.kind {
            NumericExprKind::Rational(value) => write!(formatter, "{value}"),
            NumericExprKind::Constant(NumericConstant::Pi) => formatter.write_str("π"),
            NumericExprKind::Constant(NumericConstant::Tau) => formatter.write_str("τ"),
            NumericExprKind::Constant(NumericConstant::Euler) => formatter.write_str("ℇ"),
            NumericExprKind::Input(id) => write!(formatter, "input{}", id.0),
            NumericExprKind::Neg(value) => write!(formatter, "-({value})"),
            NumericExprKind::Add(left, right) => write!(formatter, "({left} + {right})"),
            NumericExprKind::Sub(left, right) => write!(formatter, "({left} - {right})"),
            NumericExprKind::Mul(left, right) => write!(formatter, "({left} * {right})"),
            NumericExprKind::Div(left, right) => write!(formatter, "({left} / {right})"),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Gate {
    H,
    X,
    Y,
    Z,
    S,
    Sdg,
    T,
    Tdg,
    Cx,
    Cy,
    Cz,
    Swap,
    P,
    Rx,
    Ry,
    Rz,
    Cp,
    Crx,
    Cry,
    Crz,
    Ccx,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassicalExprKind {
    Bool(bool),
    Bit(ClassicalBit),
    Not(Box<ClassicalExpr>),
    Eq(Box<ClassicalExpr>, Box<ClassicalExpr>),
    And(Box<ClassicalExpr>, Box<ClassicalExpr>),
    Or(Box<ClassicalExpr>, Box<ClassicalExpr>),
    Xor(Box<ClassicalExpr>, Box<ClassicalExpr>),
}

pub type ClassicalExpr = AstNode<ClassicalExprKind>;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct BlockData {
    pub classical_registers: Vec<Register>,
    pub statements: Vec<Statement>,
}

pub type Block = AstNode<BlockData>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StatementKind {
    Reset(Qubit),
    Apply {
        gate: Gate,
        parameters: Vec<NumericExpr>,
        qubits: Vec<Qubit>,
    },
    Measure {
        qubit: Qubit,
        target: ClassicalBit,
    },
    Assign {
        target: ClassicalBit,
        value: ClassicalExpr,
    },
    If {
        condition: ClassicalExpr,
        then_branch: Block,
        else_branch: Block,
    },
    /// A lexical sequence introduced while lowering one source operation,
    /// such as a register-wide measurement or a specialized subroutine call.
    Scope(Block),
}

pub type Statement = AstNode<StatementKind>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProgramData {
    pub version: OpenQasmVersion,
    pub numeric_inputs: Vec<NumericInput>,
    pub quantum_registers: Vec<Register>,
    pub classical_registers: Vec<Register>,
    pub body: Block,
}

pub type Program = AstNode<ProgramData>;

impl AstNode<ProgramData> {
    /// Visits every owned IR node in this program, including expressions and
    /// declarations. References such as [`Qubit`] and [`ClassicalBit`] are not
    /// nodes and therefore have no independent AST ID.
    pub fn visit_ast_ids(&self, mut visit: impl FnMut(AstId)) {
        fn numeric(expression: &NumericExpr, visit: &mut impl FnMut(AstId)) {
            visit(expression.ast_id);
            match &expression.kind {
                NumericExprKind::Neg(inner) => numeric(inner, visit),
                NumericExprKind::Add(left, right)
                | NumericExprKind::Sub(left, right)
                | NumericExprKind::Mul(left, right)
                | NumericExprKind::Div(left, right) => {
                    numeric(left, visit);
                    numeric(right, visit);
                }
                NumericExprKind::Rational(_)
                | NumericExprKind::Constant(_)
                | NumericExprKind::Input(_) => {}
            }
        }

        fn classical(expression: &ClassicalExpr, visit: &mut impl FnMut(AstId)) {
            visit(expression.ast_id);
            match &expression.kind {
                ClassicalExprKind::Not(inner) => classical(inner, visit),
                ClassicalExprKind::Eq(left, right)
                | ClassicalExprKind::And(left, right)
                | ClassicalExprKind::Or(left, right)
                | ClassicalExprKind::Xor(left, right) => {
                    classical(left, visit);
                    classical(right, visit);
                }
                ClassicalExprKind::Bool(_) | ClassicalExprKind::Bit(_) => {}
            }
        }

        fn visit_block(block: &Block, visit: &mut impl FnMut(AstId)) {
            visit(block.ast_id);
            for register in &block.classical_registers {
                visit(register.ast_id);
            }
            for statement in &block.statements {
                visit(statement.ast_id);
                match &statement.kind {
                    StatementKind::Apply { parameters, .. } => {
                        for parameter in parameters {
                            numeric(parameter, visit);
                        }
                    }
                    StatementKind::If {
                        condition,
                        then_branch,
                        else_branch,
                    } => {
                        classical(condition, visit);
                        visit_block(then_branch, visit);
                        visit_block(else_branch, visit);
                    }
                    StatementKind::Assign { value, .. } => classical(value, visit),
                    StatementKind::Scope(body) => visit_block(body, visit),
                    StatementKind::Reset(_) | StatementKind::Measure { .. } => {}
                }
            }
        }

        visit(self.ast_id);
        for input in &self.numeric_inputs {
            visit(input.ast_id);
        }
        for register in self
            .quantum_registers
            .iter()
            .chain(&self.classical_registers)
        {
            visit(register.ast_id);
        }
        visit_block(&self.body, &mut visit);
    }

    /// One past the largest AST ID in this program.
    pub fn ast_id_bound(&self) -> usize {
        let mut bound = 0;
        self.visit_ast_ids(|id| bound = bound.max(id.0 + 1));
        bound
    }

    pub fn operation_count(&self) -> usize {
        fn count(block: &Block) -> usize {
            block
                .statements
                .iter()
                .map(|statement| match &statement.kind {
                    StatementKind::If {
                        then_branch,
                        else_branch,
                        ..
                    } => 1 + count(then_branch) + count(else_branch),
                    StatementKind::Scope(body) => count(body),
                    _ => 1,
                })
                .sum()
        }

        count(&self.body)
    }
}
