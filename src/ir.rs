use std::fmt;

use num_rational::BigRational;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct OpenQasmVersion {
    pub major: u32,
    pub minor: u32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Register {
    pub id: SymbolId,
    pub name: String,
    pub width: usize,
}

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
pub struct NumericInput {
    pub id: SymbolId,
    pub name: String,
    pub ty: NumericType,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NumericConstant {
    Pi,
    Tau,
    Euler,
}

/// Numeric expression used as a parameter to a gate.
///
/// Finite integer, decimal, and scientific literals are normalized exactly:
/// `0.1`, `0.100`, and `1e-1` all become `Rational(1/10)`. For example,
/// `-theta / 2 + pi/4` retains its symbolic structure while both numeric
/// operands are exact rationals.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NumericExpr {
    Rational(BigRational),
    Constant(NumericConstant),
    Input(SymbolId),
    Neg(Box<NumericExpr>),
    Add(Box<NumericExpr>, Box<NumericExpr>),
    Sub(Box<NumericExpr>, Box<NumericExpr>),
    Mul(Box<NumericExpr>, Box<NumericExpr>),
    Div(Box<NumericExpr>, Box<NumericExpr>),
}

impl fmt::Display for NumericExpr {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Rational(value) => write!(formatter, "{value}"),
            Self::Constant(NumericConstant::Pi) => formatter.write_str("π"),
            Self::Constant(NumericConstant::Tau) => formatter.write_str("τ"),
            Self::Constant(NumericConstant::Euler) => formatter.write_str("ℇ"),
            Self::Input(id) => write!(formatter, "input{}", id.0),
            Self::Neg(value) => write!(formatter, "-({value})"),
            Self::Add(left, right) => write!(formatter, "({left} + {right})"),
            Self::Sub(left, right) => write!(formatter, "({left} - {right})"),
            Self::Mul(left, right) => write!(formatter, "({left} * {right})"),
            Self::Div(left, right) => write!(formatter, "({left} / {right})"),
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClassicalExpr {
    Bool(bool),
    Bit(ClassicalBit),
    Not(Box<ClassicalExpr>),
    Eq(Box<ClassicalExpr>, Box<ClassicalExpr>),
    And(Box<ClassicalExpr>, Box<ClassicalExpr>),
    Or(Box<ClassicalExpr>, Box<ClassicalExpr>),
    Xor(Box<ClassicalExpr>, Box<ClassicalExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Block {
    pub classical_registers: Vec<Register>,
    pub statements: Vec<Statement>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Statement {
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
    If {
        condition: ClassicalExpr,
        then_branch: Block,
        else_branch: Block,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub version: OpenQasmVersion,
    pub numeric_inputs: Vec<NumericInput>,
    pub quantum_registers: Vec<Register>,
    pub classical_registers: Vec<Register>,
    pub body: Block,
}

impl Program {
    pub fn operation_count(&self) -> usize {
        fn count(block: &Block) -> usize {
            block
                .statements
                .iter()
                .map(|statement| match statement {
                    Statement::If {
                        then_branch,
                        else_branch,
                        ..
                    } => 1 + count(then_branch) + count(else_branch),
                    _ => 1,
                })
                .sum()
        }

        count(&self.body)
    }
}
