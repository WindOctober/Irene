//! Specification syntax, separate from executable IR expressions.
//!
//! Pest parses syntax; checking resolves symbols/helpers, sorts and dimensions.
//! Neither proves predicates or mathematical domains (e.g. factorial requires a
//! nonnegative integer). Numbers are exact mathematical rationals, not
//! finite-width program arithmetic. Quantum terms include symbolic linear algebra
//! and program quantum references in state predicates; checking does not extract
//! a circuit state or prove purity.

use num_rational::BigRational;

use crate::{NumericConstant, SymbolId};

const MAX_QUANTUM_QUBITS: usize = 64;

mod functions;
mod parser;
pub use functions::{FunctionError, check_expression, define_function, instantiate_function};
pub use parser::{AnnotationParseError, parse_annotation, parse_expression, parse_function};

/// Mathematical specification types and program quantum-reference types.
/// Specification arithmetic has no machine-width wrapping/rounding.
/// Uint carries a nonnegative domain obligation. Quantum dimensions are qubit
/// counts, not vector lengths; no exponentially sized matrix is allocated.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecType {
    Bool,
    Bit,
    Int,
    Uint,
    Float,
    Angle,
    Complex,
    Ket(usize),
    Bra(usize),
    Operator(usize),
    /// A program qubit reference, not an assumption that its state is pure.
    Qubit,
    /// A program quantum register; unlike a scalar qubit, it can be indexed.
    QubitRegister(usize),
}

/// Normalized one-qubit states in the computational, X and Y bases.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QubitState {
    Zero,
    One,
    /// (|0> + |1>) / \sqrt(2).
    Plus,
    /// (|0> - |1>) / \sqrt(2).
    Minus,
    /// (|0> + i |1>) / \sqrt(2).
    PlusI,
    /// (|0> - i |1>) / \sqrt(2).
    MinusI,
}

/// One-qubit matrices in the ordered basis |0>, |1>.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Pauli {
    I,
    X,
    /// [[0, -i], [i, 0]].
    Y,
    Z,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct FunctionId(pub usize);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Parameter {
    pub name: String,
    pub ty: SpecType,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SpecFunction {
    pub name: String,
    pub parameters: Vec<Parameter>,
    pub result: SpecType,
    pub body: SpecExpr,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinderKind {
    Sum,
    Product,
    Forall,
    Exists,
    Sup,
    Inf,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnnotationKind {
    Requires,
    Ensures,
    Invariant,
    Terminates,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TerminationKind {
    AlmostSure,
}

/// Termination is a property tag, not a variable or a numeric expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnnotationPayload {
    Expression(SpecExpr),
    Termination(TerminationKind),
}

/// UTF-8 byte offsets into the original source, with an exclusive end.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceSpan {
    pub source: String,
    pub start: usize,
    pub end: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Annotation {
    pub kind: AnnotationKind,
    pub payload: AnnotationPayload,
    pub span: SourceSpan,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnaryOp {
    Neg,
    Not,
    Factorial,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Add,
    Sub,
    Mul,
    Tensor,
    Div,
    Mod,
    Pow,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Implies,
}

/// Closed initial vocabulary: unknown functions are errors, not opaque strings.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MathFunction {
    Abs,
    Sqrt,
    Exp,
    Log,
    Sin,
    Cos,
    Tan,
    Sinh,
    Cosh,
    Tanh,
    Asin,
    Acos,
    Atan,
    Floor,
    Ceil,
    Binomial,
    Expectation,
    Min,
    Max,
    Conjugate,
    RealPart,
    ImagPart,
    Adjoint,
    Diag,
    Trace,
    Normalize,
    /// Ensemble reduced density operator at the annotated boundary.
    AvgDensity,
    /// One half of the trace norm of the difference of density operators.
    TraceDistance,
    Probability,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SpecExpr {
    Number(BigRational),
    ImaginaryUnit,
    /// Product-state factors in written tensor order, leftmost first.
    Ket(Vec<QubitState>),
    /// The conjugate transpose of the corresponding ket literal.
    Bra(Vec<QubitState>),
    Pauli(Pauli),
    Bool(bool),
    Constant(NumericConstant),
    Infinity,
    /// Only returned by standalone parsing. OpenQASM import resolves all names.
    Name(String),
    /// A classical or quantum program reference, preserving its declaration ID.
    /// Quantum references are not converted into mathematical ket literals.
    Symbol {
        id: SymbolId,
        name: String,
    },
    /// Parameter position in the owning helper function (never a program ID).
    Parameter(usize),
    /// Lexically scoped sum/quantifier variable. Kept distinct from parameters.
    BoundVariable(u32),
    /// Unresolved helper call, resolved and arity/type checked before import ends.
    NamedCall {
        name: String,
        arguments: Vec<Self>,
    },
    HelperCall {
        function: FunctionId,
        arguments: Vec<Self>,
    },
    Conditional {
        condition: Box<Self>,
        then_value: Box<Self>,
        else_value: Box<Self>,
    },
    Binder {
        kind: BinderKind,
        variable: Parameter,
        /// Assigned by checking. None only in the standalone parser output.
        id: Option<u32>,
        lower: Box<Self>,
        upper: Box<Self>,
        inclusive: bool,
        body: Box<Self>,
    },
    Unary {
        op: UnaryOp,
        operand: Box<Self>,
    },
    Binary {
        op: BinaryOp,
        left: Box<Self>,
        right: Box<Self>,
    },
    Call {
        function: MathFunction,
        arguments: Vec<Self>,
    },
    Index {
        value: Box<Self>,
        index: Box<Self>,
    },
    /// Vector or nested matrix literal.
    List(Vec<Self>),
}
