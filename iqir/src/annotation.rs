//! Specification syntax, separate from executable IR expressions.
//!
//! Pest parses syntax; name resolution and classical checking belong to consumers.
//! Parsing does not prove predicates or mathematical domains (e.g. factorial requires a
//! nonnegative integer). Numbers are exact mathematical rationals, not
//! finite-width program arithmetic. Quantum operators remain reserved.

use num_rational::BigRational;

use crate::{NumericConstant, SymbolId};

mod parser;
pub use parser::{AnnotationParseError, parse_annotation, parse_expression, parse_function};

/// Classical specification types. These use mathematical arithmetic, not
/// machine-width wrapping/rounding. Uint carries a nonnegative domain obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpecType {
    Bool,
    Bit,
    Int,
    Uint,
    Float,
    Angle,
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
    Bool(bool),
    Constant(NumericConstant),
    Infinity,
    /// Only returned by standalone parsing. OpenQASM import resolves all names.
    Name(String),
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
