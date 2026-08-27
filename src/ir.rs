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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SymbolId(pub usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Qubit {
    pub register: SymbolId,
    pub index: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct ClassicalBit {
    pub register: SymbolId,
    pub index: usize,
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
