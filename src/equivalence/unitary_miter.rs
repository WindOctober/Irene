//! Explicit full-unitary comparison by ordinary forward execution of a miter.
//!
//! This is NOT a transformation for partial outputs, initialized ancillas, or
//! general channels. All declared qubits are arbitrary inputs and observed
//! quantum outputs, paired in declaration/cell order. Unused classical storage
//! and constant writes (including QASM 2 creg initialization) are omitted;
//! classical reads/control, measurement, and reset are rejected.
//!
//! TODO: Preserve source-library phase conventions during frontend lowering
//! before extending this channel-oriented miter to phase-sensitive operator
//! equality or coherent control of the whole generated circuit. QASM 2's
//! reference qelib1 defines rz(a) = u1(a) = P(a) = exp(i*a/2) Rz(a),
//! whereas the shared IR and QASM 3 stdgates use textbook Rz. Adjoining
//! the IR cannot recover a source global phase already omitted by lowering.
//! For rx/ry, QASM 3's gphase(-a/2) compensates its built-in U convention:
//! the resulting standard gates ARE textbook Rx/Ry; do not add it again.
//! Track any source phase explicitly and conjugate it when taking the inverse;
//! it is ignorable only for full-channel comparison, not under quantum control.
//! References: <https://openqasm.com/language/gates.html#built-in-gates>
//! <https://github.com/openqasm/openqasm/blob/OpenQASM2.x/examples/qelib1.inc>

use std::collections::{BTreeMap, BTreeSet};

use crate::ir::{
    AstIdGenerator, Block, BlockData, ClassicalExprKind, Gate, NumericExpr, NumericExprKind,
    OpenQasmVersion, Program, ProgramData, Qubit, RegisterData, Statement, StatementKind, SymbolId,
    gate_shape,
};

#[derive(Debug, thiserror::Error)]
pub enum UnitaryMiterError {
    #[error("unitary miter does not support this statement kind")]
    UnsupportedStatement,
    #[error("unitary miter requires equal full quantum interface widths")]
    InterfaceWidth,
    #[error("unitary miter does not support runtime numeric inputs")]
    NumericInput,
    #[error(
        "unitary miter requires quantum gate-only programs (scopes and unused constant classical writes are allowed)"
    )]
    NonUnitary,
    #[error("invalid quantum declarations or gate operands")]
    InvalidOperands,
}

/// Structural full-unitary admission, without building a miter or executing HPS.
/// Numeric domains must still be checked before rewriting or execution.
/// Specification annotations and helpers do not affect admission.
pub fn validate(source: &Program) -> Result<(), UnitaryMiterError> {
    let wires = wire_map(source)?;
    let mut blocks = vec![&source.body];
    while let Some(block) = blocks.pop() {
        for s in &block.statements {
            match &s.kind {
                StatementKind::While { .. }
                | StatementKind::ScalarDeclare { .. }
                | StatementKind::ScalarAssign { .. }
                | StatementKind::GlobalPhase(_)
                | StatementKind::Unitary { .. } => {
                    return Err(UnitaryMiterError::UnsupportedStatement);
                }
                StatementKind::Scope(b) => blocks.push(b),
                StatementKind::Assign { value, .. }
                    if matches!(value.kind, ClassicalExprKind::Bool(_)) => {}
                StatementKind::Apply {
                    gate,
                    parameters,
                    qubits,
                } => {
                    let (n, p) = gate_shape(*gate);
                    if qubits.len() != n
                        || parameters.len() != p
                        || qubits.iter().collect::<BTreeSet<_>>().len() != n
                        || qubits.iter().any(|q| !wires.contains_key(q))
                    {
                        return Err(UnitaryMiterError::InvalidOperands);
                    }
                    let mut pending = parameters.iter().collect::<Vec<_>>();
                    while let Some(e) = pending.pop() {
                        match &e.kind {
                            NumericExprKind::Input(_) => {
                                return Err(UnitaryMiterError::NumericInput);
                            }
                            NumericExprKind::Neg(a) => pending.push(a),
                            NumericExprKind::Add(a, b)
                            | NumericExprKind::Sub(a, b)
                            | NumericExprKind::Mul(a, b)
                            | NumericExprKind::Div(a, b) => {
                                pending.extend([a.as_ref(), b.as_ref()])
                            }
                            _ => {}
                        }
                    }
                }
                _ => return Err(UnitaryMiterError::NonUnitary),
            }
        }
    }
    Ok(())
}

/// Returns `(forward; inverse(adjoint_of), identity)` for a full quantum
/// interface. Both returned programs have fresh AST identities and one common
/// positional wire layout. Checking their *channels* preserves exactly the
/// original full-unitary equality up to an input-independent global phase.
///
/// Both source programs must be unitary, not merely the side being inverted.
/// No internal HPS paths are matched, and no source programs are modified.
/// The generated programs contain executable operations only: source annotations
/// and specification helpers are neither copied nor used as proof assumptions.
/// Inversion/composition does not preserve their source statement boundaries.
pub fn miter(
    forward: &Program,
    adjoint_of: &Program,
) -> Result<(Program, Program), UnitaryMiterError> {
    let forward_wires = wire_map(forward)?;
    let inverse_wires = wire_map(adjoint_of)?;
    if forward_wires.len() != inverse_wires.len() {
        return Err(UnitaryMiterError::InterfaceWidth);
    }
    let mut ids = AstIdGenerator::default();
    let mut statements = Vec::new();
    append_block(
        &forward.body,
        &forward_wires,
        false,
        &mut ids,
        &mut statements,
    )?;
    append_block(
        &adjoint_of.body,
        &inverse_wires,
        true,
        &mut ids,
        &mut statements,
    )?;
    let circuit = program(forward_wires.len(), statements, &mut ids);
    let identity = program(forward_wires.len(), Vec::new(), &mut ids);
    Ok((circuit, identity))
}

fn program(width: usize, statements: Vec<Statement>, ids: &mut AstIdGenerator) -> Program {
    let register = ids.node(RegisterData {
        id: SymbolId(0),
        name: "q".into(),
        width,
    });
    let body = ids.node(BlockData {
        classical_registers: Vec::new(),
        statements,
    });
    ids.node(ProgramData {
        annotations: Default::default(),
        spec_functions: Vec::new(),
        version: OpenQasmVersion { major: 3, minor: 0 },
        numeric_inputs: Vec::new(),
        quantum_registers: vec![register],
        classical_registers: Vec::new(),
        body,
    })
}

fn wire_map(program: &Program) -> Result<BTreeMap<Qubit, Qubit>, UnitaryMiterError> {
    if !program.numeric_inputs.is_empty() {
        return Err(UnitaryMiterError::NumericInput);
    }
    let mut wires = BTreeMap::new();
    let mut registers = BTreeSet::new();
    for register in &program.quantum_registers {
        if !registers.insert(register.id) {
            return Err(UnitaryMiterError::InvalidOperands);
        }
        for index in 0..register.width {
            let target = Qubit {
                register: SymbolId(0),
                index: wires.len(),
            };
            wires.insert(
                Qubit {
                    register: register.id,
                    index,
                },
                target,
            );
        }
    }
    Ok(wires)
}

fn append_block(
    block: &Block,
    wires: &BTreeMap<Qubit, Qubit>,
    inverse: bool,
    ids: &mut AstIdGenerator,
    out: &mut Vec<Statement>,
) -> Result<(), UnitaryMiterError> {
    for offset in 0..block.statements.len() {
        let index = if inverse {
            block.statements.len() - 1 - offset
        } else {
            offset
        };
        match &block.statements[index].kind {
            StatementKind::Scope(inner) => append_block(inner, wires, inverse, ids, out)?,
            StatementKind::Apply {
                gate,
                parameters,
                qubits,
            } => {
                let (arity, parameter_count) = gate_shape(*gate);
                if parameters.len() != parameter_count
                    || qubits.len() != arity
                    || qubits.iter().collect::<BTreeSet<_>>().len() != arity
                {
                    return Err(UnitaryMiterError::InvalidOperands);
                }
                let qubits = qubits
                    .iter()
                    .map(|q| {
                        wires
                            .get(q)
                            .cloned()
                            .ok_or(UnitaryMiterError::InvalidOperands)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let parameters = parameters
                    .iter()
                    .map(|parameter| {
                        let expression = copy_numeric(parameter, ids)?;
                        Ok(if inverse {
                            ids.node(NumericExprKind::Neg(Box::new(expression)))
                        } else {
                            expression
                        })
                    })
                    .collect::<Result<Vec<_>, UnitaryMiterError>>()?;
                let gate = if inverse {
                    match gate {
                        Gate::S => Gate::Sdg,
                        Gate::Sdg => Gate::S,
                        Gate::T => Gate::Tdg,
                        Gate::Tdg => Gate::T,
                        // Exhaustive so adding a gate cannot silently assume
                        // it is self-adjoint or inverted by angle negation.
                        Gate::H
                        | Gate::X
                        | Gate::Y
                        | Gate::Z
                        | Gate::Cx
                        | Gate::Cy
                        | Gate::Cz
                        | Gate::Swap
                        | Gate::Ccx
                        | Gate::Ccz
                        | Gate::P
                        | Gate::Rx
                        | Gate::Ry
                        | Gate::Rz
                        | Gate::Cp
                        | Gate::Crx
                        | Gate::Cry
                        | Gate::Crz => *gate,
                    }
                } else {
                    *gate
                };
                out.push(ids.node(StatementKind::Apply {
                    gate,
                    parameters,
                    qubits,
                }));
            }
            // The interface is explicitly quantum-only and no classical reads
            // or control are admitted anywhere. Such writes cannot affect it.
            StatementKind::Assign { value, .. }
                if matches!(value.kind, ClassicalExprKind::Bool(_)) => {}
            StatementKind::While { .. }
            | StatementKind::ScalarDeclare { .. }
            | StatementKind::ScalarAssign { .. }
            | StatementKind::GlobalPhase(_)
            | StatementKind::Unitary { .. } => {
                return Err(UnitaryMiterError::UnsupportedStatement);
            }
            StatementKind::Reset(_)
            | StatementKind::Measure { .. }
            | StatementKind::Assign { .. }
            | StatementKind::If { .. } => {
                return Err(UnitaryMiterError::NonUnitary);
            }
        }
    }
    Ok(())
}

fn copy_numeric(
    expr: &NumericExpr,
    ids: &mut AstIdGenerator,
) -> Result<NumericExpr, UnitaryMiterError> {
    use NumericExprKind::*;
    let kind = match &expr.kind {
        Input(_) => return Err(UnitaryMiterError::NumericInput),
        Rational(value) => Rational(value.clone()),
        Constant(value) => Constant(*value),
        Neg(x) => Neg(Box::new(copy_numeric(x, ids)?)),
        Add(a, b) => Add(
            Box::new(copy_numeric(a, ids)?),
            Box::new(copy_numeric(b, ids)?),
        ),
        Sub(a, b) => Sub(
            Box::new(copy_numeric(a, ids)?),
            Box::new(copy_numeric(b, ids)?),
        ),
        Mul(a, b) => Mul(
            Box::new(copy_numeric(a, ids)?),
            Box::new(copy_numeric(b, ids)?),
        ),
        Div(a, b) => Div(
            Box::new(copy_numeric(a, ids)?),
            Box::new(copy_numeric(b, ids)?),
        ),
    };
    Ok(ids.node(kind))
}
