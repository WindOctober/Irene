//! Validation and interface normalization for equivalence checking.
//!
//! Program-local symbol IDs are deliberately absent from the semantic order of
//! inputs and outputs below.  A vector position is the public, canonical name
//! of a pair; local endpoints are retained only as lookup metadata.

use std::collections::{BTreeMap, BTreeSet};

use thiserror::Error;

use crate::ir::{Block, ClassicalBit, NumericType, Program, Qubit, StatementKind, SymbolId};
use crate::symbolic::{
    BooleanPolynomial, ExecutionConfig, HybridPathSum, OutputSelection, SymbolicError, Variable,
    execute,
};

/// One program endpoint.  Quantum/classical output pairs may be mixed; mixed
/// pairs are compared after a terminal computational-basis (Z) observation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Endpoint {
    Quantum(Qubit),
    Classical(ClassicalBit),
}

/// A pair of external quantum inputs.
///
/// This uses [`Endpoint`] so deserializers can report a typed error for an
/// accidentally supplied classical cell instead of silently reinterpreting it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InputPair {
    pub left: Endpoint,
    pub right: Endpoint,
}

impl InputPair {
    pub fn quantum(left: Qubit, right: Qubit) -> Self {
        Self {
            left: Endpoint::Quantum(left),
            right: Endpoint::Quantum(right),
        }
    }
}

/// A pair of source-level numeric parameters with the same declared type.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct NumericInputPair {
    pub left: SymbolId,
    pub right: SymbolId,
}

/// One pair of observable outputs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutputPair {
    pub left: Endpoint,
    pub right: Endpoint,
}

/// Complete interface description for comparing two programs.
///
/// Every paired quantum input is an arbitrary symbolic basis input and every
/// unpaired qubit starts in `|0>`. Numeric input pairing is validated for
/// specific interface errors before source-language numeric inputs are
/// rejected as unsupported. OpenQASM numeric
/// expressions have target-width rounding, wrapping, range, and division
/// semantics even when a declaration omits its width; Irene's exact symbolic
/// expression domain does not model those rules.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct EquivalenceConfig {
    pub input_pairs: Vec<InputPair>,
    pub numeric_input_pairs: Vec<NumericInputPair>,
    pub output_pairs: Vec<OutputPair>,
}

impl EquivalenceConfig {
    /// Pairs all top-level quantum and classical cells in declaration order.
    ///
    /// Every quantum input is arbitrary and every storage cell is observed.
    /// Returns None for incompatible storage counts or numeric parameter types;
    /// callers with different interfaces must specify the pairs explicitly.
    /// This only constructs the interface; analyze validates and executes it.
    pub fn positional(left: &Program, right: &Program) -> Option<Self> {
        fn bits(program: &Program) -> Vec<ClassicalBit> {
            program
                .classical_registers
                .iter()
                .flat_map(|register| {
                    (0..register.width).map(|index| ClassicalBit {
                        register: register.id,
                        index,
                    })
                })
                .collect()
        }

        let left_qubits = super::qubits(left);
        let right_qubits = super::qubits(right);
        let left_bits = bits(left);
        let right_bits = bits(right);
        if left_qubits.len() != right_qubits.len() || left_bits.len() != right_bits.len() {
            return None;
        }
        if left.numeric_inputs.len() != right.numeric_inputs.len()
            || left
                .numeric_inputs
                .iter()
                .zip(&right.numeric_inputs)
                .any(|(left, right)| left.ty != right.ty)
        {
            return None;
        }
        Some(EquivalenceConfig {
            input_pairs: left_qubits
                .iter()
                .cloned()
                .zip(right_qubits.iter().cloned())
                .map(|(left, right)| InputPair::quantum(left, right))
                .collect(),
            numeric_input_pairs: left
                .numeric_inputs
                .iter()
                .zip(&right.numeric_inputs)
                .map(|(left, right)| NumericInputPair {
                    left: left.id,
                    right: right.id,
                })
                .collect(),
            output_pairs: left_qubits
                .into_iter()
                .map(Endpoint::Quantum)
                .zip(right_qubits.into_iter().map(Endpoint::Quantum))
                .chain(
                    left_bits
                        .into_iter()
                        .map(Endpoint::Classical)
                        .zip(right_bits.into_iter().map(Endpoint::Classical)),
                )
                .map(|(left, right)| OutputPair { left, right })
                .collect(),
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Side {
    Left,
    Right,
}

impl std::fmt::Display for Side {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter.write_str(match self {
            Self::Left => "left",
            Self::Right => "right",
        })
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum UnsupportedInterface {
    #[error("{side} numeric input {input:?} is not explicitly paired")]
    UnpairedNumericInput { side: Side, input: SymbolId },
    #[error(
        "{side} numeric input {input:?} has type {ty:?}, whose source-language numeric semantics are not modeled"
    )]
    NumericInputSemanticsUnsupported {
        side: Side,
        input: SymbolId,
        ty: NumericType,
    },
    #[error("no collision-free canonical symbol ID is available")]
    CanonicalSymbolSpaceExhausted,
}

/// Configuration/execution errors are proof outcomes of neither equivalence nor
/// inequivalence.  In particular, [`InterfaceError::Unsupported`] must be
/// surfaced as `Unknown` by the verdict layer.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum InterfaceError {
    #[error("invalid equivalence configuration: {0}")]
    InvalidConfiguration(String),
    #[error(transparent)]
    SolverDisagreement(#[from] super::smt::SolverDisagreement),
    #[error(
        "input pair {position} must contain two quantum endpoints, found {left:?} and {right:?}"
    )]
    KindMismatchedInput {
        position: usize,
        left: Endpoint,
        right: Endpoint,
    },
    #[error("duplicate {side} input endpoint {endpoint:?}")]
    DuplicateInputEndpoint { side: Side, endpoint: Endpoint },
    #[error("unknown {side} quantum input {qubit:?}")]
    UnknownQuantumInput { side: Side, qubit: Qubit },
    #[error("duplicate {side} numeric input {input:?}")]
    DuplicateNumericInput { side: Side, input: SymbolId },
    #[error("unknown {side} numeric input {input:?}")]
    UnknownNumericInput { side: Side, input: SymbolId },
    #[error("numeric input pair {position} has incompatible types {left:?} and {right:?}")]
    NumericTypeMismatch {
        position: usize,
        left: NumericType,
        right: NumericType,
    },
    #[error("duplicate {side} output endpoint {endpoint:?}")]
    DuplicateOutputEndpoint { side: Side, endpoint: Endpoint },
    #[error("unknown {side} output endpoint {endpoint:?}")]
    UnknownOutputEndpoint { side: Side, endpoint: Endpoint },
    #[error("symbolic execution failed on the {side}: {source}")]
    Execution {
        side: Side,
        #[source]
        source: SymbolicError,
    },
    #[error("the {side} executor omitted output pair {position} ({endpoint:?})")]
    MissingTerminalOutput {
        side: Side,
        position: usize,
        endpoint: Endpoint,
    },
    #[error(transparent)]
    Unsupported(#[from] UnsupportedInterface),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PreparedOutputKind {
    Quantum,
    Classical,
}

/// One component's output at a canonical output-pair position.
///
/// A density-kernel consumer must impose `ket(value) = bra(value)` for every
/// `Classical` value.  This is what makes a mixed Q/C endpoint a measurement,
/// rather than an unsound renaming of a coherent quantum wire.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedOutput {
    pub kind: PreparedOutputKind,
    pub value: BooleanPolynomial,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedTerminal {
    /// Indexed by output-pair position, independent of local endpoint IDs.
    pub outputs: Vec<PreparedOutput>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedSide {
    pub hps: HybridPathSum,
    /// Kept in lockstep with `hps.components`.
    pub terminals: Vec<PreparedTerminal>,
    /// Local lookup keys mapped to shared quantum-input pair positions.
    pub quantum_input_positions: BTreeMap<Qubit, usize>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PreparedComparison {
    pub left: PreparedSide,
    pub right: PreparedSide,
    /// Common kind at every output-pair position.  A mixed Q/C pair is
    /// classical because the quantum side receives a terminal Z observation.
    pub output_kinds: Vec<PreparedOutputKind>,
}

type ValidatedOutputs = (Vec<Endpoint>, Vec<Endpoint>, Vec<PreparedOutputKind>);

/// Validates, executes, and lowers two interfaces to canonical pair positions.
pub fn prepare_comparison(
    left: &Program,
    right: &Program,
    config: &EquivalenceConfig,
) -> Result<PreparedComparison, InterfaceError> {
    let left_qubits = declared_qubits(left);
    let right_qubits = declared_qubits(right);
    let (left_inputs, right_inputs) = validate_quantum_inputs(config, &left_qubits, &right_qubits)?;

    let (left_outputs, right_outputs, output_kinds) = validate_outputs(left, right, config)?;
    validate_numeric_inputs(left, right, config)?;

    let first_canonical = maximum_symbol(left)
        .into_iter()
        .chain(maximum_symbol(right))
        .max()
        .map_or(Some(0), |value| value.checked_add(1))
        .ok_or(UnsupportedInterface::CanonicalSymbolSpaceExhausted)?;
    let canonical_quantum_register = SymbolId(first_canonical);

    let left_side = prepare_side(
        Side::Left,
        left,
        left_inputs,
        &left_outputs,
        &output_kinds,
        canonical_quantum_register,
    )?;
    let right_side = prepare_side(
        Side::Right,
        right,
        right_inputs,
        &right_outputs,
        &output_kinds,
        canonical_quantum_register,
    )?;
    Ok(PreparedComparison {
        left: left_side,
        right: right_side,
        output_kinds,
    })
}

fn validate_quantum_inputs(
    config: &EquivalenceConfig,
    left_declared: &BTreeSet<Qubit>,
    right_declared: &BTreeSet<Qubit>,
) -> Result<(Vec<Qubit>, Vec<Qubit>), InterfaceError> {
    let mut left_seen = BTreeSet::new();
    let mut right_seen = BTreeSet::new();
    let mut left = Vec::new();
    let mut right = Vec::new();
    for (position, pair) in config.input_pairs.iter().enumerate() {
        let (Endpoint::Quantum(left_qubit), Endpoint::Quantum(right_qubit)) =
            (&pair.left, &pair.right)
        else {
            return Err(InterfaceError::KindMismatchedInput {
                position,
                left: pair.left.clone(),
                right: pair.right.clone(),
            });
        };
        validate_quantum_input(Side::Left, left_qubit, left_declared, &mut left_seen)?;
        validate_quantum_input(Side::Right, right_qubit, right_declared, &mut right_seen)?;
        left.push(left_qubit.clone());
        right.push(right_qubit.clone());
    }
    Ok((left, right))
}

fn validate_quantum_input(
    side: Side,
    qubit: &Qubit,
    declared: &BTreeSet<Qubit>,
    seen: &mut BTreeSet<Qubit>,
) -> Result<(), InterfaceError> {
    if !seen.insert(qubit.clone()) {
        return Err(InterfaceError::DuplicateInputEndpoint {
            side,
            endpoint: Endpoint::Quantum(qubit.clone()),
        });
    }
    if !declared.contains(qubit) {
        return Err(InterfaceError::UnknownQuantumInput {
            side,
            qubit: qubit.clone(),
        });
    }
    Ok(())
}

fn validate_numeric_inputs(
    left: &Program,
    right: &Program,
    config: &EquivalenceConfig,
) -> Result<(), InterfaceError> {
    let left_declared = left
        .numeric_inputs
        .iter()
        .map(|input| (input.id, input.ty))
        .collect::<BTreeMap<_, _>>();
    let right_declared = right
        .numeric_inputs
        .iter()
        .map(|input| (input.id, input.ty))
        .collect::<BTreeMap<_, _>>();
    let mut left_positions = BTreeMap::new();
    let mut right_positions = BTreeMap::new();
    for (position, pair) in config.numeric_input_pairs.iter().enumerate() {
        let left_ty =
            *left_declared
                .get(&pair.left)
                .ok_or(InterfaceError::UnknownNumericInput {
                    side: Side::Left,
                    input: pair.left,
                })?;
        let right_ty =
            *right_declared
                .get(&pair.right)
                .ok_or(InterfaceError::UnknownNumericInput {
                    side: Side::Right,
                    input: pair.right,
                })?;
        if left_positions.insert(pair.left, position).is_some() {
            return Err(InterfaceError::DuplicateNumericInput {
                side: Side::Left,
                input: pair.left,
            });
        }
        if right_positions.insert(pair.right, position).is_some() {
            return Err(InterfaceError::DuplicateNumericInput {
                side: Side::Right,
                input: pair.right,
            });
        }
        if left_ty != right_ty {
            return Err(InterfaceError::NumericTypeMismatch {
                position,
                left: left_ty,
                right: right_ty,
            });
        }
    }
    if let Some(input) = left_declared
        .keys()
        .find(|input| !left_positions.contains_key(input))
    {
        return Err(UnsupportedInterface::UnpairedNumericInput {
            side: Side::Left,
            input: *input,
        }
        .into());
    }
    if let Some(input) = right_declared
        .keys()
        .find(|input| !right_positions.contains_key(input))
    {
        return Err(UnsupportedInterface::UnpairedNumericInput {
            side: Side::Right,
            input: *input,
        }
        .into());
    }

    // Numeric expressions model free inputs as exact symbolic values. Rekeying
    // an OpenQASM numeric input into that domain would erase source-level
    // rounding (float/angle), wrapping/range and division (int/uint). An
    // omitted width selects a target-defined width; it does not denote an
    // unbounded mathematical value. Do this check only after pairing
    // validation so malformed interfaces retain their more specific errors.
    reject_numeric_inputs(Side::Left, left)?;
    reject_numeric_inputs(Side::Right, right)?;

    Ok(())
}

fn reject_numeric_inputs(side: Side, program: &Program) -> Result<(), InterfaceError> {
    if let Some(input) = program.numeric_inputs.first() {
        return Err(UnsupportedInterface::NumericInputSemanticsUnsupported {
            side,
            input: input.id,
            ty: input.ty,
        }
        .into());
    }
    Ok(())
}

fn validate_outputs(
    left: &Program,
    right: &Program,
    config: &EquivalenceConfig,
) -> Result<ValidatedOutputs, InterfaceError> {
    let left_qubits = declared_qubits(left);
    let right_qubits = declared_qubits(right);
    let left_bits = declared_classical_bits(left);
    let right_bits = declared_classical_bits(right);
    let mut left_seen = BTreeSet::new();
    let mut right_seen = BTreeSet::new();
    let mut left_outputs = Vec::new();
    let mut right_outputs = Vec::new();
    let mut kinds = Vec::new();
    for pair in &config.output_pairs {
        validate_output(
            Side::Left,
            &pair.left,
            &left_qubits,
            &left_bits,
            &mut left_seen,
        )?;
        validate_output(
            Side::Right,
            &pair.right,
            &right_qubits,
            &right_bits,
            &mut right_seen,
        )?;
        kinds.push(
            if matches!(&pair.left, Endpoint::Quantum(_))
                && matches!(&pair.right, Endpoint::Quantum(_))
            {
                PreparedOutputKind::Quantum
            } else {
                PreparedOutputKind::Classical
            },
        );
        left_outputs.push(pair.left.clone());
        right_outputs.push(pair.right.clone());
    }
    Ok((left_outputs, right_outputs, kinds))
}

fn validate_output(
    side: Side,
    endpoint: &Endpoint,
    qubits: &BTreeSet<Qubit>,
    bits: &BTreeSet<ClassicalBit>,
    seen: &mut BTreeSet<Endpoint>,
) -> Result<(), InterfaceError> {
    if !seen.insert(endpoint.clone()) {
        return Err(InterfaceError::DuplicateOutputEndpoint {
            side,
            endpoint: endpoint.clone(),
        });
    }
    let declared = match endpoint {
        Endpoint::Quantum(qubit) => qubits.contains(qubit),
        Endpoint::Classical(bit) => bits.contains(bit),
    };
    if !declared {
        return Err(InterfaceError::UnknownOutputEndpoint {
            side,
            endpoint: endpoint.clone(),
        });
    }
    Ok(())
}

fn prepare_side(
    side: Side,
    program: &Program,
    inputs: Vec<Qubit>,
    outputs: &[Endpoint],
    output_kinds: &[PreparedOutputKind],
    canonical_register: SymbolId,
) -> Result<PreparedSide, InterfaceError> {
    let debug = std::env::var_os("IRENE_DEBUG_AGGREGATE").is_some();
    if debug {
        eprintln!("prepare {side:?}: execution start");
    }
    let quantum_input_positions = inputs
        .iter()
        .cloned()
        .enumerate()
        .map(|(position, qubit)| (qubit, position))
        .collect::<BTreeMap<_, _>>();
    let selection = OutputSelection::new(
        outputs.iter().filter_map(|endpoint| match endpoint {
            Endpoint::Quantum(qubit) => Some(qubit.clone()),
            Endpoint::Classical(_) => None,
        }),
        outputs.iter().filter_map(|endpoint| match endpoint {
            Endpoint::Classical(bit) => Some(bit.clone()),
            Endpoint::Quantum(_) => None,
        }),
    );
    let mut hps = execute(
        program,
        &ExecutionConfig::with_symbolic_inputs(inputs.clone()),
        &selection,
    )
    .map_err(|source| InterfaceError::Execution { side, source })?;
    if debug {
        eprintln!("prepare {side:?}: input canonicalization start");
    }

    canonicalize_boolean_inputs(&mut hps, &inputs, canonical_register);
    if debug {
        eprintln!("prepare {side:?}: input canonicalization finished");
    }
    hps.input.quantum = (0..inputs.len())
        .map(|position| {
            let qubit = Qubit {
                register: canonical_register,
                index: position,
            };
            (
                qubit.clone(),
                BooleanPolynomial::variable(Variable::Input(qubit)),
            )
        })
        .collect();

    // TODO: Remove the redundant output extraction/reinsertion design. Keep
    // visible output expressions in the HPS and store only endpoint mappings
    // and observation kinds in the interface layer. Update snapshot/kernel
    // consumers together, preserving terminal Z-observation semantics; until
    // then, `hps` and `terminals` must be treated as one complete result.
    let mut terminals = Vec::with_capacity(hps.components.len());
    for component in &mut hps.components {
        let mut prepared = Vec::with_capacity(outputs.len());
        for (position, (endpoint, kind)) in outputs.iter().zip(output_kinds).enumerate() {
            let value = match endpoint {
                Endpoint::Quantum(qubit) => component.output.quantum.remove(qubit),
                Endpoint::Classical(bit) => component.output.classical.remove(bit),
            }
            .ok_or_else(|| InterfaceError::MissingTerminalOutput {
                side,
                position,
                endpoint: endpoint.clone(),
            })?;
            prepared.push(PreparedOutput { kind: *kind, value });
        }
        terminals.push(PreparedTerminal { outputs: prepared });
    }
    Ok(PreparedSide {
        hps,
        terminals,
        quantum_input_positions,
    })
}

fn canonicalize_boolean_inputs(
    hps: &mut HybridPathSum,
    inputs: &[Qubit],
    canonical_register: SymbolId,
) {
    for (position, source) in inputs.iter().enumerate() {
        let source = Variable::Input(source.clone());
        let target_qubit = Qubit {
            register: canonical_register,
            index: position,
        };
        let target = BooleanPolynomial::variable(Variable::Input(target_qubit));
        for value in hps.input.quantum.values_mut() {
            *value = value.substitute(&source, &target);
        }
        for component in &mut hps.components {
            for guard in &mut component.guard {
                *guard = guard.substitute(&source, &target);
            }
            component.scalar = component.scalar.substitute(&source, &target);
            component.phase.substitute(&source, &target);
            for value in component.output.quantum.values_mut() {
                *value = value.substitute(&source, &target);
            }
            for value in component.output.classical.values_mut() {
                *value = value.substitute(&source, &target);
            }
            for entry in &mut component.output.history {
                let value = entry.value_mut();
                *value = value.substitute(&source, &target);
            }
        }
    }
    // History targets are program storage names, not observable labels.  Once
    // execution is complete, only each recorded value/equality matters to the
    // density kernel, so number writes by occurrence as well.
    for component in &mut hps.components {
        for (position, entry) in component.output.history.iter_mut().enumerate() {
            if let crate::symbolic::HistoryEntry::Write { target, .. } = entry {
                *target = ClassicalBit {
                    register: canonical_register,
                    index: position,
                };
            }
        }
    }
}

fn declared_qubits(program: &Program) -> BTreeSet<Qubit> {
    program
        .quantum_registers
        .iter()
        .flat_map(|register| {
            (0..register.width).map(|index| Qubit {
                register: register.id,
                index,
            })
        })
        .collect()
}

fn declared_classical_bits(program: &Program) -> BTreeSet<ClassicalBit> {
    program
        .classical_registers
        .iter()
        .flat_map(|register| {
            (0..register.width).map(|index| ClassicalBit {
                register: register.id,
                index,
            })
        })
        .collect()
}

fn maximum_symbol(program: &Program) -> Option<usize> {
    fn visit_block(block: &Block, maximum: &mut Option<usize>) {
        for register in &block.classical_registers {
            *maximum = Some(maximum.map_or(register.id.0, |old| old.max(register.id.0)));
        }
        for statement in &block.statements {
            match &statement.kind {
                StatementKind::If {
                    then_branch,
                    else_branch,
                    ..
                } => {
                    visit_block(then_branch, maximum);
                    visit_block(else_branch, maximum);
                }
                StatementKind::Scope(body) => visit_block(body, maximum),
                _ => {}
            }
        }
    }
    let mut maximum = program
        .numeric_inputs
        .iter()
        .map(|input| input.id.0)
        .chain(
            program
                .quantum_registers
                .iter()
                .map(|register| register.id.0),
        )
        .chain(
            program
                .classical_registers
                .iter()
                .map(|register| register.id.0),
        )
        .max();
    visit_block(&program.body, &mut maximum);
    maximum
}

#[cfg(test)]
#[path = "../../tests/unit/equivalence/interface/tests.rs"]
mod tests;
