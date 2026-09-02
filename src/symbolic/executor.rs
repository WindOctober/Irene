use std::collections::{BTreeMap, BTreeSet};

use num_rational::BigRational;
use thiserror::Error;

use crate::ir::{
    Block, ClassicalBit, ClassicalExpr, Gate, NumericExpr, Program, Qubit, Register, Statement,
};

use super::{BooleanPolynomial, PhaseCoefficient, PhasePolynomial, Scalar, Variable};

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum SymbolicError {
    #[error("configured symbolic input is not declared by the program: {0:?}")]
    UnknownInput(Qubit),
    #[error("classical bit is read before it is assigned: {0:?}")]
    UninitializedClassical(ClassicalBit),
}

/// Selects the quantum state from which symbolic execution starts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InitialState {
    /// Treat every declared qubit as an independent symbolic basis input.
    ///
    /// For two qubits this produces the input signature `|x0 x1⟩`. These
    /// variables name basis indices; they are not numerical amplitudes.
    AllSymbolic,
    /// Start every qubit in `|0⟩`, except for the listed symbolic inputs.
    ///
    /// For example, selecting only `q[1]` gives `|0 x1⟩`.
    Zero { symbolic_inputs: BTreeSet<Qubit> },
}

/// Options controlling symbolic execution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExecutionConfig {
    pub initial_state: InitialState,
}

impl ExecutionConfig {
    /// Makes all declared quantum wires free basis variables.
    pub fn all_symbolic() -> Self {
        Self {
            initial_state: InitialState::AllSymbolic,
        }
    }

    /// Configures execution from the all-zero quantum state.
    pub fn zero() -> Self {
        Self::default()
    }

    /// Starts from zero while treating only the given qubits as symbolic inputs.
    pub fn with_symbolic_inputs(inputs: impl IntoIterator<Item = Qubit>) -> Self {
        Self {
            initial_state: InitialState::Zero {
                symbolic_inputs: inputs.into_iter().collect(),
            },
        }
    }
}

impl Default for ExecutionConfig {
    fn default() -> Self {
        Self {
            initial_state: InitialState::Zero {
                symbolic_inputs: BTreeSet::new(),
            },
        }
    }
}

/// One event in the sparse classical-history representation.
///
/// For example, after `H q; measure q -> c`, the history records `Write(c, y0)`.
/// Replacing the measurement with `reset q` records `Discard(y0)` instead.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HistoryEntry {
    /// A measurement result written to a classical bit.
    Write {
        target: ClassicalBit,
        value: BooleanPolynomial,
    },
    /// A result discarded by reset: inaccessible to the program but retained as history.
    Discard { value: BooleanPolynomial },
}

/// Quantum memory, current classical memory, and its complete write history.
///
/// The paper represents classical history as a stack of complete memory
/// snapshots. Irene stores only writes because the initial memory and this
/// event sequence reconstruct the same snapshots. Past entries are semantic:
/// paths with different histories belong to different classical worlds and
/// therefore cannot interfere.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct HybridMemory {
    /// Computational-basis expression carried by each quantum wire.
    pub quantum: BTreeMap<Qubit, BooleanPolynomial>,
    /// Present value of each in-scope classical bit.
    pub classical: BTreeMap<ClassicalBit, BooleanPolynomial>,
    /// Sparse form of the classical-memory stack, including hidden reset outcomes.
    pub history: Vec<HistoryEntry>,
}

/// One HPS summand produced by symbolic control flow.
///
/// Its amplitude is `guard * scalar * exp(2πi phase)`; `output` describes the
/// hybrid-memory signature of the summand.
///
/// For example, branching on a measured path variable `y0` produces a then
/// component guarded by `y0` and an else component guarded by `1 ⊕ y0`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Component {
    /// Boolean filter selecting the paths on which this component is active.
    pub guard: BooleanPolynomial,
    /// Real symbolic amplitude; complex factors are stored in `phase`.
    pub scalar: Scalar,
    /// Path variables summed over when this component is concretized.
    pub path_support: BTreeSet<usize>,
    /// Accumulated exponent in `exp(2πi phase)`.
    pub phase: PhasePolynomial,
    /// Symbolic hybrid memory produced by this component.
    pub output: HybridMemory,
}

/// Symbolic denotation of a hybrid program as a finite sum of HPS components.
///
/// `PartialEq` on this type is structural equality only. Program equivalence
/// must compare the induced density-operator maps after normalization or
/// concretization; distinct HPS syntax can denote the same hybrid state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HybridPathSum {
    /// Input signature shared by every component.
    pub input: HybridMemory,
    /// Summands created by classically controlled execution.
    pub components: Vec<Component>,
}

/// Executes a program from the configured quantum inputs.
///
/// For example, with [`ExecutionConfig::all_symbolic`], the initial values of
/// two declared qubits are `x0` and `x1`. After `cx q[0], q[1]`, their output
/// expressions are `x0` and `x1 ⊕ x0`.
/// Parameterized gates retain their source angles in the phase or scalar AST;
/// numerical approximation is deferred until explicitly requested.
pub fn execute(
    program: &Program,
    config: &ExecutionConfig,
) -> Result<HybridPathSum, SymbolicError> {
    let input = initial_memory(program, &config.initial_state)?;
    let component = Component {
        guard: BooleanPolynomial::one(),
        scalar: Scalar::one(),
        path_support: BTreeSet::new(),
        phase: PhasePolynomial::zero(),
        output: input.clone(),
    };
    let mut executor = Executor { next_path: 0 };
    let components = executor.execute_block(vec![component], &program.body)?;
    Ok(HybridPathSum { input, components })
}

fn initial_memory(
    program: &Program,
    initial_state: &InitialState,
) -> Result<HybridMemory, SymbolicError> {
    // An HPS input signature contains constants or free Boolean variables.
    // Uninitialized OpenQASM 3 classical declarations have no defined value;
    // measurement or a future assignment inserts one into the map.
    let qubits: BTreeSet<_> = register_cells(&program.quantum_registers).collect();
    if let InitialState::Zero { symbolic_inputs } = initial_state {
        if let Some(qubit) = symbolic_inputs.difference(&qubits).next() {
            return Err(SymbolicError::UnknownInput(qubit.clone()));
        }
    }
    let quantum = qubits
        .into_iter()
        .map(|qubit| {
            let symbolic = match initial_state {
                InitialState::AllSymbolic => true,
                InitialState::Zero { symbolic_inputs } => symbolic_inputs.contains(&qubit),
            };
            let value = if symbolic {
                BooleanPolynomial::variable(Variable::Input(qubit.clone()))
            } else {
                BooleanPolynomial::zero()
            };
            (qubit, value)
        })
        .collect();
    Ok(HybridMemory {
        quantum,
        classical: BTreeMap::new(),
        history: Vec::new(),
    })
}

/// Mutable execution context used only to allocate globally fresh path names.
///
/// Branches share this counter, so paths created in distinct components never
/// accidentally denote the same summation variable.
struct Executor {
    next_path: usize,
}

impl Executor {
    /// Executes statements in source order and removes block-local storage at
    /// lexical scope exit.
    ///
    /// A local bit has no value until assigned. Its measurement writes remain
    /// in `history` after exit because hiding a result must not restore quantum
    /// interference.
    fn execute_block(
        &mut self,
        mut components: Vec<Component>,
        block: &Block,
    ) -> Result<Vec<Component>, SymbolicError> {
        for statement in &block.statements {
            components = self.execute_statement(components, statement)?;
        }
        for component in &mut components {
            for bit in classical_cells(&block.classical_registers) {
                component.output.classical.remove(&bit);
            }
        }
        Ok(components)
    }

    /// Executes one statement over every incoming component.
    ///
    /// A classical branch is represented as two guarded HPS summands. Every
    /// other statement is linear and is applied independently to each summand.
    fn execute_statement(
        &mut self,
        components: Vec<Component>,
        statement: &Statement,
    ) -> Result<Vec<Component>, SymbolicError> {
        match statement {
            Statement::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let mut result = Vec::new();
                for component in components {
                    let condition = evaluate_classical(condition, &component.output.classical)?;
                    // ⟦if b then P else Q⟧(h) = b⟦P⟧(h) + (1-b)⟦Q⟧(h).
                    // Example: if c contains y0, the components receive guards
                    // y0 and 1 ⊕ y0, respectively.
                    let mut then_component = component.clone();
                    then_component.guard = then_component.guard.and(&condition);
                    let mut else_component = component;
                    else_component.guard = else_component.guard.and(&condition.complement());

                    if !then_component.guard.is_zero() {
                        result.extend(self.execute_block(vec![then_component], then_branch)?);
                    }
                    if !else_component.guard.is_zero() {
                        result.extend(self.execute_block(vec![else_component], else_branch)?);
                    }
                }
                Ok(result)
            }
            _ => components
                .into_iter()
                .map(|mut component| {
                    self.execute_linear(&mut component, statement)?;
                    Ok(component)
                })
                .collect(),
        }
    }

    /// Applies a non-branching statement to one HPS component.
    ///
    /// Measurement extends classical history, while reset extends hidden
    /// history and then writes `0` to the quantum wire. Both operations retain
    /// the information needed to prevent measured alternatives from
    /// interfering again.
    fn execute_linear(
        &mut self,
        component: &mut Component,
        statement: &Statement,
    ) -> Result<(), SymbolicError> {
        // Linear statements transform each existing component independently;
        // only classical `if` forms an explicit sum of components.
        match statement {
            Statement::Reset(qubit) => {
                let value = component.output.quantum[qubit].clone();
                // The discarded outcome separates worlds exactly like an
                // inaccessible measurement, preventing later interference.
                // Example: reset maps q=y0 to q=0 and records Discard(y0).
                component
                    .output
                    .history
                    .push(HistoryEntry::Discard { value });
                component
                    .output
                    .quantum
                    .insert(qubit.clone(), BooleanPolynomial::zero());
                Ok(())
            }
            Statement::Apply {
                gate,
                parameters,
                qubits,
            } => self.apply_gate(component, *gate, parameters, qubits),
            Statement::Measure { qubit, target } => {
                let value = component.output.quantum[qubit].clone();
                // Measurement copies the wire expression into classical
                // history; it does not remove the measured quantum wire.
                // Example: q=y0 gives c=y0 and records Write(c, y0).
                component
                    .output
                    .classical
                    .insert(target.clone(), value.clone());
                component.output.history.push(HistoryEntry::Write {
                    target: target.clone(),
                    value,
                });
                Ok(())
            }
            Statement::If { .. } => unreachable!(),
        }
    }

    fn apply_gate(
        &mut self,
        component: &mut Component,
        gate: Gate,
        parameters: &[NumericExpr],
        qubits: &[Qubit],
    ) -> Result<(), SymbolicError> {
        // Each arm acts on the current symbolic basis expressions. Permutation
        // gates rewrite `output.quantum`; diagonal gates add to `phase`; gates
        // with non-uniform magnitudes also multiply `scalar`. The result has
        // the HPS form
        //   sum_y scalar(x,y) exp(2πi phase(x,y)) |output(x,y)⟩.
        let first = qubits[0].clone();
        match gate {
            Gate::H => {
                let input = component.output.quantum[&first].clone();
                let path_index = self.fresh_path();
                let path = BooleanPolynomial::variable(Variable::Path(path_index));
                // H|x⟩ = 1/sqrt(2) Σ_y exp(2πi xy/2)|y⟩.
                component
                    .phase
                    .add_boolean(&path.and(&input), PhaseCoefficient::rational(ratio(1, 2)));
                component.output.quantum.insert(first, path);
                component.path_support.insert(path_index);
                component.scalar = component
                    .scalar
                    .clone()
                    .multiply(Scalar::sqrt(Scalar::rational(ratio(1, 2))));
            }
            Gate::X => self.flip(component, first),
            Gate::Y => {
                let input = component.output.quantum[&first].clone();
                // Y|x⟩ = exp(2πi(1/4 + x/2)) |x ⊕ 1⟩.
                component.phase.add_boolean(
                    &BooleanPolynomial::one(),
                    PhaseCoefficient::rational(ratio(1, 4)),
                );
                component
                    .phase
                    .add_boolean(&input, PhaseCoefficient::rational(ratio(1, 2)));
                self.flip(component, first);
            }
            Gate::Z => self.phase(component, &first, ratio(1, 2)),
            Gate::S => self.phase(component, &first, ratio(1, 4)),
            Gate::Sdg => self.phase(component, &first, ratio(-1, 4)),
            Gate::T => self.phase(component, &first, ratio(1, 8)),
            Gate::Tdg => self.phase(component, &first, ratio(-1, 8)),
            Gate::Cx => {
                // CX|c,t⟩ = |c,t ⊕ c⟩.
                let control = component.output.quantum[&first].clone();
                let target = qubits[1].clone();
                let value = component.output.quantum[&target].xor(&control);
                component.output.quantum.insert(target, value);
            }
            Gate::Cy => {
                let control = component.output.quantum[&first].clone();
                let target = qubits[1].clone();
                let target_value = component.output.quantum[&target].clone();
                // Condition both the Y phase and the target flip on the control:
                // t becomes t ⊕ c and the phase gains c/4 + c*t/2.
                component
                    .phase
                    .add_boolean(&control, PhaseCoefficient::rational(ratio(1, 4)));
                component.phase.add_boolean(
                    &control.and(&target_value),
                    PhaseCoefficient::rational(ratio(1, 2)),
                );
                component
                    .output
                    .quantum
                    .insert(target, target_value.xor(&control));
            }
            Gate::Cz => {
                // CZ contributes (-1)^(control*target).
                let control = component.output.quantum[&first].clone();
                let target = &component.output.quantum[&qubits[1]];
                component.phase.add_boolean(
                    &control.and(target),
                    PhaseCoefficient::rational(ratio(1, 2)),
                );
            }
            Gate::Swap => {
                let second = qubits[1].clone();
                let left = component.output.quantum[&first].clone();
                let right = component.output.quantum[&second].clone();
                component.output.quantum.insert(first, right);
                component.output.quantum.insert(second, left);
            }
            Gate::P => {
                // P(θ)|x⟩ = exp(iθx)|x⟩. Phase coefficients use
                // turns, hence the stored coefficient is θ/τ.
                let value = component.output.quantum[&first].clone();
                component.phase.add_boolean(
                    &value,
                    PhaseCoefficient::angle(parameters[0].clone(), ratio(1, 1)),
                );
            }
            Gate::Rz => {
                // Rz(θ)|x⟩ = exp(iθ(x-1/2))|x⟩.
                let angle = parameters[0].clone();
                let value = component.output.quantum[&first].clone();
                component.phase.add_boolean(
                    &BooleanPolynomial::one(),
                    PhaseCoefficient::angle(angle.clone(), ratio(-1, 2)),
                );
                component
                    .phase
                    .add_boolean(&value, PhaseCoefficient::angle(angle, ratio(1, 1)));
            }
            Gate::Cp => {
                // CP(θ) contributes exp(iθ) only on |11⟩.
                let control = component.output.quantum[&first].clone();
                let target = &component.output.quantum[&qubits[1]];
                component.phase.add_boolean(
                    &control.and(target),
                    PhaseCoefficient::angle(parameters[0].clone(), ratio(1, 1)),
                );
            }
            Gate::Crz => {
                // The Rz global phase becomes observable when controlled:
                // exp(iθ*c*(t-1/2)).
                let angle = parameters[0].clone();
                let control = component.output.quantum[&first].clone();
                let target = component.output.quantum[&qubits[1]].clone();
                component.phase.add_boolean(
                    &control,
                    PhaseCoefficient::angle(angle.clone(), ratio(-1, 2)),
                );
                component.phase.add_boolean(
                    &control.and(&target),
                    PhaseCoefficient::angle(angle, ratio(1, 1)),
                );
            }
            Gate::Rx => self.rotate_x(component, first, &parameters[0], None),
            Gate::Ry => self.rotate_y(component, first, &parameters[0], None),
            Gate::Crx => {
                let control = component.output.quantum[&first].clone();
                self.rotate_x(component, qubits[1].clone(), &parameters[0], Some(control));
            }
            Gate::Cry => {
                let control = component.output.quantum[&first].clone();
                self.rotate_y(component, qubits[1].clone(), &parameters[0], Some(control));
            }
        }
        Ok(())
    }

    fn fresh_path(&mut self) -> usize {
        // H and non-diagonal rotations introduce one Boolean output index for
        // each affected qubit. This monotone counter keeps them unique.
        let path = self.next_path;
        self.next_path += 1;
        path
    }

    fn flip(&self, component: &mut Component, qubit: Qubit) {
        // X is logical complement on a symbolic computational-basis value:
        // x becomes 1 ⊕ x.
        let value = component.output.quantum[&qubit].complement();
        component.output.quantum.insert(qubit, value);
    }

    fn phase(&self, component: &mut Component, qubit: &Qubit, angle: BigRational) {
        // A fixed diagonal gate contributes phase only when its input wire is
        // one. For example, Z adds x/2 turns.
        let value = &component.output.quantum[qubit];
        component
            .phase
            .add_boolean(value, PhaseCoefficient::rational(angle));
    }

    /// Expands `Rx(θ)` into paths with amplitudes `cos(θ/2)` and
    /// `-i sin(θ/2)`.
    ///
    /// If the input is `x` and the fresh output is `y`, `x ⊕ y` selects the
    /// sine term. The phase `-(x ⊕ y)/4` supplies `-i` on that path. A
    /// controlled rotation keeps only `y = x` when its control is false.
    fn rotate_x(
        &mut self,
        component: &mut Component,
        target: Qubit,
        angle: &NumericExpr,
        control: Option<BooleanPolynomial>,
    ) {
        let input = component.output.quantum[&target].clone();
        let path_index = self.fresh_path();
        let path = BooleanPolynomial::variable(Variable::Path(path_index));
        let flipped = input.xor(&path);
        let scalar = rotation_scalar(angle, &flipped, control.as_ref());
        component.scalar = component.scalar.clone().multiply(scalar);

        let phase_condition = match control {
            Some(control) => control.and(&flipped),
            None => flipped,
        };
        component
            .phase
            .add_boolean(&phase_condition, PhaseCoefficient::rational(ratio(-1, 4)));
        component.output.quantum.insert(target, path);
        component.path_support.insert(path_index);
    }

    /// Expands `Ry(θ)` into real sine/cosine paths.
    ///
    /// For input `x` and output `y`, the scalar again selects sine when
    /// `x ⊕ y = 1`. The phase `x(x ⊕ y)/2` supplies the sole minus sign:
    /// `Ry(θ)|1⟩ = cos(θ/2)|1⟩ - sin(θ/2)|0⟩`.
    fn rotate_y(
        &mut self,
        component: &mut Component,
        target: Qubit,
        angle: &NumericExpr,
        control: Option<BooleanPolynomial>,
    ) {
        let input = component.output.quantum[&target].clone();
        let path_index = self.fresh_path();
        let path = BooleanPolynomial::variable(Variable::Path(path_index));
        let flipped = input.xor(&path);
        let scalar = rotation_scalar(angle, &flipped, control.as_ref());
        component.scalar = component.scalar.clone().multiply(scalar);

        let mut negative = input.and(&flipped);
        if let Some(control) = control {
            negative = control.and(&negative);
        }
        component
            .phase
            .add_boolean(&negative, PhaseCoefficient::rational(ratio(1, 2)));
        component.output.quantum.insert(target, path);
        component.path_support.insert(path_index);
    }
}

/// Selects the sine or cosine coefficient for a rotation path.
///
/// `flipped = input ⊕ output`, so the uncontrolled result is
/// `if flipped then sin(θ/2) else cos(θ/2)`. Under a false quantum
/// control it becomes `if flipped then 0 else 1`, i.e. the identity exactly.
fn rotation_scalar(
    angle: &NumericExpr,
    flipped: &BooleanPolynomial,
    control: Option<&BooleanPolynomial>,
) -> Scalar {
    let half_angle = NumericExpr::Div(
        Box::new(angle.clone()),
        Box::new(NumericExpr::Rational(ratio(2, 1))),
    );
    let rotation = Scalar::select(
        flipped.clone(),
        Scalar::sin(half_angle.clone()),
        Scalar::cos(half_angle),
    );
    match control {
        Some(control) => Scalar::select(
            control.clone(),
            rotation,
            Scalar::select(flipped.clone(), Scalar::zero(), Scalar::one()),
        ),
        None => rotation,
    }
}

fn ratio(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(numerator.into(), denominator.into())
}

fn evaluate_classical(
    expression: &ClassicalExpr,
    memory: &BTreeMap<ClassicalBit, BooleanPolynomial>,
) -> Result<BooleanPolynomial, SymbolicError> {
    // Classical values use the same ANF representation as wire values. For
    // example, if c0=x and c1=y, `c0 || c1` becomes x ⊕ y ⊕ xy.
    match expression {
        ClassicalExpr::Bool(value) => Ok(BooleanPolynomial::from(*value)),
        ClassicalExpr::Bit(bit) => memory
            .get(bit)
            .cloned()
            .ok_or_else(|| SymbolicError::UninitializedClassical(bit.clone())),
        ClassicalExpr::Not(inner) => Ok(evaluate_classical(inner, memory)?.complement()),
        ClassicalExpr::Eq(left, right) => Ok(evaluate_classical(left, memory)?
            .xor(&evaluate_classical(right, memory)?)
            .complement()),
        ClassicalExpr::And(left, right) => {
            Ok(evaluate_classical(left, memory)?.and(&evaluate_classical(right, memory)?))
        }
        ClassicalExpr::Or(left, right) => {
            let left = evaluate_classical(left, memory)?;
            let right = evaluate_classical(right, memory)?;
            Ok(left.xor(&right).xor(&left.and(&right)))
        }
        ClassicalExpr::Xor(left, right) => {
            Ok(evaluate_classical(left, memory)?.xor(&evaluate_classical(right, memory)?))
        }
    }
}

fn register_cells(registers: &[Register]) -> impl Iterator<Item = Qubit> + '_ {
    // Flatten `qubit[3] q` into q[0], q[1], q[2].
    registers.iter().flat_map(|register| {
        (0..register.width).map(|index| Qubit {
            register: register.id,
            index,
        })
    })
}

fn classical_cells(registers: &[Register]) -> impl Iterator<Item = ClassicalBit> + '_ {
    // Classical registers use the same `(symbol, index)` addressing scheme.
    registers.iter().flat_map(|register| {
        (0..register.width).map(|index| ClassicalBit {
            register: register.id,
            index,
        })
    })
}
