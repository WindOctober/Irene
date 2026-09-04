use std::collections::{BTreeMap, BTreeSet};

use num_rational::BigRational;
use thiserror::Error;

use crate::ir::{
    AstIdGenerator, Block, ClassicalBit, ClassicalExpr, ClassicalExprKind, Gate, NumericExpr,
    NumericExprKind, Program, Qubit, Register, StatementKind,
};

use super::optimize::slice::{self, DiscardSet, OutputSelection, SlicePlan};
use super::optimize::{merge_components, simplify, simplify_component};
use super::validate;
use super::{BooleanPolynomial, PhaseCoefficient, PhasePolynomial, Scalar, Variable};

#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum SymbolicError {
    #[error("configured symbolic input is not declared by the program: {0:?}")]
    UnknownInput(Qubit),
    #[error("selected quantum output is not declared by the program: {0:?}")]
    UnknownQuantumOutput(Qubit),
    #[error("selected classical output is not declared by the program: {0:?}")]
    UnknownClassicalOutput(ClassicalBit),
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
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum HistoryEntry {
    /// A measurement result written to a classical bit.
    Write {
        target: ClassicalBit,
        value: BooleanPolynomial,
    },
    /// A result discarded by reset: inaccessible to the program but retained as history.
    Discard { value: BooleanPolynomial },
}

/// Quantum memory, current classical memory, and measurement/decoherence history.
///
/// The paper uses a stack of classical-memory snapshots. Irene keeps current
/// classical values separately and records only measurement writes and hidden
/// discarded values. These entries retain the distinctions between classical
/// worlds that must not interfere; ordinary deterministic assignments need no
/// additional history entry.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct HybridMemory {
    /// Computational-basis expression carried by each quantum wire.
    pub quantum: BTreeMap<Qubit, BooleanPolynomial>,
    /// Present value of each in-scope classical bit.
    pub classical: BTreeMap<ClassicalBit, BooleanPolynomial>,
    /// Sparse form of the classical-memory stack, including hidden reset outcomes.
    pub history: Vec<HistoryEntry>,
}

impl HybridMemory {
    /// Hides one computational-basis value while retaining the equality
    /// constraint required by partial trace.
    ///
    /// Constants create no alternative worlds. Likewise, if an earlier
    /// measurement already recorded the same expression, another copy would
    /// impose the identical bra/ket equality and is redundant.
    pub(crate) fn discard(&mut self, value: BooleanPolynomial) {
        if value.is_zero() || value.is_one() {
            return;
        }
        let already_recorded = self.history.iter().any(|entry| match entry {
            HistoryEntry::Write {
                value: recorded, ..
            }
            | HistoryEntry::Discard { value: recorded } => recorded == &value,
        });
        if !already_recorded {
            self.history.push(HistoryEntry::Discard { value });
        }
    }
}

/// One HPS summand produced by symbolic control flow.
///
/// Its amplitude is `scalar * exp(2πi phase)` on assignments satisfying
/// `guard`; `output` describes the hybrid-memory signature of the summand.
///
/// For example, branching on a measured path variable `y0` produces a then
/// component guarded by `y0` and an else component guarded by `1 ⊕ y0`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Component {
    /// Polynomials interpreted as equations to zero; their conjunction selects
    /// this component. For example, `y0` denotes the constraint `y0 = 0`.
    pub guard: Vec<BooleanPolynomial>,
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

/// Executes a program from the configured inputs and selected outputs.
///
/// For example, with [`ExecutionConfig::all_symbolic`], the initial values of
/// two declared qubits are `x0` and `x1`. After `cx q[0], q[1]`, their output
/// expressions are `x0` and `x1 ⊕ x0`.
/// Parameterized gates retain their source angles in the phase or scalar AST;
/// numerical approximation is deferred until explicitly requested.
pub fn execute(
    program: &Program,
    config: &ExecutionConfig,
    output_selection: &OutputSelection,
) -> Result<HybridPathSum, SymbolicError> {
    let plan = slice::build_slice_plan(program, output_selection)?;
    validate::definite_assignment(program, output_selection)?;
    let mut hps = simplify(execute_with_plan(program, config, &plan)?);
    hps.components = merge_components(hps.components);
    Ok(hps)
}

/// Executes with a precomputed slice plan.
///
/// Statements always come from the original program. The sidecar plan only
/// decides whether each statement is relevant and where dead values can be
/// discarded.
fn execute_with_plan(
    program: &Program,
    config: &ExecutionConfig,
    plan: &SlicePlan,
) -> Result<HybridPathSum, SymbolicError> {
    let mut tracked_inputs = plan.live_quantum.clone();
    match &config.initial_state {
        InitialState::AllSymbolic => {
            tracked_inputs.extend(register_cells(&program.quantum_registers));
        }
        InitialState::Zero { symbolic_inputs } => {
            tracked_inputs.extend(symbolic_inputs.iter().cloned());
        }
    }
    let input = initial_memory(program, &config.initial_state, &tracked_inputs)?;
    let mut component = Component {
        guard: Vec::new(),
        scalar: Scalar::one(),
        path_support: BTreeSet::new(),
        phase: PhasePolynomial::zero(),
        output: input.clone(),
    };
    // Symbolic inputs remain in `input`, even when they cannot affect a
    // selected output. Move those dead inputs into hidden history instead of
    // silently deleting them: `Discard(x)` represents the partial trace that
    // prevents the x=0 and x=1 amplitudes from interfering afterwards.
    DiscardSet {
        quantum: tracked_inputs
            .difference(&plan.live_quantum)
            .cloned()
            .collect(),
        classical: Vec::new(),
    }
    .apply(&mut component);
    let mut executor = Executor {
        next_path: 0,
        ids: AstIdGenerator::starting_at(program.ast_id_bound()),
    };
    let components = executor.execute_block(vec![component], &program.body, plan)?;
    Ok(HybridPathSum { input, components })
}

fn initial_memory(
    program: &Program,
    initial_state: &InitialState,
    tracked_qubits: &BTreeSet<Qubit>,
) -> Result<HybridMemory, SymbolicError> {
    // An HPS input signature contains constants or free Boolean variables.
    // Uninitialized OpenQASM 3 classical declarations have no defined value;
    // measurement or a future assignment inserts one into the map.
    let qubits: BTreeSet<_> = register_cells(&program.quantum_registers).collect();
    if let InitialState::Zero { symbolic_inputs } = initial_state
        && let Some(qubit) = symbolic_inputs.difference(&qubits).next()
    {
        return Err(SymbolicError::UnknownInput(qubit.clone()));
    }
    let quantum = qubits
        .into_iter()
        .filter(|qubit| tracked_qubits.contains(qubit))
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

/// Mutable allocation context shared across one symbolic execution.
///
/// Branches share the path counter so distinct components never reuse a
/// summation variable. Synthesized numeric expressions receive AST IDs beyond
/// the source program's ID range.
struct Executor {
    next_path: usize,
    ids: AstIdGenerator,
}

impl Executor {
    /// Executes original IR statements using an AST-ID-indexed slice plan.
    ///
    /// Statements run in source order. At lexical scope exit, block-local
    /// classical values are removed from the current memory, but their writes
    /// remain in history: hiding a measurement result must not restore
    /// interference between the worlds it created.
    fn execute_block(
        &mut self,
        mut components: Vec<Component>,
        block: &Block,
        plan: &SlicePlan,
    ) -> Result<Vec<Component>, SymbolicError> {
        // Entry discard sets primarily occur on `if` branches. Backward analysis
        // takes the union of both branches' dependencies before the `if`, so a
        // value needed only by the sibling branch is still present here. The
        // discard set traces that value out as soon as this branch is entered.
        //
        // Example: in `if c { cx a, out } else { skip }`, with only `out`
        // selected, `a` is live before the `if` but is discarded at the entry
        // of the else block.
        if let Some(discard) = plan.discard_set(block.ast_id) {
            for component in &mut components {
                discard.apply(component);
            }
            if components.len() > 1 {
                components = merge_components(components);
            }
        }
        for statement in &block.statements {
            if !plan.retains(statement.ast_id) {
                continue;
            }
            let is_join = matches!(&statement.kind, StatementKind::If { .. });
            let is_reset = matches!(&statement.kind, StatementKind::Reset(_));
            components = match &statement.kind {
                StatementKind::If {
                    condition,
                    then_branch,
                    else_branch,
                } => self.execute_if(components, condition, then_branch, else_branch, plan)?,
                StatementKind::Scope(body) => self.execute_block(components, body, plan)?,
                _ => components
                    .into_iter()
                    .map(|mut component| {
                        self.execute_linear(&mut component, &statement.kind)?;
                        Ok(component)
                    })
                    .collect::<Result<_, _>>()?,
            };
            // A post-statement discard set denotes the last point at which a
            // value can influence the selected outputs. For example, after
            // `cx a, out`, `a` can be traced out when no later live statement
            // reads it, while its effect on `out` remains represented.
            let discard = plan.discard_set(statement.ast_id);
            if let Some(discard) = discard {
                for component in &mut components {
                    discard.apply(component);
                }
            }
            // Branch joins, information-destroying resets, and discard
            // boundaries can make previously distinct components identical.
            // Merge only at those events instead of rescanning after every
            // unitary statement.
            if components.len() > 1 && (is_join || is_reset || discard.is_some()) {
                components = merge_components(components);
            }
        }
        let removes_locals = !block.classical_registers.is_empty();
        for component in &mut components {
            for bit in classical_cells(&block.classical_registers) {
                component.output.classical.remove(&bit);
            }
        }
        if components.len() > 1 && removes_locals {
            components = merge_components(components);
        }
        Ok(components)
    }

    /// Executes a classical conditional either as a guarded unitary or as an
    /// explicit sum of HPS components.
    ///
    /// A block containing only monomial gates has an exact pointwise action on
    /// computational-basis expressions. For example, `if c { z q }` adds the
    /// phase `c*q/2` directly, so the symbolic values `c=0` and `c=1` need not
    /// become separate components. Other blocks retain the general HPS rule
    /// `c [[then]] + (1-c) [[else]]`.
    fn execute_if(
        &mut self,
        components: Vec<Component>,
        condition: &ClassicalExpr,
        then_branch: &Block,
        else_branch: &Block,
        plan: &SlicePlan,
    ) -> Result<Vec<Component>, SymbolicError> {
        if is_predicable_block(then_branch, plan) && is_predicable_block(else_branch, plan) {
            let mut result = Vec::with_capacity(components.len());
            for mut component in components {
                let predicate = evaluate_classical(condition, &component.output.classical)?;
                self.execute_predicated_block(&mut component, then_branch, &predicate, plan);
                self.execute_predicated_block(
                    &mut component,
                    else_branch,
                    &predicate.complement(),
                    plan,
                );
                result.push(component);
            }
            return Ok(result);
        }

        let mut result = Vec::new();
        for component in components {
            let condition = evaluate_classical(condition, &component.output.classical)?;
            // Guards are equations equal to zero. The then branch therefore
            // adds `1 ⊕ condition = 0`, while the else branch adds
            // `condition = 0`. Simplifying immediately removes determined path
            // variables before either branch introduces more expressions.
            let mut then_component = component.clone();
            let then_constraint = condition.complement();
            if !then_constraint.is_zero() {
                then_component.guard.push(then_constraint);
            }
            let mut else_component = component;
            if !condition.is_zero() {
                else_component.guard.push(condition);
            }
            if simplify_component(&mut then_component) {
                result.extend(self.execute_block(vec![then_component], then_branch, plan)?);
            }
            if simplify_component(&mut else_component) {
                result.extend(self.execute_block(vec![else_component], else_branch, plan)?);
            }
        }
        Ok(result)
    }

    /// Applies a side-effect-free unitary block under one symbolic predicate.
    ///
    /// [`is_predicable_block`] ensures that every retained statement has an
    /// exact guarded basis-state transformer and that no branch-local partial
    /// trace is skipped here.
    fn execute_predicated_block(
        &mut self,
        component: &mut Component,
        block: &Block,
        predicate: &BooleanPolynomial,
        plan: &SlicePlan,
    ) {
        for statement in &block.statements {
            if !plan.retains(statement.ast_id) {
                continue;
            }
            match &statement.kind {
                StatementKind::Apply {
                    gate,
                    parameters,
                    qubits,
                } => self.apply_predicated_gate(component, *gate, parameters, qubits, predicate),
                StatementKind::Scope(body) => {
                    self.execute_predicated_block(component, body, predicate, plan);
                }
                _ => unreachable!("predicable blocks contain only monomial gates"),
            }
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
        statement: &StatementKind,
    ) -> Result<(), SymbolicError> {
        // Linear statements transform each existing component independently;
        // only classical `if` forms an explicit sum of components.
        match statement {
            StatementKind::Reset(qubit) => {
                let value = component
                    .output
                    .quantum
                    .insert(qubit.clone(), BooleanPolynomial::zero());
                // The discarded outcome separates worlds exactly like an
                // inaccessible measurement, preventing later interference.
                // Example: reset maps q=y0 to q=0 and records Discard(y0).
                if let Some(value) = value {
                    component.output.discard(value);
                }
                Ok(())
            }
            StatementKind::Apply {
                gate,
                parameters,
                qubits,
            } => self.apply_gate(component, *gate, parameters, qubits),
            StatementKind::Measure { qubit, target } => {
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
            StatementKind::Assign { target, value } => {
                let value = evaluate_classical(value, &component.output.classical)?;
                component.output.classical.insert(target.clone(), value);
                Ok(())
            }
            StatementKind::If { .. } | StatementKind::Scope(_) => unreachable!(),
        }
    }

    fn apply_gate(
        &mut self,
        component: &mut Component,
        gate: Gate,
        parameters: &[NumericExpr],
        qubits: &[Qubit],
    ) -> Result<(), SymbolicError> {
        let predicate = BooleanPolynomial::one();
        if is_monomial_gate(gate) {
            self.apply_monomial_gate(component, gate, parameters, qubits, &predicate);
            return Ok(());
        }

        // Non-monomial gates introduce a new path and possibly a non-uniform
        // scalar. They retain their ordinary, unconditional HPS rules here;
        // symbolic classical predication conservatively falls back to explicit
        // branch components before reaching this method.
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
            Gate::X
            | Gate::Y
            | Gate::Z
            | Gate::S
            | Gate::Sdg
            | Gate::T
            | Gate::Tdg
            | Gate::Cx
            | Gate::Ccx
            | Gate::Cy
            | Gate::Cz
            | Gate::Swap
            | Gate::P
            | Gate::Rz
            | Gate::Cp
            | Gate::Crz => unreachable!("monomial gates returned above"),
        }
        Ok(())
    }

    /// Applies a monomial gate under a classical Boolean predicate.
    ///
    /// Monomial gates map each basis vector to one basis vector with a
    /// unit-magnitude phase. Consequently, predication only multiplies their
    /// Boolean update and phase conditions by `predicate`; it introduces no
    /// path variable or branch component.
    fn apply_monomial_gate(
        &self,
        component: &mut Component,
        gate: Gate,
        parameters: &[NumericExpr],
        qubits: &[Qubit],
        predicate: &BooleanPolynomial,
    ) {
        let first = qubits[0].clone();
        match gate {
            Gate::X => self.flip_when(component, first, predicate),
            Gate::Y => {
                let input = component.output.quantum[&first].clone();
                // `if b { Y q }` maps x to x⊕b and contributes
                // b*(1/4+x/2) turns.
                component
                    .phase
                    .add_boolean(predicate, PhaseCoefficient::rational(ratio(1, 4)));
                component.phase.add_boolean(
                    &predicate.and(&input),
                    PhaseCoefficient::rational(ratio(1, 2)),
                );
                self.flip_when(component, first, predicate);
            }
            Gate::Z => self.phase_when(component, &first, ratio(1, 2), predicate),
            Gate::S => self.phase_when(component, &first, ratio(1, 4), predicate),
            Gate::Sdg => self.phase_when(component, &first, ratio(-1, 4), predicate),
            Gate::T => self.phase_when(component, &first, ratio(1, 8), predicate),
            Gate::Tdg => self.phase_when(component, &first, ratio(-1, 8), predicate),
            Gate::Cx => {
                // `if b { CX c,t }` maps t to t ⊕ b*c.
                let control = component.output.quantum[&first].clone();
                let target = qubits[1].clone();
                let change = predicate.and(&control);
                let value = component.output.quantum[&target].xor(&change);
                component.output.quantum.insert(target, value);
            }
            Gate::Ccx => {
                let left = component.output.quantum[&first].clone();
                let right = component.output.quantum[&qubits[1]].clone();
                let target = qubits[2].clone();
                let change = predicate.and(&left).and(&right);
                let value = component.output.quantum[&target].xor(&change);
                component.output.quantum.insert(target, value);
            }
            Gate::Cy => {
                let control = component.output.quantum[&first].clone();
                let effective_control = predicate.and(&control);
                let target = qubits[1].clone();
                let target_value = component.output.quantum[&target].clone();
                component
                    .phase
                    .add_boolean(&effective_control, PhaseCoefficient::rational(ratio(1, 4)));
                component.phase.add_boolean(
                    &effective_control.and(&target_value),
                    PhaseCoefficient::rational(ratio(1, 2)),
                );
                component
                    .output
                    .quantum
                    .insert(target, target_value.xor(&effective_control));
            }
            Gate::Cz => {
                let control = component.output.quantum[&first].clone();
                let target = component.output.quantum[&qubits[1]].clone();
                component.phase.add_boolean(
                    &predicate.and(&control).and(&target),
                    PhaseCoefficient::rational(ratio(1, 2)),
                );
            }
            Gate::Swap => {
                let second = qubits[1].clone();
                let left = component.output.quantum[&first].clone();
                let right = component.output.quantum[&second].clone();
                let change = predicate.and(&left.xor(&right));
                component.output.quantum.insert(first, left.xor(&change));
                component.output.quantum.insert(second, right.xor(&change));
            }
            Gate::P => {
                let value = component.output.quantum[&first].clone();
                component.phase.add_boolean(
                    &predicate.and(&value),
                    PhaseCoefficient::angle(parameters[0].clone(), ratio(1, 1)),
                );
            }
            Gate::Rz => {
                let angle = parameters[0].clone();
                let value = component.output.quantum[&first].clone();
                component.phase.add_boolean(
                    predicate,
                    PhaseCoefficient::angle(angle.clone(), ratio(-1, 2)),
                );
                component.phase.add_boolean(
                    &predicate.and(&value),
                    PhaseCoefficient::angle(angle, ratio(1, 1)),
                );
            }
            Gate::Cp => {
                let control = component.output.quantum[&first].clone();
                let target = component.output.quantum[&qubits[1]].clone();
                component.phase.add_boolean(
                    &predicate.and(&control).and(&target),
                    PhaseCoefficient::angle(parameters[0].clone(), ratio(1, 1)),
                );
            }
            Gate::Crz => {
                let angle = parameters[0].clone();
                let control = predicate.and(&component.output.quantum[&first]);
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
            Gate::H | Gate::Rx | Gate::Ry | Gate::Crx | Gate::Cry => {
                unreachable!("non-monomial gate passed to monomial transformer")
            }
        }
    }

    /// Applies one already-classified monomial gate without splitting worlds.
    fn apply_predicated_gate(
        &self,
        component: &mut Component,
        gate: Gate,
        parameters: &[NumericExpr],
        qubits: &[Qubit],
        predicate: &BooleanPolynomial,
    ) {
        if predicate.is_zero() {
            return;
        }
        self.apply_monomial_gate(component, gate, parameters, qubits, predicate);
    }

    fn fresh_path(&mut self) -> usize {
        // H and non-diagonal rotations introduce one Boolean output index for
        // each affected qubit. This monotone counter keeps them unique.
        let path = self.next_path;
        self.next_path += 1;
        path
    }

    fn flip_when(&self, component: &mut Component, qubit: Qubit, predicate: &BooleanPolynomial) {
        // A predicated X changes x to x ⊕ b. The unconditional case uses
        // b=1 and therefore reduces to ordinary Boolean complement.
        let value = component.output.quantum[&qubit].xor(predicate);
        component.output.quantum.insert(qubit, value);
    }

    fn phase_when(
        &self,
        component: &mut Component,
        qubit: &Qubit,
        angle: BigRational,
        predicate: &BooleanPolynomial,
    ) {
        // A fixed diagonal gate contributes phase only when both its input
        // wire and the surrounding classical predicate are one.
        let value = &component.output.quantum[qubit];
        component
            .phase
            .add_boolean(&predicate.and(value), PhaseCoefficient::rational(angle));
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
        let scalar = self.rotation_scalar(angle, &flipped, control.as_ref());
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
        let scalar = self.rotation_scalar(angle, &flipped, control.as_ref());
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

    /// Selects the sine or cosine coefficient for a rotation path.
    ///
    /// `flipped = input ⊕ output`, so the uncontrolled result is
    /// `if flipped then sin(θ/2) else cos(θ/2)`. Under a false quantum
    /// control it becomes `if flipped then 0 else 1`, i.e. the identity exactly.
    fn rotation_scalar(
        &mut self,
        angle: &NumericExpr,
        flipped: &BooleanPolynomial,
        control: Option<&BooleanPolynomial>,
    ) -> Scalar {
        let denominator = self.ids.node(NumericExprKind::Rational(ratio(2, 1)));
        let half_angle = self.ids.node(NumericExprKind::Div(
            Box::new(angle.clone()),
            Box::new(denominator),
        ));
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
}

/// Whether a sliced block can be executed as one guarded basis transformer.
///
/// Branch-local discard points are deliberately excluded: partial trace under
/// a symbolic predicate needs its own density-level rule and cannot be applied
/// to the unsplit component unconditionally. Blocks with classical mutation,
/// measurement, reset, or non-monomial gates likewise use ordinary splitting.
fn is_predicable_block(block: &Block, plan: &SlicePlan) -> bool {
    block.classical_registers.is_empty()
        && plan.discard_set(block.ast_id).is_none()
        && block.statements.iter().all(|statement| {
            if !plan.retains(statement.ast_id) {
                return true;
            }
            if plan.discard_set(statement.ast_id).is_some() {
                return false;
            }
            match &statement.kind {
                StatementKind::Apply { gate, .. } => is_monomial_gate(*gate),
                StatementKind::Scope(body) => is_predicable_block(body, plan),
                StatementKind::Reset(_)
                | StatementKind::Measure { .. }
                | StatementKind::Assign { .. }
                | StatementKind::If { .. } => false,
            }
        })
}

/// Monomial gates permute computational-basis states and attach phases of unit
/// magnitude, so their action remains exact after multiplying it by a Boolean
/// predicate.
fn is_monomial_gate(gate: Gate) -> bool {
    matches!(
        gate,
        Gate::X
            | Gate::Y
            | Gate::Z
            | Gate::S
            | Gate::Sdg
            | Gate::T
            | Gate::Tdg
            | Gate::Cx
            | Gate::Ccx
            | Gate::Cy
            | Gate::Cz
            | Gate::Swap
            | Gate::P
            | Gate::Rz
            | Gate::Cp
            | Gate::Crz
    )
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
    match &expression.kind {
        ClassicalExprKind::Bool(value) => Ok(BooleanPolynomial::from(*value)),
        ClassicalExprKind::Bit(bit) => memory
            .get(bit)
            .cloned()
            .ok_or_else(|| SymbolicError::UninitializedClassical(bit.clone())),
        ClassicalExprKind::Not(inner) => Ok(evaluate_classical(inner, memory)?.complement()),
        ClassicalExprKind::Eq(left, right) => Ok(evaluate_classical(left, memory)?
            .xor(&evaluate_classical(right, memory)?)
            .complement()),
        ClassicalExprKind::And(left, right) => {
            Ok(evaluate_classical(left, memory)?.and(&evaluate_classical(right, memory)?))
        }
        ClassicalExprKind::Or(left, right) => {
            let left = evaluate_classical(left, memory)?;
            let right = evaluate_classical(right, memory)?;
            Ok(left.xor(&right).xor(&left.and(&right)))
        }
        ClassicalExprKind::Xor(left, right) => {
            Ok(evaluate_classical(left, memory)?.xor(&evaluate_classical(right, memory)?))
        }
    }
}

pub(crate) fn register_cells(registers: &[Register]) -> impl Iterator<Item = Qubit> + '_ {
    // Flatten `qubit[3] q` into q[0], q[1], q[2].
    registers.iter().flat_map(|register| {
        (0..register.width).map(|index| Qubit {
            register: register.id,
            index,
        })
    })
}

pub(crate) fn classical_cells(registers: &[Register]) -> impl Iterator<Item = ClassicalBit> + '_ {
    // Classical registers use the same `(symbol, index)` addressing scheme.
    registers.iter().flat_map(|register| {
        (0..register.width).map(|index| ClassicalBit {
            register: register.id,
            index,
        })
    })
}
