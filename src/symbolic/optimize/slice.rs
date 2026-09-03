//! Backward dependency analysis for output-directed symbolic execution.
//!
//! Starting from the selected outputs, this module walks each block backwards
//! and records where quantum or classical values become dead. The executor
//! later consumes those sparse discard sets in source order; it does not repeat
//! the dependency analysis for every HPS component.

use std::collections::BTreeSet;

use crate::ir::{
    AstId, Block, ClassicalBit, ClassicalExpr, ClassicalExprKind, Program, Qubit, StatementKind,
};
use crate::symbolic::executor::{classical_cells, register_cells};
use crate::symbolic::{Component, SymbolicError};

/// Quantum and classical program outputs retained by symbolic execution.
///
/// For example, selecting only `q[1]` causes an unrelated measurement
/// `measure q[0] -> c[0]` to be removed, unless `q[0]` or `c[0]` later affects
/// `q[1]`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutputSelection {
    pub quantum: BTreeSet<Qubit>,
    pub classical: BTreeSet<ClassicalBit>,
}

impl OutputSelection {
    /// Constructs the output interface used as the root of dependency analysis.
    pub fn new(
        quantum: impl IntoIterator<Item = Qubit>,
        classical: impl IntoIterator<Item = ClassicalBit>,
    ) -> Self {
        Self {
            quantum: quantum.into_iter().collect(),
            classical: classical.into_iter().collect(),
        }
    }
}

/// Builds an output-directed slice plan.
///
/// Dependency analysis traverses the program once in reverse and records the
/// exact positions where values cease to affect the selected outputs.
///
/// For example, for `cx q[0], q[1]` with only `q[1]` observed, both operands
/// are live before the gate, while `q[0]` becomes dead immediately afterwards.
pub(crate) fn build_slice_plan(
    program: &Program,
    output_selection: &OutputSelection,
) -> Result<SlicePlan, SymbolicError> {
    let outputs = terminal_live_set(program, output_selection)?;
    let node_count = program.ast_id_bound();
    let mut plan = SlicePlan {
        live_quantum: BTreeSet::new(),
        entries: vec![NodePlan::default(); node_count],
    };
    let analysis = analyze_block(&program.body, outputs, &mut plan);
    plan.live_quantum = analysis.live.quantum;
    Ok(plan)
}

/// Backward-slice metadata for the complete program.
///
/// The table is indexed directly by the original node's [`AstId`]. A block ID
/// addresses its entry discard set; a statement ID addresses its
/// post-statement discard set and retention bit. Block entries handle
/// branch-specific liveness; statement entries handle ordinary last uses. No
/// executable IR is copied into the plan.
#[derive(Debug)]
pub(crate) struct SlicePlan {
    pub(crate) live_quantum: BTreeSet<Qubit>,
    entries: Vec<NodePlan>,
}

#[derive(Debug, Clone, Default)]
struct NodePlan {
    retained: bool,
    discard: Option<DiscardSet>,
}

impl SlicePlan {
    fn retain(&mut self, id: AstId) {
        self.entries[id.0].retained = true;
    }

    fn set_discard(&mut self, id: AstId, discard: DiscardSet) {
        if !discard.is_empty() {
            self.entries[id.0].discard = Some(discard);
        }
    }

    pub(crate) fn retains(&self, id: AstId) -> bool {
        self.entries[id.0].retained
    }

    pub(crate) fn discard_set(&self, id: AstId) -> Option<&DiscardSet> {
        self.entries[id.0].discard.as_ref()
    }
}

/// Variables that die at one precomputed program position.
///
/// A discard set after `cx q[0], q[1]`, when only `q[1]` remains live, contains
/// `q[0]`. Applying it removes `q[0]` from the visible quantum memory while
/// preserving any hidden classical distinction required by partial trace.
#[derive(Debug, Clone, Default)]
pub(crate) struct DiscardSet {
    pub(crate) quantum: Vec<Qubit>,
    pub(crate) classical: Vec<ClassicalBit>,
}

impl DiscardSet {
    fn is_empty(&self) -> bool {
        self.quantum.is_empty() && self.classical.is_empty()
    }
    /// Computes the variables needed before a boundary but not after it.
    ///
    /// If a branch starts with `{q[0], q[1]}` live but needs only `q[1]`, its
    /// entry discard set contains `q[0]`.
    fn between(before: &LiveSet, after: &LiveSet) -> Self {
        Self {
            quantum: before.quantum.difference(&after.quantum).cloned().collect(),
            classical: before
                .classical
                .difference(&after.classical)
                .cloned()
                .collect(),
        }
    }

    /// Removes dead classical values and partially traces dead quantum values.
    ///
    /// Removing a symbolic value such as `y0` records `Discard(y0)`, because
    /// the alternatives `y0 = 0` and `y0 = 1` must remain incoherent. Removing
    /// a known `0` or `1` needs no history entry because it creates no worlds.
    /// Thus this operation computes a reduced density state; it is not merely
    /// deletion from a state vector.
    pub(crate) fn apply(&self, component: &mut Component) {
        for qubit in &self.quantum {
            if let Some(value) = component.output.quantum.remove(qubit) {
                component.output.discard(value);
            }
        }
        for bit in &self.classical {
            component.output.classical.remove(bit);
        }
    }
}

#[derive(Debug, Clone, Default)]
struct LiveSet {
    /// Quantum values that can still influence an observed output.
    quantum: BTreeSet<Qubit>,
    /// Classical values that can still influence an output or branch.
    classical: BTreeSet<ClassicalBit>,
}

/// Builds every sparse discard set in one reverse traversal.
///
/// For `measure q -> c; if (c) x r;` with `r` observed, reverse traversal
/// first discovers that `c` controls a live update, then follows the
/// measurement back to `q`. Consequently both statements are retained even
/// when neither `q` nor `c` is itself observable.
struct BlockSummary {
    live: LiveSet,
    retained: bool,
}

fn analyze_block(block: &Block, mut live: LiveSet, plan: &mut SlicePlan) -> BlockSummary {
    let mut retained = false;
    for statement in block.statements.iter().rev() {
        match &statement.kind {
            StatementKind::Apply { qubits, .. } => {
                // A multi-qubit unitary may entangle every operand with a live
                // output. A unitary confined to a dead subsystem is invisible
                // after partial trace.
                if qubits.iter().any(|qubit| live.quantum.contains(qubit)) {
                    let after = DiscardSet {
                        quantum: qubits
                            .iter()
                            .filter(|qubit| !live.quantum.contains(*qubit))
                            .cloned()
                            .collect(),
                        classical: Vec::new(),
                    };
                    live.quantum.extend(qubits.iter().cloned());
                    plan.retain(statement.ast_id);
                    plan.set_discard(statement.ast_id, after);
                    retained = true;
                }
            }
            StatementKind::Reset(qubit) => {
                // Reset creates a fresh |0>, so its incoming value is dead.
                // Example: in `h q; reset q` with q observed, reset remains but
                // the preceding H is outside the output's dependency cone.
                if live.quantum.remove(qubit) {
                    plan.retain(statement.ast_id);
                    retained = true;
                }
            }
            StatementKind::Measure { qubit, target } => {
                // The measurement matters if its quantum wire survives or its
                // classical result is used. Assignment kills the old target.
                // If only c is live in `measure q -> c`, q becomes live before
                // the measurement and dies immediately after it.
                let qubit_is_live = live.quantum.contains(qubit);
                let target_is_live = live.classical.remove(target);
                if qubit_is_live || target_is_live {
                    live.quantum.insert(qubit.clone());
                    plan.retain(statement.ast_id);
                    plan.set_discard(
                        statement.ast_id,
                        DiscardSet {
                            quantum: (!qubit_is_live)
                                .then(|| qubit.clone())
                                .into_iter()
                                .collect(),
                            classical: (!target_is_live)
                                .then(|| target.clone())
                                .into_iter()
                                .collect(),
                        },
                    );
                    retained = true;
                }
            }
            StatementKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                // Both branches must start from one common pre-`if` memory, so
                // their input dependencies are unioned. Each branch receives
                // an entry discard set for the part of that union needed only by
                // the opposite branch. For example, if only the then branch
                // uses `a`, the else block traces out `a` immediately.
                let after = live.clone();
                let then_analysis = analyze_block(then_branch, after.clone(), plan);
                let else_analysis = analyze_block(else_branch, after.clone(), plan);
                if then_analysis.retained || else_analysis.retained {
                    let mut before = LiveSet {
                        quantum: then_analysis
                            .live
                            .quantum
                            .union(&else_analysis.live.quantum)
                            .cloned()
                            .collect(),
                        classical: then_analysis
                            .live
                            .classical
                            .union(&else_analysis.live.classical)
                            .cloned()
                            .collect(),
                    };
                    collect_classical_reads(condition, &mut before.classical);
                    plan.set_discard(
                        then_branch.ast_id,
                        DiscardSet::between(&before, &then_analysis.live),
                    );
                    plan.set_discard(
                        else_branch.ast_id,
                        DiscardSet::between(&before, &else_analysis.live),
                    );
                    plan.retain(statement.ast_id);
                    live = before;
                    retained = true;
                }
            }
        }
    }
    BlockSummary { live, retained }
}

/// Adds every classical cell read by an expression to the live set.
///
/// For `c[0] ^ !c[1]`, both `c[0]` and `c[1]` become live before the branch.
fn collect_classical_reads(expression: &ClassicalExpr, bits: &mut BTreeSet<ClassicalBit>) {
    match &expression.kind {
        ClassicalExprKind::Bool(_) => {}
        ClassicalExprKind::Bit(bit) => {
            bits.insert(bit.clone());
        }
        ClassicalExprKind::Not(inner) => collect_classical_reads(inner, bits),
        ClassicalExprKind::Eq(left, right)
        | ClassicalExprKind::And(left, right)
        | ClassicalExprKind::Or(left, right)
        | ClassicalExprKind::Xor(left, right) => {
            collect_classical_reads(left, bits);
            collect_classical_reads(right, bits);
        }
    }
}

/// Validates the requested output interface and turns it into the terminal
/// live set from which backward analysis starts.
fn terminal_live_set(
    program: &Program,
    output_selection: &OutputSelection,
) -> Result<LiveSet, SymbolicError> {
    let quantum = register_cells(&program.quantum_registers).collect::<BTreeSet<_>>();
    let classical = classical_cells(&program.classical_registers).collect::<BTreeSet<_>>();
    if let Some(qubit) = output_selection.quantum.difference(&quantum).next() {
        return Err(SymbolicError::UnknownQuantumOutput(qubit.clone()));
    }
    if let Some(bit) = output_selection.classical.difference(&classical).next() {
        return Err(SymbolicError::UnknownClassicalOutput(bit.clone()));
    }
    Ok(LiveSet {
        quantum: output_selection.quantum.clone(),
        classical: output_selection.classical.clone(),
    })
}
