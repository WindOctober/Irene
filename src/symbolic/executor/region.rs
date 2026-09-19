//! Compose a small, independently simplified channel with the current prefix.
//!
//! A source-order window ends at a common last-use boundary for all of its
//! measurements. All touched wires (including correction targets and sliced
//! discards) form its boundary, not just the measured wire. Nonconstant quantum
//! values become free inputs; the prefix's guards, paths and environment NEVER
//! enter the local proof. Only a single history-free Kraus summary is accepted.
//! The same summary is composed with EVERY prefix component, preserving their
//! coherent cross terms and their existing environment labels.

use super::*;
use crate::ir::Statement;
use crate::symbolic::optimize::substitute_component;

const MAX_STATEMENTS: usize = 48;
const MAX_WIRES: usize = 12;
const MAX_COMPONENTS: usize = 16;

#[derive(Default)]
struct Boundary {
    quantum: BTreeSet<Qubit>,
    classical: BTreeSet<ClassicalBit>,
    reads: BTreeSet<ClassicalBit>,
    written: BTreeSet<ClassicalBit>,
    pending: BTreeSet<ClassicalBit>,
    measurements: usize,
    operations: usize,
    splits: usize,
}

impl Boundary {
    fn read(&mut self, expression: &ClassicalExpr) {
        match &expression.kind {
            ClassicalExprKind::Bool(_) => {}
            ClassicalExprKind::Bit(bit) => {
                self.classical.insert(bit.clone());
                if !self.written.contains(bit) {
                    self.reads.insert(bit.clone());
                }
            }
            ClassicalExprKind::Not(inner) => self.read(inner),
            ClassicalExprKind::Eq(a, b)
            | ClassicalExprKind::And(a, b)
            | ClassicalExprKind::Or(a, b)
            | ClassicalExprKind::Xor(a, b) => {
                self.read(a);
                self.read(b);
            }
        }
    }

    fn statement(&mut self, statement: &Statement, plan: &SlicePlan, nested: bool) -> bool {
        if !plan.retains(statement.ast_id) {
            return true;
        }
        self.operations += 1;
        match &statement.kind {
            StatementKind::Apply { qubits, .. } => self.quantum.extend(qubits.iter().cloned()),
            StatementKind::Reset(q) if !nested => {
                self.quantum.insert(q.clone());
            }
            StatementKind::Measure { qubit, target } if !nested => {
                self.quantum.insert(qubit.clone());
                self.classical.insert(target.clone());
                self.written.insert(target.clone());
                self.pending.insert(target.clone());
                self.measurements += 1;
            }
            StatementKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                if !is_predicable_block(then_branch, plan)
                    || !is_predicable_block(else_branch, plan)
                {
                    self.splits += 1;
                    if self.splits > 3 {
                        return false;
                    }
                }
                self.read(condition);
                for branch in [then_branch, else_branch] {
                    if !branch.classical_registers.is_empty() {
                        return false;
                    }
                    self.discards(plan.discard_set(branch.ast_id), false);
                    for child in &branch.statements {
                        if !self.statement(child, plan, true) {
                            return false;
                        }
                    }
                }
            }
            // Mutable classical inputs, nested measurements/resets and scope
            // boundaries stay with the ordinary executor. No partial summary
            // is guessed for an unsupported control/data-flow interface.
            _ => return false,
        }
        self.discards(plan.discard_set(statement.ast_id), !nested);
        self.operations <= MAX_STATEMENTS && self.quantum.len() <= MAX_WIRES
    }

    fn discards(&mut self, discard: Option<&DiscardSet>, complete_join: bool) {
        if let Some(discard) = discard {
            self.quantum.extend(discard.quantum.iter().cloned());
            self.classical.extend(discard.classical.iter().cloned());
            if complete_join {
                for bit in &discard.classical {
                    self.pending.remove(bit);
                }
            }
        }
    }
}

impl Executor {
    pub(super) fn summarize_region(
        &mut self,
        prefix: &[Component],
        statements: &[Statement],
        plan: &SlicePlan,
    ) -> Option<(usize, Vec<Component>)> {
        if prefix.is_empty() || prefix.len() > MAX_COMPONENTS {
            return None;
        }
        // TODO: Preselect candidate starts by tracing dependencies backwards
        // from each measurement result's last use, rather than retrying
        // overlapping forward windows at every retained statement. Track
        // reaching measurement definitions (not just reused classical names)
        // and all quantum operands, including entangling gates and corrections.
        // Initially keep a contiguous source-order window covering those
        // dependencies; skipping or reordering intervening gates requires an
        // independent commutation proof. Reuse the exact local summary check
        // and ordinary-execution fallback; candidate selection is not a proof.
        let mut boundary = Boundary::default();
        let mut length = None;
        for (index, statement) in statements.iter().take(MAX_STATEMENTS).enumerate() {
            if !boundary.statement(statement, plan, false) {
                return None;
            }
            if boundary.measurements > 0 && boundary.pending.is_empty() {
                length = Some(index + 1);
                break;
            }
        }
        let length = length?;
        let mut memory = HybridMemory::default();
        let mut inputs = Vec::new();
        for wire in &boundary.quantum {
            let first = prefix[0].output.quantum.get(wire);
            if prefix
                .iter()
                .any(|c| c.output.quantum.contains_key(wire) != first.is_some())
            {
                return None;
            }
            if let Some(first) = first {
                let value = if (first.is_zero() || first.is_one())
                    && prefix
                        .iter()
                        .all(|c| c.output.quantum.get(wire) == Some(first))
                {
                    first.clone()
                } else {
                    inputs.push(wire.clone());
                    BooleanPolynomial::variable(Variable::Input(wire.clone()))
                };
                memory.quantum.insert(wire.clone(), value);
            }
        }
        // A symbolic classical parameter needs a shared environment interface,
        // not a free coherent qubit. Until that interface exists, admit only
        // literal constants common to the entire prefix; otherwise fall back.
        for bit in &boundary.reads {
            let value = prefix[0].output.classical.get(bit)?;
            if !(value.is_zero() || value.is_one())
                || prefix
                    .iter()
                    .any(|c| c.output.classical.get(bit) != Some(value))
            {
                return None;
            }
            memory.classical.insert(bit.clone(), value.clone());
        }
        let local = Component {
            guard: vec![],
            scalar: Scalar::one(),
            path_support: BTreeSet::new(),
            phase: PhasePolynomial::zero(),
            output: memory,
        };
        let mut executor = Executor {
            next_path: 0,
            ids: self.ids.clone(),
            boundaries_since_compaction: 0,
            compaction_interval: MIN_COMPACTION_INTERVAL,
            pending_feedback: BTreeSet::new(),
            summarize_regions: false,
        };
        let mut result = vec![local];
        // Check budgets between source statements, including explicit joins.
        for statement in &statements[..length] {
            result = executor
                .execute_statements(result, std::slice::from_ref(statement), plan, true)
                .ok()?;
            if result.len() > MAX_COMPONENTS {
                return None;
            }
        }
        result = compact_components(result, true);
        let [mut summary]: [Component; 1] = result.try_into().ok()?;
        if !summary.output.history.is_empty() || !summary.guard.is_empty() {
            return None;
        }
        // Use disjoint temporary names for ALL bound and boundary variables
        // before inserting any prefix expression (simultaneous substitution).
        let mut next = self.next_path.max(executor.next_path);
        for path in summary.path_support.clone() {
            let fresh = next;
            next = next.checked_add(1)?;
            substitute_component(&mut summary, &Variable::Path(path), &path_value(fresh));
            summary.path_support.insert(fresh);
        }
        let mut replacements = Vec::new();
        for wire in inputs {
            let temporary = next;
            next = next.checked_add(1)?;
            substitute_component(
                &mut summary,
                &Variable::Input(wire.clone()),
                &path_value(temporary),
            );
            replacements.push((wire, temporary));
        }
        let mut composed = Vec::with_capacity(prefix.len());
        for original in prefix {
            let mut instantiated = summary.clone();
            for (wire, temporary) in &replacements {
                let value = &original.output.quantum[wire];
                substitute_component(&mut instantiated, &Variable::Path(*temporary), value);
            }
            let mut component = original.clone();
            component.scalar = component.scalar.multiply(instantiated.scalar);
            component.path_support.extend(instantiated.path_support);
            for (monomial, coefficient) in instantiated.phase.selectors() {
                component.phase.add_boolean(&monomial, coefficient.clone());
            }
            for wire in &boundary.quantum {
                component.output.quantum.remove(wire);
            }
            for bit in &boundary.classical {
                component.output.classical.remove(bit);
            }
            component.output.quantum.extend(instantiated.output.quantum);
            component
                .output
                .classical
                .extend(instantiated.output.classical);
            // Prefix guard/history are untouched. Local history is empty by
            // certificate, not deleted here, and no probability is renormalized.
            composed.push(component);
        }
        self.next_path = next;
        self.ids = executor.ids;
        Some((length, composed))
    }
}

fn path_value(path: usize) -> BooleanPolynomial {
    BooleanPolynomial::variable(Variable::Path(path))
}

#[cfg(test)]
mod tests;
