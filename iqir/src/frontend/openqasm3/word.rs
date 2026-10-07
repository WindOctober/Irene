//! Simultaneous assignment for classical words lowered to bit operations.
use super::*;

impl Lowerer {
    /// Scalar writes suffice unless an RHS reads a different destination bit.
    pub(super) fn assign_cells(
        &mut self,
        targets: Vec<ClassicalBit>,
        values: Vec<ClassicalExpr>,
    ) -> Statement {
        let destinations: BTreeSet<_> = targets.iter().cloned().collect();
        fn cross_read(
            e: &ClassicalExpr,
            own: &ClassicalBit,
            destinations: &BTreeSet<ClassicalBit>,
        ) -> bool {
            match &e.kind {
                // Numeric scalar reads never alias Boolean word destinations.
                ClassicalExprKind::ScalarCompare { .. } => false,
                ClassicalExprKind::Bool(_) => false,
                ClassicalExprKind::Bit(b) => b != own && destinations.contains(b),
                ClassicalExprKind::Not(a) => cross_read(a, own, destinations),
                ClassicalExprKind::And(a, b)
                | ClassicalExprKind::Or(a, b)
                | ClassicalExprKind::Xor(a, b)
                | ClassicalExprKind::Eq(a, b) => {
                    cross_read(a, own, destinations) || cross_read(b, own, destinations)
                }
            }
        }
        if targets
            .iter()
            .zip(&values)
            .any(|(t, v)| cross_read(v, t, &destinations))
        {
            return self.assign_word(targets, values);
        }
        let statements = targets
            .into_iter()
            .zip(values)
            .map(|(target, value)| self.ids.node(StatementKind::Assign { target, value }))
            .collect();
        self.sequence(statements)
    }
    /// Evaluate every RHS before writing any destination. The scoped temporary
    /// word is not an observable program output.
    pub(super) fn assign_word(
        &mut self,
        targets: Vec<ClassicalBit>,
        values: Vec<ClassicalExpr>,
    ) -> Statement {
        self.scopes.enter(ScopeKind::Block);
        let binding = self
            .scopes
            .declare(
                "$word_snapshot",
                BindingKind::ClassicalBit(BitType::Register {
                    width: targets.len(),
                }),
            )
            .expect("fresh scope");
        self.scopes.exit();
        let register = self.ids.node(RegisterData {
            id: binding.id,
            name: "$word_snapshot".into(),
            width: targets.len(),
        });
        let temps = bit_operand(
            binding.id,
            BitType::Register {
                width: targets.len(),
            },
        )
        .into_cells();
        let mut statements: Vec<_> = temps
            .iter()
            .cloned()
            .zip(values)
            .map(|(target, value)| self.ids.node(StatementKind::Assign { target, value }))
            .collect();
        for (target, temp) in targets.into_iter().zip(temps) {
            let value = self.ids.node(ClassicalExprKind::Bit(temp));
            statements.push(self.ids.node(StatementKind::Assign { target, value }));
        }
        let block = self.ids.node(BlockData {
            classical_registers: vec![register],
            statements,
        });
        self.ids.node(StatementKind::Scope(block))
    }
}
