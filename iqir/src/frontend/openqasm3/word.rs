//! Fixed-width arithmetic and simultaneous assignment for classical words.
use super::*;

impl Lowerer {
    /// Adds or subtracts modulo 2^width, shared by angle and unsigned words.
    pub(super) fn add_word(
        &mut self,
        left: Vec<ClassicalExpr>,
        right: Vec<ClassicalExpr>,
        subtract: bool,
    ) -> Vec<ClassicalExpr> {
        let n = left.len();
        let mut carry = self.ids.node(ClassicalExprKind::Bool(subtract));
        let mut result = Vec::with_capacity(n);
        for (i, (a, mut b)) in left.into_iter().zip(right).enumerate() {
            if subtract {
                b = self.ids.node(ClassicalExprKind::Not(Box::new(b)));
            }
            // Carry occurs only once in the next-carry expression; don't build
            // an exponentially duplicated Boolean syntax tree.
            let aa = self.clone_classical_expr(&a);
            let bb = self.clone_classical_expr(&b);
            let parity = self.bitwise_scalar(ast::ArithOp::BitXor, a, b);
            let p = self.clone_classical_expr(&parity);
            let c = self.clone_classical_expr(&carry);
            result.push(self.bitwise_scalar(ast::ArithOp::BitXor, parity, c));
            if i + 1 < n {
                let generated = self.bitwise_scalar(ast::ArithOp::BitAnd, aa, bb);
                let propagated = self.bitwise_scalar(ast::ArithOp::BitAnd, p, carry);
                carry = self.bitwise_scalar(ast::ArithOp::BitXor, generated, propagated);
            }
        }
        result
    }

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
