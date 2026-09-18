//! Exact decompositions of supported controlled gates.
use super::*;

impl Lowerer {
    pub(super) fn controlled_involution(&mut self, gate: Gate, q: Vec<Qubit>) -> Statement {
        let mut apply = |gate, parameters, qubits| {
            self.ids.node(StatementKind::Apply {
                gate,
                parameters,
                qubits,
            })
        };
        if gate == Gate::Swap {
            // CX(b,a); CCX(c,a,b); CX(b,a), exact including global phase.
            let a = apply(Gate::Cx, vec![], vec![q[2].clone(), q[1].clone()]);
            let b = apply(Gate::Ccx, vec![], q.clone());
            let c = apply(Gate::Cx, vec![], vec![q[2].clone(), q[1].clone()]);
            return self.sequence(vec![a, b, c]);
        }
        assert_eq!(gate, Gate::H);
        // Ry(pi/4) Z Ry(-pi/4) = H. Time order is right-to-left.
        let negative = self.pi_multiple(-1, 4);
        let a = self.ids.node(StatementKind::Apply {
            gate: Gate::Ry,
            parameters: vec![negative],
            qubits: vec![q[1].clone()],
        });
        let b = self.ids.node(StatementKind::Apply {
            gate: Gate::Cz,
            parameters: vec![],
            qubits: q.clone(),
        });
        let positive = self.pi_multiple(1, 4);
        let c = self.ids.node(StatementKind::Apply {
            gate: Gate::Ry,
            parameters: vec![positive],
            qubits: vec![q[1].clone()],
        });
        self.sequence(vec![a, b, c])
    }

    pub(super) fn pi_multiple(&mut self, numerator: i128, denominator: i128) -> NumericExpr {
        let pi = self
            .ids
            .node(NumericExprKind::Constant(crate::ir::NumericConstant::Pi));
        let ratio = self.ids.node(NumericExprKind::Rational(BigRational::new(
            numerator.into(),
            denominator.into(),
        )));
        self.ids
            .node(NumericExprKind::Mul(Box::new(pi), Box::new(ratio)))
    }
}
