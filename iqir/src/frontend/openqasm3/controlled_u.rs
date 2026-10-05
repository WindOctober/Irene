//! Four-parameter stdgates.inc CU, including the controlled global phase.
use super::*;

impl Lowerer {
    pub(super) fn lower_standard_cu(
        &mut self,
        call: ast::GateCallExpr,
        controls: usize,
    ) -> Result<Statement, FrontendError> {
        let binding = self.scopes.lookup("cu").map_err(scope_error)?;
        if !matches!(binding.kind, BindingKind::Gate) {
            return Err(expected!("standard cu gate", &call));
        }
        if controls != 0 {
            return Err(unsupported!("additional controls on cu", &call));
        }
        let parameters = call
            .arg_list()
            .and_then(|a| a.expression_list())
            .map(|a| a.exprs().collect::<Vec<_>>())
            .unwrap_or_default();
        if parameters.len() != 4 {
            return Err(expected!("four cu parameters", &call));
        }
        let operands = call
            .qubit_list()
            .ok_or_else(|| expected!("cu operands", &call))?
            .gate_operands()
            .map(|q| self.lower_qubits(q))
            .collect::<Result<Vec<_>, _>>()?;
        if operands.len() != 2 {
            return Err(expected!("two cu operands", &call));
        }
        let mut widths = operands.iter().filter_map(|q| match q {
            QuantumOperand::Scalar(_) => None,
            QuantumOperand::Register(q) => Some(q.len()),
        });
        let width = widths.next().unwrap_or(1);
        if widths.any(|w| w != width) {
            return Err(expected!("equal-width cu registers", &call));
        }
        let mut statements = Vec::new();
        for i in 0..width {
            let c = operands[0].broadcast_at(i);
            let t = operands[1].broadcast_at(i);
            if c == t {
                return Err(expected!("distinct cu operands", &call));
            }
            let theta = self.lower_numeric_expr(parameters[0].clone())?;
            let phi = self.lower_numeric_expr(parameters[1].clone())?;
            let lambda = self.lower_numeric_expr(parameters[2].clone())?;
            let gamma = self.lower_numeric_expr(parameters[3].clone())?;
            let phi_copy = self.ids.clone_numeric_expr(&phi);
            let lambda_copy = self.ids.clone_numeric_expr(&lambda);
            let sum = self.ids.node(NumericExprKind::Add(
                Box::new(phi_copy),
                Box::new(lambda_copy),
            ));
            let two = self
                .ids
                .node(NumericExprKind::Rational(BigRational::from_integer(
                    2.into(),
                )));
            let half = self
                .ids
                .node(NumericExprKind::Div(Box::new(sum), Box::new(two)));
            let phase = self
                .ids
                .node(NumericExprKind::Add(Box::new(gamma), Box::new(half)));
            // U(theta,phi,lambda) = exp(i*(phi+lambda)/2) Rz(phi) Ry(theta) Rz(lambda).
            // gamma becomes a phase on the control, NOT a discardable global phase.
            for (gate, parameters, qubits) in [
                (Gate::P, vec![phase], vec![c.clone()]),
                (Gate::Crz, vec![lambda], vec![c.clone(), t.clone()]),
                (Gate::Cry, vec![theta], vec![c.clone(), t.clone()]),
                (Gate::Crz, vec![phi], vec![c, t]),
            ] {
                statements.push(self.ids.node(StatementKind::Apply {
                    gate,
                    parameters,
                    qubits,
                }));
            }
        }
        Ok(self.sequence(statements))
    }
}
