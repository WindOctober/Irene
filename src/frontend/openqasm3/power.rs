//! Exact controlled decompositions, inverses and literal integer powers.
//! Composite CU must not distribute a nontrivial power through its decomposition.
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

    /// Literal exponents only; typed constant propagation is handled separately.
    pub(super) fn known_power(&mut self, expression: Expr) -> Result<i128, FrontendError> {
        fn literal(expression: Expr, depth: usize) -> Result<i128, FrontendError> {
            if depth >= 64 {
                return Err(unsupported!("integer power expression depth", &expression));
            }
            match expression {
                Expr::Literal(token) => {
                    let ast::LiteralKind::IntNumber(number) = token.kind() else {
                        return Err(expected!("an integer power literal", &token));
                    };
                    if number.to_string().len() > 128 {
                        return Err(unsupported!("integer power literal budget", &token));
                    }
                    u64::try_from(exact_integer_value(number)?)
                        .map(i128::from)
                        .map_err(|_| expected!("an integer power literal at most 64 bits", &token))
                }
                Expr::ParenExpr(paren) => literal(
                    paren
                        .expr()
                        .ok_or_else(|| expected!("an integer power", &paren))?,
                    depth + 1,
                ),
                Expr::PrefixExpr(prefix) if matches!(prefix.op_kind(), Some(ast::UnaryOp::Neg)) => {
                    literal(
                        prefix
                            .expr()
                            .ok_or_else(|| expected!("an integer power", &prefix))?,
                        depth + 1,
                    )?
                    .checked_neg()
                    .ok_or_else(|| unsupported!("integer power overflow", &prefix))
                }
                other => Err(unsupported!("nonliteral integer power", &other)),
            }
        }
        literal(expression, 0)
    }

    /// Lowered single-gate broadcasts, and commuting angle-bit rotations only.
    /// Composite gate decompositions require the caller's admission checks;
    /// a gate-generated Scope by itself does not imply commutativity.
    /// Allocate fresh IDs after resetting the discarded lowering scratch IDs.
    pub(super) fn power_statement(&mut self, s: Statement, k: i128) -> Statement {
        match s.kind {
            StatementKind::Apply {
                mut gate,
                parameters,
                qubits,
            } => {
                let parameters = match gate {
                    Gate::P
                    | Gate::Rx
                    | Gate::Ry
                    | Gate::Rz
                    | Gate::Cp
                    | Gate::Crx
                    | Gate::Cry
                    | Gate::Crz => {
                        parameters
                            .iter()
                            .map(|p| {
                                let p = self.ids.clone_numeric_expr(p);
                                if k == 1 {
                                    return p;
                                }
                                let scale = self.ids.node(NumericExprKind::Rational(
                                    BigRational::from_integer(k.into()),
                                ));
                                // Retain even zero*parameter for pre-algebra domain
                                // validation; pow(0) cannot hide a bad denominator.
                                self.ids
                                    .node(NumericExprKind::Mul(Box::new(p), Box::new(scale)))
                            })
                            .collect()
                    }
                    Gate::S | Gate::Sdg | Gate::T | Gate::Tdg => {
                        let (period, sign) = match gate {
                            Gate::S => (4, 1),
                            Gate::Sdg => (4, -1),
                            Gate::T => (8, 1),
                            Gate::Tdg => (8, -1),
                            _ => unreachable!(),
                        };
                        let residue = (k.rem_euclid(period) * sign).rem_euclid(period);
                        if residue == 0 {
                            return self.sequence(vec![]);
                        }
                        gate = Gate::P;
                        vec![self.pi_multiple(residue, period / 2)]
                    }
                    Gate::H
                    | Gate::X
                    | Gate::Y
                    | Gate::Z
                    | Gate::Cx
                    | Gate::Cy
                    | Gate::Cz
                    | Gate::Swap
                    | Gate::Ccx
                    | Gate::Ccz => {
                        if k.rem_euclid(2) == 0 {
                            return self.sequence(vec![]);
                        }
                        vec![]
                    }
                };
                self.ids.node(StatementKind::Apply {
                    gate,
                    parameters,
                    qubits,
                })
            }
            StatementKind::Scope(b) => {
                assert!(
                    b.classical_registers.is_empty(),
                    "only a gate-generated scope can be powered"
                );
                let statements = b
                    .kind
                    .statements
                    .into_iter()
                    .map(|s| self.power_statement(s, k))
                    .collect();
                self.sequence(statements)
            }
            StatementKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let condition = self.clone_classical_expr(&condition);
                let mut block = |b: Block| {
                    assert!(b.classical_registers.is_empty());
                    let statements = b
                        .kind
                        .statements
                        .into_iter()
                        .map(|s| self.power_statement(s, k))
                        .collect();
                    self.ids.node(BlockData {
                        classical_registers: vec![],
                        statements,
                    })
                };
                let then_branch = block(then_branch);
                let else_branch = block(else_branch);
                self.ids.node(StatementKind::If {
                    condition,
                    then_branch,
                    else_branch,
                })
            }
            _ => unreachable!("only unitary gate lowering can be powered"),
        }
    }
}
