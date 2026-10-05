//! Integer gate powers and a conservative, flow-sensitive known-bit analysis.
//! Gate-generated scopes are not necessarily safe to power gate by gate:
//! (AB)^k is not generally A^k B^k. The caller excludes composite CU for
//! k outside {0, 1} and reduces controlled involutions to parity first.
use super::*;

#[derive(Clone, Default)]
pub(super) struct KnownBits(HashMap<ClassicalBit, bool>);

impl KnownBits {
    fn value(&self, e: &ClassicalExpr) -> Option<bool> {
        fn eval(k: &KnownBits, e: &ClassicalExpr, work: &mut usize, depth: usize) -> Option<bool> {
            *work = work.checked_sub(1)?;
            if depth >= 128 {
                return None;
            }
            Some(match &e.kind {
                ClassicalExprKind::Bool(v) => *v,
                ClassicalExprKind::Bit(b) => *k.0.get(b)?,
                ClassicalExprKind::Not(a) => !eval(k, a, work, depth + 1)?,
                ClassicalExprKind::And(a, b) => {
                    eval(k, a, work, depth + 1)? & eval(k, b, work, depth + 1)?
                }
                ClassicalExprKind::Or(a, b) => {
                    eval(k, a, work, depth + 1)? | eval(k, b, work, depth + 1)?
                }
                ClassicalExprKind::Xor(a, b) => {
                    eval(k, a, work, depth + 1)? ^ eval(k, b, work, depth + 1)?
                }
                ClassicalExprKind::Eq(a, b) => {
                    eval(k, a, work, depth + 1)? == eval(k, b, work, depth + 1)?
                }
            })
        }
        eval(self, e, &mut 65536, 0)
    }

    fn block(&mut self, b: &Block) {
        for s in &b.statements {
            self.statement(s);
        }
        for r in &b.classical_registers {
            for index in 0..r.width {
                self.0.remove(&ClassicalBit {
                    register: r.id,
                    index,
                });
            }
        }
    }

    pub(super) fn statement(&mut self, s: &Statement) {
        match &s.kind {
            StatementKind::Assign { target, value } => {
                if let Some(v) = self.value(value) {
                    self.0.insert(target.clone(), v);
                } else {
                    self.0.remove(target);
                }
            }
            StatementKind::Measure { target, .. } => {
                self.0.remove(target);
            }
            StatementKind::Scope(b) => self.block(b),
            StatementKind::If {
                condition,
                then_branch,
                else_branch,
            } => match self.value(condition) {
                Some(true) => self.block(then_branch),
                Some(false) => self.block(else_branch),
                None => {
                    let mut other = self.clone();
                    self.block(then_branch);
                    other.block(else_branch);
                    self.0.retain(|bit, value| other.0.get(bit) == Some(value));
                }
            },
            StatementKind::Reset(_) | StatementKind::Apply { .. } => {}
        }
    }
}

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

    pub(super) fn known_power(&mut self, expression: Expr) -> Result<i128, FrontendError> {
        if let Ok(v) = self.static_integer(expression.clone(), false) {
            return Ok(v.value);
        }
        let saved = self.ids.clone();
        let value = self.lower_typed_classical_expr(expression.clone());
        self.ids = saved;
        let TypedClassicalExpr::Integer {
            bits, signedness, ..
        } = value?
        else {
            return Err(unsupported!("non-integer gate power", &expression));
        };
        if bits.is_empty() || bits.len() > 64 {
            return Err(unsupported!("gate power width outside 1..64", &expression));
        }
        let known = self
            .known_bits
            .as_ref()
            .expect("pow activates known-bit analysis");
        let mut value = 0_i128;
        for (i, b) in bits.iter().enumerate() {
            let bit = known.value(b).ok_or_else(|| {
                unsupported!("gate power is not statically determined", &expression)
            })?;
            value |= i128::from(bit) << i;
        }
        if signedness == Signedness::Signed && value & (1_i128 << (bits.len() - 1)) != 0 {
            value -= 1_i128 << bits.len();
        }
        Ok(value)
    }

    pub(super) fn pi_multiple(&mut self, numerator: i128, denominator: i128) -> NumericExpr {
        let pi = self
            .ids
            .node(NumericExprKind::Constant(crate::NumericConstant::Pi));
        let ratio = self.ids.node(NumericExprKind::Rational(BigRational::new(
            numerator.into(),
            denominator.into(),
        )));
        self.ids
            .node(NumericExprKind::Mul(Box::new(pi), Box::new(ratio)))
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
