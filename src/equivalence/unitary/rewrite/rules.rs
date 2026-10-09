//! Exact local identities, shared by every candidate-discovery strategy.
//! This module does not scan circuits or decide which gates may be crossed.
use super::*;

/// Coarse candidate shapes use Op::family; exact angles and gate identities
/// are checked below. Port matching and native searches share these hints.
pub(super) const PAIRS: &[Gate] = &[
    Gate::H,
    Gate::X,
    Gate::Y,
    Gate::P,
    Gate::Rx,
    Gate::Ry,
    Gate::Rz,
    Gate::Cx,
    Gate::Cy,
    Gate::Cz,
    Gate::Swap,
    Gate::Cp,
    Gate::Crx,
    Gate::Cry,
    Gate::Crz,
    Gate::Ccx,
    Gate::Ccz,
];
pub(super) const TRIPLES: &[(Gate, Gate, Gate)] = &[
    (Gate::H, Gate::X, Gate::H),
    (Gate::H, Gate::P, Gate::H),
    (Gate::H, Gate::Cx, Gate::H),
    (Gate::H, Gate::Cz, Gate::H),
    (Gate::H, Gate::Ccx, Gate::H),
    (Gate::H, Gate::Ccz, Gate::H),
    (Gate::H, Gate::Rx, Gate::H),
    (Gate::H, Gate::Ry, Gate::H),
    (Gate::H, Gate::Crx, Gate::H),
    (Gate::H, Gate::Cry, Gate::H),
    (Gate::P, Gate::Rx, Gate::P),
    (Gate::Cx, Gate::Cx, Gate::Cx),
];

pub(super) fn can_end_triple(op: &Op) -> bool {
    TRIPLES.iter().any(|&(_, _, last)| op.family() == last)
}

/// Replacement anchor is an index in the selected slice. An absent operation
/// means the selected gates multiply to the exact operator identity.
pub(super) struct Rewrite {
    pub anchor: usize,
    pub operation: Option<Op>,
}

pub(super) fn exact(ops: &[&Op], ids: &mut AstIdGenerator) -> Option<Rewrite> {
    match ops {
        [a, b] if PAIRS.contains(&a.family()) => Some(Rewrite {
            anchor: 0,
            operation: fuse(a, b, ids)?,
        }),
        [a, middle, b] if TRIPLES.contains(&(a.family(), middle.family(), b.family())) => {
            Some(Rewrite {
                anchor: 1,
                operation: Some(
                    conjugate(a, middle, b, ids)
                        .or_else(|| native_h(a, middle, b, ids))
                        .or_else(|| swap(a, middle, b, ids))?,
                ),
            })
        }
        _ => None,
    }
}

/// CX(a,b); CX(b,a); CX(a,b) = SWAP(a,b), with no phase correction.
/// Replace in place; this rule does not propagate a wire permutation.
fn swap(a: &Op, middle: &Op, b: &Op, ids: &mut AstIdGenerator) -> Option<Op> {
    if a.gate != Gate::Cx
        || middle.gate != Gate::Cx
        || b.gate != Gate::Cx
        || a.wires != b.wires
        || a.wires[0] != middle.wires[1]
        || a.wires[1] != middle.wires[0]
    {
        return None;
    }
    Some(Op::from(ids.node(StatementKind::Apply {
        gate: Gate::Swap,
        parameters: vec![],
        qubits: a.wires.clone(),
    })))
}

/// S Rx(pi/2) S = H and its adjoint, including P-form S gates introduced by
/// other rules. Rotation angles use the exact 4pi period, retaining the sign.
/// No rounding of decimal angles or controlled-rotation variant is admitted.
fn native_h(a: &Op, middle: &Op, b: &Op, ids: &mut AstIdGenerator) -> Option<Op> {
    if a.family() != Gate::P
        || b.family() != Gate::P
        || middle.gate != Gate::Rx
        || a.wires != middle.wires
        || a.wires != b.wires
    {
        return None;
    }
    let outer = a.angle.as_ref()?.as_rational()?;
    if b.angle.as_ref()?.as_rational()? != outer {
        return None;
    }
    let rotation = if outer == rational(1, 4) {
        rational(1, 8)
    } else if outer == rational(3, 4) {
        rational(7, 8)
    } else {
        return None;
    };
    if middle.angle.as_ref()?.as_rational()? != rotation {
        return None;
    }
    Some(Op::from(ids.node(StatementKind::Apply {
        gate: Gate::H,
        parameters: vec![],
        qubits: middle.wires.clone(),
    })))
}

/// Outer Option: a valid rule instance. Inner None: exact identity.
fn fuse(a: &Op, b: &Op, ids: &mut AstIdGenerator) -> Option<Option<Op>> {
    if a.family() != b.family() || a.wires != b.wires {
        return None;
    }
    if let (Some(x), Some(y)) = (&a.angle, &b.angle) {
        let mut sum = x.clone();
        sum.add_assign(y.clone());
        let turns = sum.as_rational()?;
        if turns == rational(0, 1) {
            return Some(None);
        }
        let gate = a.family();
        let period = if matches!(gate, Gate::P | Gate::Cp) {
            2
        } else {
            4
        };
        // No general expression-tree growth: emit a single exact multiple of pi.
        let factor = ids.node(NumericExprKind::Rational(turns * rational(period, 1)));
        let pi = ids.node(NumericExprKind::Constant(NumericConstant::Pi));
        let angle = ids.node(NumericExprKind::Mul(Box::new(factor), Box::new(pi)));
        return Some(Some(Op::from(ids.node(StatementKind::Apply {
            gate,
            parameters: vec![angle],
            qubits: a.wires.clone(),
        }))));
    }
    matches!(
        a.gate,
        Gate::H
            | Gate::X
            | Gate::Y
            | Gate::Cx
            | Gate::Cy
            | Gate::Cz
            | Gate::Ccx
            | Gate::Ccz
            | Gate::Swap
    )
    .then_some(None)
}

fn conjugate(h: &Op, middle: &Op, other: &Op, ids: &mut AstIdGenerator) -> Option<Op> {
    if h.gate != Gate::H
        || other.gate != Gate::H
        || h.wires != other.wires
        || h.wires.last() != middle.wires.last()
    {
        return None;
    }
    let gate = match middle.gate {
        Gate::X => Gate::Z,
        Gate::Z => Gate::X,
        Gate::Cx => Gate::Cz,
        Gate::Cz => Gate::Cx,
        Gate::Ccx => Gate::Ccz,
        Gate::Ccz => Gate::Ccx,
        Gate::Rx => Gate::Rz,
        Gate::Crx => Gate::Crz,
        Gate::Ry | Gate::Cry => middle.gate,
        _ => return None,
    };
    let StatementKind::Apply { parameters, .. } = &middle.statement.kind else {
        unreachable!()
    };
    // H conjugates X <-> Z and Y -> -Y. These are operator identities for
    // ANY valid angle, not a claim that a decimal angle is Clifford. Controlled
    // variants change only the target basis and keep their relative phase.
    // Orient X rotations towards Z, not backwards: H Rz H -> Rx would undo
    // the trace backend's phase-only lowering immediately after expansion.
    let parameters = if matches!(middle.gate, Gate::Ry | Gate::Cry) {
        vec![ids.node(NumericExprKind::Neg(Box::new(parameters[0].clone())))]
    } else {
        parameters.clone()
    };
    Some(Op::from(ids.node(StatementKind::Apply {
        gate,
        parameters,
        qubits: middle.wires.clone(),
    })))
}
