//! Shared gate templates have private AST identities and no mutable storage.
//! Instantiation substitutes only formal parameters/wires, keeps nested calls
//! shared, and assigns fresh program-local identities to the immediate body.
use crate::*;
use std::collections::BTreeMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateDefinition {
    pub name: String,
    pub parameters: Vec<SymbolId>,
    pub qubits: Vec<Qubit>,
    pub body: Block,
}

impl GateDefinition {
    pub fn instantiate(
        &self,
        parameters: &[NumericExpr],
        qubits: &[Qubit],
        ids: &mut AstIdGenerator,
    ) -> Result<Block, String> {
        if parameters.len() != self.parameters.len() || qubits.len() != self.qubits.len() {
            return Err("gate call arity mismatch".into());
        }
        if qubits
            .iter()
            .collect::<std::collections::BTreeSet<_>>()
            .len()
            != qubits.len()
        {
            return Err("aliased gate call operands".into());
        }
        let values = self.parameters.iter().copied().zip(parameters).collect();
        let wires = self
            .qubits
            .iter()
            .cloned()
            .zip(qubits.iter().cloned())
            .collect();
        instantiate_block(&self.body, &values, &wires, ids)
    }
}

fn numeric(
    e: &NumericExpr,
    values: &BTreeMap<SymbolId, &NumericExpr>,
    ids: &mut AstIdGenerator,
) -> NumericExpr {
    use NumericExprKind as N;
    let kind = match &e.kind {
        N::Input(id) if values.contains_key(id) => return ids.clone_numeric_expr(values[id]),
        N::Neg(a) => N::Neg(Box::new(numeric(a, values, ids))),
        N::Add(a, b) | N::Sub(a, b) | N::Mul(a, b) | N::Div(a, b) => {
            let a = Box::new(numeric(a, values, ids));
            let b = Box::new(numeric(b, values, ids));
            match e.kind {
                N::Add(..) => N::Add(a, b),
                N::Sub(..) => N::Sub(a, b),
                N::Mul(..) => N::Mul(a, b),
                _ => N::Div(a, b),
            }
        }
        _ => return ids.clone_numeric_expr(e),
    };
    ids.node(kind)
}

fn instantiate_block(
    body: &Block,
    values: &BTreeMap<SymbolId, &NumericExpr>,
    wires: &BTreeMap<Qubit, Qubit>,
    ids: &mut AstIdGenerator,
) -> Result<Block, String> {
    if !body.classical_registers.is_empty() {
        return Err("classical storage in gate definition".into());
    }
    let wire = |q: &Qubit| {
        wires
            .get(q)
            .cloned()
            .ok_or_else(|| "free quantum wire in gate definition".to_string())
    };
    let mut statements = Vec::new();
    for s in &body.statements {
        use StatementKind as K;
        let kind = match &s.kind {
            K::Apply {
                gate,
                parameters,
                qubits,
            } => K::Apply {
                gate: *gate,
                parameters: parameters.iter().map(|e| numeric(e, values, ids)).collect(),
                qubits: qubits.iter().map(&wire).collect::<Result<_, _>>()?,
            },
            K::GateCall {
                definition,
                parameters,
                qubits,
            } => K::GateCall {
                definition: definition.clone(),
                parameters: parameters.iter().map(|e| numeric(e, values, ids)).collect(),
                qubits: qubits.iter().map(&wire).collect::<Result<_, _>>()?,
            },
            K::GlobalPhase(e) => K::GlobalPhase(numeric(e, values, ids)),
            K::Scope(b) => K::Scope(instantiate_block(b, values, wires, ids)?),
            K::Unitary {
                controls,
                power,
                body,
            } => K::Unitary {
                controls: controls.iter().map(&wire).collect::<Result<_, _>>()?,
                power: *power,
                body: instantiate_block(body, values, wires, ids)?,
            },
            _ => return Err("non-unitary statement in shared gate definition".into()),
        };
        statements.push(ids.node(kind));
    }
    Ok(ids.node(BlockData {
        statements,
        ..BlockData::default()
    }))
}
