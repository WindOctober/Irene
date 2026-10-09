//! External users construct IQIR directly; IreneQ consumes the same types.
use iqir::{
    AstIdGenerator, BlockData, Gate, OpenQasmVersion, Program, ProgramData, Qubit, RegisterData,
    StatementKind, SymbolId,
};
use irene::equivalence::{EquivalenceConfig, Verdict, analyze};

fn program(gates: &[Gate]) -> Program {
    let mut ids = AstIdGenerator::default();
    let register = ids.node(RegisterData {
        id: SymbolId(0),
        name: "q".into(),
        width: 1,
    });
    let statements = gates
        .iter()
        .map(|&gate| {
            ids.node(StatementKind::Apply {
                gate,
                parameters: vec![],
                qubits: vec![Qubit {
                    register: SymbolId(0),
                    index: 0,
                }],
            })
        })
        .collect();
    let body = ids.node(BlockData {
        classical_registers: vec![],
        statements,
    });
    ids.node(ProgramData {
        annotations: Default::default(),
        spec_functions: Vec::new(),
        version: OpenQasmVersion { major: 3, minor: 0 },
        numeric_inputs: vec![],
        quantum_registers: vec![register],
        classical_registers: vec![],
        body,
    })
}

#[test]
fn independently_constructed_iqir_programs_are_verified_without_a_frontend() {
    let identity: irene::ir::Program = program(&[]);
    for (gates, expected) in [
        (vec![Gate::H, Gate::H], Verdict::Equivalent),
        (vec![Gate::X], Verdict::NotEquivalent),
    ] {
        let source = program(&gates);
        let config = EquivalenceConfig::positional(&source, &identity).unwrap();
        assert_eq!(
            analyze(&source, &identity, &config).unwrap().verdict,
            expected
        );
    }
}
