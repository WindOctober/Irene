use std::fmt;

use crate::ir::{Program, Qubit};

mod canonical;
mod interface;

pub use interface::{
    Endpoint, EquivalenceConfig, InputPair, InterfaceError, NumericInputPair, OutputPair,
    PreparedComparison, PreparedOutput, PreparedOutputKind, PreparedSide, PreparedTerminal, Side,
    UnsupportedInterface, prepare_comparison,
};

fn qubits(program: &Program) -> Vec<Qubit> {
    program
        .quantum_registers
        .iter()
        .flat_map(|register| {
            (0..register.width).map(|index| Qubit {
                register: register.id,
                index,
            })
        })
        .collect()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    Equivalent,
    NotEquivalent,
    Unknown,
}

impl fmt::Display for Verdict {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let text = match self {
            Self::Equivalent => "equivalent",
            Self::NotEquivalent => "not-equivalent",
            Self::Unknown => "unknown",
        };
        formatter.write_str(text)
    }
}

pub fn analyze(_left: &Program, _right: &Program) -> Verdict {
    todo!("equivalence analysis")
}
