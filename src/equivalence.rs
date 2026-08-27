use std::fmt;

use crate::ir::Program;

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
