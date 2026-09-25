//! Adapter to complete phase-period elimination.
use super::*;

pub(super) fn compact(source: &mut WorkingTerm, work: &mut usize) -> Option<bool> {
    super::super::pair_period::compact(source, work)
}

#[cfg(test)]
mod tests;
