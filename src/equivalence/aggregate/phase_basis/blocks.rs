//! Adapter to shared phase-block compaction.
use super::*;

pub(super) fn compact(factor: &mut WorkingTerm, work: &mut usize) -> Option<bool> {
    super::super::xor_blocks::compact(factor, work)
}

#[cfg(test)]
mod tests;
