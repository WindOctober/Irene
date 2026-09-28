//! Resource limits for proof search; none changes the accepted semantics.
//!
//! The defaults were screened on closed traces and open symbolic kernels
//! separately. Wider symbolic tables can make the eventual SMT query harder.
use std::sync::OnceLock;

pub(crate) struct Limits {
    pub width: usize,
    pub symbolic_width: usize,
    pub cells: usize,
    pub exact_work: usize,
    pub probe_work: usize,
    pub schedule_work: usize,
    pub interval_work: usize,
    pub interval_seconds: u64,
    pub solver_seconds: u64,
    pub coefficient_work: usize,
    pub coefficient_nodes: usize,
    pub context_work: usize,
}

pub(crate) fn limits() -> &'static Limits {
    static LIMITS: OnceLock<Limits> = OnceLock::new();
    LIMITS.get_or_init(|| {
        fn n(key: &str, default: usize) -> usize {
            match std::env::var(key) {
                Ok(v) => v
                    .parse::<usize>()
                    .ok()
                    .filter(|v| *v > 0)
                    .unwrap_or_else(|| panic!("invalid positive resource limit {key}={v}")),
                Err(std::env::VarError::NotPresent) => default,
                Err(e) => panic!("invalid resource limit {key}: {e}"),
            }
        }
        Limits {
            width: n("IRENE_TUNE_WIDTH", 12),
            symbolic_width: n("IRENE_TUNE_SYMBOLIC_WIDTH", 6),
            cells: n("IRENE_TUNE_CELLS", 16_384),
            exact_work: n("IRENE_TUNE_EXACT_WORK", 8_000_000),
            probe_work: n("IRENE_TUNE_PROBE_WORK", 200_000),
            schedule_work: n("IRENE_TUNE_SCHEDULE_WORK", 1_000_000),
            // 21M retains the extra proof found at 24M/32M with substantially
            // fewer process-memory refusals. Use 20M for the conservative tier.
            interval_work: n("IRENE_TUNE_INTERVAL_WORK", 21_000_000),
            interval_seconds: n("IRENE_TUNE_INTERVAL_SECONDS", 180) as u64,
            solver_seconds: n("IRENE_TUNE_SOLVER_SECONDS", 30) as u64,
            coefficient_work: n("IRENE_TUNE_COEFFICIENT_WORK", 8_000_000),
            coefficient_nodes: n("IRENE_TUNE_COEFFICIENT_NODES", 800_000),
            context_work: n("IRENE_TUNE_CONTEXT_WORK", 120_000),
        }
    })
}
