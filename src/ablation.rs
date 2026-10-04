//! Synchronous, thread-local controls for optimization ablation studies.
//!
//! Defaults preserve the normal pipeline. Disabled passes retain their input
//! or decline a sufficient proof; they never establish inequivalence. Parsing,
//! semantic validation, core XAG constructors and exact SMT encoding remain.
//! Scopes restore their caller's configuration even during panic unwinding.
//! A scope does not propagate to newly spawned threads or asynchronous tasks.

use std::{cell::RefCell, fmt, str::FromStr};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(usize)]
pub enum Group {
    GateRewrite,
    FeedbackSummary,
    ExpressionSimplify,
    PathSumPlanning,
}

impl Group {
    pub const ALL: [Self; 4] = [
        Self::GateRewrite,
        Self::FeedbackSummary,
        Self::ExpressionSimplify,
        Self::PathSumPlanning,
    ];
    pub const fn name(self) -> &'static str {
        match self {
            Self::GateRewrite => "gate-rewrite",
            Self::FeedbackSummary => "feedback-summary",
            Self::ExpressionSimplify => "expression-simplify",
            Self::PathSumPlanning => "path-sum-planning",
        }
    }
}

impl FromStr for Group {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::ALL.into_iter().find(|g| g.name() == s).ok_or_else(||
            format!("unknown ablation group {s:?}; expected gate-rewrite, feedback-summary, expression-simplify, path-sum-planning"))
    }
}

/// Four optimization switches; proof routes and basic elimination stay available.
/// Downstream passes may recover proofs lost by an upstream disabled pass.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Config {
    disabled: u8,
}

impl Config {
    pub fn without(groups: impl IntoIterator<Item = Group>) -> Self {
        Self {
            disabled: groups
                .into_iter()
                .fold(0, |mask, g| mask | (1 << g as usize)),
        }
    }
    pub fn enabled(self, group: Group) -> bool {
        self.disabled & (1 << group as usize) == 0
    }
    pub fn disabled(self) -> Vec<Group> {
        Group::ALL
            .into_iter()
            .filter(|g| !self.enabled(*g))
            .collect()
    }
    /// Empty means normal defaults; `all` disables all four optional groups.
    /// Typos and empty list elements are errors, never silent default fallback.
    pub fn parse(value: &str) -> Result<Self, String> {
        if value.trim().is_empty() {
            return Ok(Self::default());
        }
        if value.trim() == "all" {
            return Ok(Self::without(Group::ALL));
        }
        value
            .split(',')
            .map(|s| s.trim().parse())
            .collect::<Result<Vec<_>, _>>()
            .map(Self::without)
    }
    /// Explicit opt-in for process-based runners; the library never implicitly
    /// reads this variable while running an unscoped `analyze` or `execute`.
    pub fn from_env() -> Result<Self, String> {
        match std::env::var("IRENE_ABLATE") {
            Ok(value) => Self::parse(&value),
            Err(std::env::VarError::NotPresent) => Ok(Self::default()),
            Err(e) => Err(format!("invalid IRENE_ABLATE: {e}")),
        }
    }
}

/// Entry-gate counts, NOT rewrite hits, certificates or causal speedups.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Counts {
    pub admitted: u64,
    pub skipped: u64,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Report {
    pub config: Config,
    pub counts: [Counts; 4],
}
impl Report {
    pub fn counts(&self, group: Group) -> Counts {
        self.counts[group as usize]
    }
}
impl fmt::Display for Report {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for group in Group::ALL {
            let c = self.counts(group);
            writeln!(
                f,
                "ablation {} enabled={} admitted={} skipped={}",
                group.name(),
                self.config.enabled(group),
                c.admitted,
                c.skipped
            )?;
        }
        Ok(())
    }
}

thread_local! { static ACTIVE: RefCell<Option<Report>> = const { RefCell::new(None) }; }

struct Restore(Option<Report>);
impl Drop for Restore {
    fn drop(&mut self) {
        ACTIVE.with(|active| {
            active.replace(self.0.take());
        });
    }
}

/// Run any synchronous analysis/execution with these switches and obtain the
/// effective configuration and entry counters, including on a returned error.
/// Nested scopes have independent reports and restore their parent exactly.
pub fn run<T>(config: Config, operation: impl FnOnce() -> T) -> (T, Report) {
    let _restore = Restore(ACTIVE.with(|active| {
        active.replace(Some(Report {
            config,
            counts: [Counts::default(); 4],
        }))
    }));
    let value = operation();
    let report = ACTIVE.with(|active| active.borrow_mut().take().expect("active ablation scope"));
    (value, report)
}

pub(crate) fn permit(group: Group) -> bool {
    ACTIVE.with(|active| {
        let mut active = active.borrow_mut();
        let Some(report) = active.as_mut() else {
            return true;
        };
        let enabled = report.config.enabled(group);
        let c = &mut report.counts[group as usize];
        if enabled {
            c.admitted = c.admitted.saturating_add(1);
        } else {
            c.skipped = c.skipped.saturating_add(1);
        }
        enabled
    })
}

/// Planning-off keeps the supplied stable variable order and does not even
/// evaluate the cost heuristic. The summation itself is unchanged.
pub(crate) fn choose_path<I: Iterator, K: Ord>(
    mut candidates: I,
    cost: impl FnMut(&I::Item) -> K,
) -> Option<I::Item> {
    if permit(Group::PathSumPlanning) {
        candidates.min_by_key(cost)
    } else {
        candidates.next()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn planning_off_uses_fixed_order_without_evaluating_cost() {
        let (selected, report) = run(Config::without([Group::PathSumPlanning]), || {
            choose_path([4, 2, 1].into_iter(), |_| -> usize {
                panic!("cost must not run")
            })
        });
        assert_eq!(selected, Some(4));
        assert_eq!(report.counts(Group::PathSumPlanning).skipped, 1);
        assert_eq!(choose_path([4, 2, 1].into_iter(), |x| *x), Some(1));
    }
    #[test]
    fn strict_parser_and_combinations() {
        assert_eq!(Config::parse("").unwrap(), Config::default());
        assert_eq!(Config::parse("all").unwrap().disabled(), Group::ALL);
        assert_eq!(
            Config::parse("feedback-summary,expression-simplify,feedback-summary")
                .unwrap()
                .disabled(),
            vec![Group::FeedbackSummary, Group::ExpressionSimplify]
        );
        for bad in [
            "unitary",
            "feedback",
            "path-algebra",
            "graph-match",
            "contraction",
            "gate-rewrite,",
            "all,gate-rewrite",
        ] {
            assert!(Config::parse(bad).is_err());
        }
    }
    #[test]
    fn nesting_panic_and_thread_isolation() {
        let (_, outer) = run(Config::without([Group::FeedbackSummary]), || {
            assert!(!permit(Group::FeedbackSummary));
            let (_, inner) = run(Config::default(), || {
                assert!(permit(Group::FeedbackSummary))
            });
            assert_eq!(inner.counts(Group::FeedbackSummary).admitted, 1);
            assert!(
                std::panic::catch_unwind(|| run(Config::default(), || panic!("test"))).is_err()
            );
            assert!(!permit(Group::FeedbackSummary));
            std::thread::spawn(|| assert!(permit(Group::FeedbackSummary)))
                .join()
                .unwrap();
        });
        assert_eq!(outer.counts(Group::FeedbackSummary).skipped, 2);
        assert!(permit(Group::FeedbackSummary));
    }
}
