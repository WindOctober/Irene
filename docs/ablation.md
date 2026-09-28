# Optimization ablation studies

Compare the baseline with four leave-one-out variants. All groups are enabled
by default; enabling a group does not activate otherwise-disabled strategies.

| Group | Disabled enhancements | Retained behavior |
| --- | --- | --- |
| `gate-rewrite` | Circuit cancellation, fusion and commuting rewrites | Unitary admission, miter construction, trace/identity proofs and HPS execution |
| `feedback-summary` | Feedback summaries, branch convergence, hidden-history elimination and density merging | Measurement semantics, original histories and coherent amplitude merging |
| `expression-simplify` | XAG factoring/Davio; enhanced coefficient-DAG indicator, context and factoring rules; interval-DAG selector alignment/factoring | Shared graphs, basic identities, exact coefficient arithmetic and complete proof backends |
| `path-sum-planning` | Independent-sum decomposition, factor/guard/region proof grouping, alternative-order search and cost-driven variable selection | Fixed-order elimination, local contraction and complete coherent sums |

Parsing, interface validation, gate semantics, output slicing, Fourier/Omega/vacuous
rules, legal guard substitution, VF2/Exact-HPS, pathwise comparison, unitary trace,
kernel/exact-SMT and interval routes stay enabled. Limits and tolerances are unchanged.
`all` disables the four enhancement groups, not all algebra or proof backends.

With planning off, table and DAG sums select the first remaining variable in
deterministic set order. Per-variable factor collection remains; disconnected
sum/product subproofs are bypassed. Scheduled Davio uses one fixed order, or is
skipped if expression simplification is also off.

## CLI and worker

```sh
irene left.qasm right.qasm --ablation-report
irene left.qasm right.qasm --ablate expression-simplify --ablation-report
irene left.qasm right.qasm --ablate gate-rewrite,path-sum-planning --ablation-report
irene left.qasm right.qasm --ablate all --ablation-report

IRENE_ABLATE=feedback-summary tools/irene-experiment-worker/target/release/irene-experiment-worker case.json
```

The CLI flag overrides `IRENE_ABLATE`; an empty value disables no groups.
Unknown names, malformed lists and the legacy names `unitary`, `feedback`,
`path-algebra`, `graph-match`, `contraction` are errors.

Worker output includes `ablation.schema_version: 2`, the effective `disabled`
list, and per-group `enabled`, `admitted`, `skipped` fields. Counts track
entry-gate checks, not successful rewrites. Retain the requested profile in campaign
configuration because externally killed jobs may produce no report.

## Rust API

Wrap the complete synchronous operation:

```rust,ignore
use irene::ablation::{self, Config, Group};
let (answer, report) = ablation::run(
    Config::without([Group::ExpressionSimplify, Group::PathSumPlanning]),
    || irene::equivalence::analyze(&left, &right, &interface),
);
```

Scopes are thread-local, nestable and restored on unwind. They cover synchronous
analysis and identity-bound calls, but are not inherited by new threads or async
tasks. Wrap each analysis in its worker thread. Unscoped library calls use defaults;
only CLI and worker entry points read environment settings.

## Baseline and comparison

The standard worker includes tuned dependency-miter and interval-HPS processing:

- `gate-rewrite` off retains the unmodified miter and its HPS/kernel route.
- Interval DAGs honor `expression-simplify` and `path-sum-planning`.
- Feedback summaries are controlled at symbolic execution boundaries.
- `equivalence/tuning.rs` supplies limits, including 21 million interval steps and
  a 180-second interval deadline.
- The default channel diamond-distance tolerance is 1e-12. Certified tolerance
  results are `approx_eq`, separate from exact `eq` and `neq`.
- An inconclusive reduced-miter proof does not restart the original program pair.

Hold inputs/interfaces, resource limits, solver versions, tolerance and other
switches fixed. Record the build, gate strategy and effective configuration.
Compare verdicts, time and memory across all cases, not just the solved intersection;
keep Unknown and resource failures separate from exact and approximate results.
Use repeated same-host runs for timing comparisons.

Group effects interact: summaries use expression rewriting, and early trace proofs
can bypass kernel passes. Use paired ablations to investigate interactions.
Removing proof backends or lemmas is a separate experiment.
