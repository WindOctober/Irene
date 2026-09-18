# Optimization ablation studies

Compare the baseline with four leave-one-out variants. All groups are enabled
by default; enabling a group does not activate otherwise-disabled strategies.

| Group | Disabled enhancements | Retained behavior |
| --- | --- | --- |
| `gate-rewrite` | Circuit cancellation, fusion, commuting rewrites, inverse-composition miter construction and its trace/identity proofs | Direct comparison of the original programs through HPS/kernel |
| `feedback-summary` | Feedback summaries, branch convergence, hidden-history elimination and density merging | Measurement semantics, original histories and coherent amplitude merging |
| `expression-simplify` | XAG factoring/Davio; enhanced coefficient-DAG indicator, context and factoring rules; interval-DAG selector alignment/factoring | Shared graphs, basic identities, exact coefficient arithmetic and complete proof backends |
| `path-sum-planning` | Independent-sum decomposition, factor/guard/region proof grouping, alternative-order search and cost-driven variable selection | Fixed-order elimination, local contraction and complete coherent sums |

Parsing, interface validation, gate semantics, output slicing, Fourier/Omega/vacuous
rules, legal guard substitution, VF2/Exact-HPS, pathwise comparison and
kernel/exact-SMT stay enabled. Limits and tolerances are unchanged.
`all` disables the four groups, not the underlying HPS algebra.

With planning off, table and DAG sums select the first remaining variable in
deterministic set order. Per-variable factor collection remains; disconnected
sum/product subproofs are bypassed. Scheduled Davio uses one fixed order, or is
skipped if expression simplification is also off.

## CLI

Run from the repository root:

```sh
cargo run --release -- left.qasm right.qasm --ablation-report
cargo run --release -- left.qasm right.qasm --ablate expression-simplify --ablation-report
cargo run --release -- left.qasm right.qasm --ablate gate-rewrite,path-sum-planning --ablation-report
cargo run --release -- left.qasm right.qasm --ablate all --ablation-report

IRENE_ABLATE=feedback-summary cargo run --release -- left.qasm right.qasm --ablation-report
```

The CLI flag overrides `IRENE_ABLATE`; an empty value disables no groups.
Only the four group names above and `all` are accepted; unknown names and
malformed lists are errors.

`--ablation-report` prints per-group `enabled`, `admitted` and `skipped` fields
to stderr. Counts track entry-gate checks, not successful rewrites. The Rust
API exposes the effective configuration and counters through `ablation::Report`,
with schema version `ablation::SCHEMA_VERSION = 3`.

Comparable results must use the same ablation schema and group definitions.

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
the CLI reads `IRENE_ABLATE`, while library callers can opt in with `Config::from_env()`.

## Baseline and comparison

The switches apply to `analyze` and to the optional dependency-miter and
interval-HPS APIs when called within the same ablation scope:

- `gate-rewrite` off skips dependency-miter candidates and unitary-trace proofs
  before inverse construction. The original pair goes directly to HPS/kernel;
  no miter interval-identity fallback is invoked.
- Interval DAGs honor `expression-simplify` and `path-sum-planning`.
- Feedback summaries are controlled at symbolic execution boundaries.
- `equivalence/tuning.rs` supplies limits, including 21 million interval steps and
  a 180-second interval deadline.
- Numerical identity bounds are returned by `interval_hps::identity_bound`.
  Callers select a tolerance and account for preprocessing error; these bounds
  do not change the exact verdicts returned by `analyze` or the CLI.

Hold inputs/interfaces, resource limits, solver versions, tolerance and other
switches fixed. Record the build, gate strategy and effective configuration.
Compare verdicts, time and memory across all cases, not just the solved intersection;
keep Unknown and resource failures separate from exact and approximate results.
Use repeated same-host runs for timing comparisons.

Group effects interact: summaries use expression rewriting, and early trace proofs
can bypass kernel passes. Use paired ablations to investigate interactions.
The `gate-rewrite` group measures the complete miter strategy, including its
proof routes. The other groups retain their underlying proof backends.
