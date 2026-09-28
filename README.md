# Irene

Irene checks equivalence of hybrid quantum programs in supported subsets of
OpenQASM 2 and 3, including measurement, reset, and classical feedback.
It reports equivalence, non-equivalence, or an inconclusive result; unsupported
features and invalid inputs may produce errors.

This source-only release includes benchmark inputs and data-generation code,
not historical results, campaign archives, paper figures, or published-table
audits. The instructions generate new measurements for this checkout; they
do not guarantee historical numerical results.

## Build and run

Use Linux for the runners, Rust 1.91 or newer, a C/C++ toolchain (including
make and m4), and Python 3.11 or newer. From the repository root:

```sh
cargo build --release --locked
cargo build --release --locked --manifest-path tools/irene-experiment-worker/Cargo.toml
python3 -m venv envs/runner
envs/runner/bin/python -m pip install psutil tomli
target/release/irene left.qasm right.qasm
```

Both files must use the same OpenQASM major version. Install Bitwuzla, Z3,
and cvc5 on PATH for SMT-backed routes; missing solvers can leave checks
inconclusive. Record solver versions. See [architecture](docs/architecture.md)
and [language support](docs/language-support.md).

## Generate benchmark data

See [benchmarks](benchmarks/README.md) for inputs and provenance. Use the
manifest-based worker to preserve input and observable-output correspondences.

The runner works from both Git checkouts and anonymous source archives.
No compatibility symlink or Git initialization is required. When Git metadata
is absent, results record `source-archive` rather than inventing a revision.

Start with a small collection:

```sh
envs/runner/bin/python scripts/experiments/run.py --tool irene \
  --manifest benchmarks/qubit-reuse/manifest.toml \
  --collection irene-full-qubit-reuse \
  --jobs 1 --timeout 600 --memory-gib 6 --reserve-memory-gib 2
```

Generate the full Irene dataset across the seven evaluation manifests:

```sh
for suite in sqbricks sqbricks/generated openqasm3-programs qubit-reuse itertestq caqr quokka; do
  collection=$(printf '%s' "$suite" | tr / -)
  envs/runner/bin/python scripts/experiments/run.py --tool irene \
    --manifest "benchmarks/$suite/manifest.toml" \
    --collection "irene-full-$collection" \
    --jobs 1 --timeout 600 --memory-gib 6 --reserve-memory-gib 2
done
```

Per-case results, stdout/stderr, JSONL records, and summaries are generated
under experiments/irene/<collection>/; temporary jobs go under var/experiments/.
Completed cases may be reused. Use new collection names or a fresh clone for
different builds/settings. Do not commit generated data.
Generated directories are ignored by Git. Runner records use repository-relative
paths and omit hostnames; runtime tools still resolve paths locally. Review
third-party diagnostics before publishing newly generated logs.

Choose concurrency and reserved memory for your machine. These sequential
commands are not the historical campaign scheduler. For timing comparisons,
hold hardware, OS, solvers, resource enforcement, concurrency, and interfaces
fixed across arms. Record actual versions, source revision, and commands.
Keep exact and certified approximate results, Unknown, errors, and resource
failures distinct.

## Generate ablation data

Use the same worker and change only IRENE_ABLATE, with a separate collection:

```sh
IRENE_ABLATE=expression-simplify envs/runner/bin/python scripts/experiments/run.py \
  --tool irene --manifest benchmarks/qubit-reuse/manifest.toml \
  --collection irene-without-expression-simplify-qubit-reuse \
  --jobs 1 --timeout 600 --memory-gib 6 --reserve-memory-gib 2
```

Repeat across the seven manifests for gate-rewrite, feedback-summary,
expression-simplify, and path-sum-planning. Unset IRENE_ABLATE for full Irene.
This source uses the schema-2 groups in [docs/ablation.md](docs/ablation.md):
gate-rewrite retains the miter proof route. It is not interchangeable with
a different ablation build that also removes that route.

## Generate representation measurements

After building the worker, use a new label for each campaign:

```sh
envs/runner/bin/python scripts/experiments/run_representation_campaign.py \
  --root . --label representation-local --jobs 1 \
  --timeout 600 --analysis-timeout 600
```

Traces and analysis go under experiments/campaigns/<label>/. These measure
HPS Boolean-expression checkpoints, not total process memory or ANF-backend
runtime. Retain incomplete-capture and expansion-budget flags. The explicit
expansion analyzer is scripts/representation_stats.py; historical ZDD recount
data and paper plots are not included.

## Baseline adapters

scripts/experiments/workers/ contains QCEC, VeriQC, SQbricks, QuPRS, and Quokka
adapters. Install third-party tools and environments separately at chosen
upstream revisions. worker_command() in scripts/experiments/run.py specifies
expected paths for QCEC, VeriQC, and SQbricks; use their --tool values with
the collection runner. QuPRS/Quokka have separate JSON-job adapters and are
not options of that runner.

Available Git revisions are read from the actual tool checkouts; installations
without Git metadata are labelled `source-archive`. Record package and solver
versions separately. This release does not claim a fully provisioned historical
six-tool environment.

## Development

```sh
cargo test --release --locked
cargo test --release --locked --manifest-path tools/irene-experiment-worker/Cargo.toml
```

These are software regression tests, not published-result audits.
Benchmark import/materialization utilities are in scripts/benchmarks/.
