# Read-only representation statistics

This is a representation-size experiment, not a replacement ANF verifier.
The normal verifier is unchanged. Observation is opt-in and synchronous/thread-local.
It neither calls simplification nor changes any HPS field, proof choice, or ablation
switch. Recording costs time/memory: do not use instrumented runs as performance
measurements, and do not promise identical outcomes under wall-clock limits.

## Collect one trace per pair

```sh
cargo build --release --offline
target/release/irene left.qasm right.qasm \
  --representation-stats /tmp/pair-001.jsonl --representation-stats-every 1
```

Destinations must not already exist. Verdict stdout is unchanged. Statistics write
errors are reported on stderr and leave an incomplete trace, not a changed verdict.
The default sampling interval is 32; use 1 for each executed statement/region
summary, and use the SAME interval for the entire corpus. Final HPS states are
always observed. A summary counts as a checkpoint rather than executing its
replaced statements again. Partial branch and local-proof checkpoints are marked
by the same scope: each snapshot is the active HPS component set, not all resident
states of the entire verifier at once. Kernel-only and native circuit-frontier
proof states are not covered in this version; cases with no HPS checkpoints are
reported as unobserved, not zero-size successes.

For the experiment runner, preserve the existing input/output mapping and other
settings and wrap its existing library call, rather than using the positional CLI
for benchmarks with non-positional mappings:

An existing worker calling `equivalence::analyze` can instead set
`IRENE_REPRESENTATION_STATS=/unique/per-pair/path.jsonl` and
`IRENE_REPRESENTATION_STATS_EVERY=1` in that worker process's environment. Rebuild
the worker against the updated library. No change to its verification inputs or
interface is required. Do not reuse one destination across parallel jobs. An
explicit Session takes precedence. Invalid statistics settings/file destinations
are diagnosed on stderr; they do not change the verification verdict.

Alternatively, use an explicit scope:

```rust,ignore
use irene::symbolic::representation_stats::{Config, Session};
let stats = Session::start(trace_path, Config { every: 1, ..Config::default() })?;
let result = equivalence::analyze(&left, &right, &existing_config);
stats.finish()?;
// Handle `result` using the existing experiment logic.
```

Each checkpoint gathers quantum/classical output expressions, guards, phase
selectors, scalar Select conditions (recursively), and histories. All roots are
traversed together. Pointer identity deduplicates shared nodes across fields and
components. No ANF expansion, graph normalization, or graph cache update is done.
Snapshots use compact three-u64 node records plus u64 edge/root arrays.

## Offline bounded ANF analysis and corpus summary

```sh
python3 scripts/representation_stats.py /path/to/trace-directory \
  --output /tmp/representation-summary.json --table-csv /tmp/representation-table.csv
```

The directory must contain only representation traces, one file per program pair.
The output must be new. No compilation, re-verification, network or third-party
Python package is required. Terms, work, retained monomial memberships and retained
variable occurrences have separate budgets (see `--help`). Run this separately
from benchmark verification. Defaults deliberately stop well before an exhaustive
unbounded expansion; for hard OS memory isolation the analyst can additionally
run this command in an independent cgroup. The 6GB verification limit is not a
reason to invent ANF sizes for failed conversions.

The optional CSV contains exactly one header row and one data row (four columns),
pooled over the complete paired cases, not separate benchmark tables. Its XAG
storage column uses exact packed payload bytes, not the original graph heap.
The JSON retains the paired-case denominator, excluded cases, and buffer capacities.

ANF conversion implements Boolean idempotence and XOR cancellation, not syntactic
term multiplication counts. **Sharing is included:** identical canonical monomials
are interned across all root polynomials, and identical full polynomials share one
descriptor. An unshared model is also reported. The shared model is a packed,
interned ANF model, not a claim about the heap footprint of an `im` persistent
collection; HAMT/trie sharing and allocator overhead require a specific ANF backend.
Sharing is per snapshot, never between cases or checkpoints that did not coexist.

## Storage fields and the small paper table

- `xag_nodes`, `xag_edges`: unique physical graph nodes and their outgoing references.
- `xag_packed_bytes`: exact payload size of compact XAG node/edge/root arrays.
- `xag_buffer_bytes`: actual allocated **capacity bytes of snapshot Vec buffers**.
  This is NOT the original Arc/BTreeSet graph's heap usage, allocator usable size,
  total process RSS, or memory used by conversion workspace. It must not be labeled
  "actual verifier memory". Input-variable identities are inside node records.
- `anf_unique_monomials`, `anf_unique_polynomials`, `anf_variable_occurrences`:
  exact counts for successfully converted, shared root polynomials. Do not call
  monomials "XAG-equivalent nodes".
- `anf_shared_estimated_bytes`: 24 bytes per live variable identity, 16 per unique
  monomial and polynomial descriptor, 8 per monomial-variable occurrence, 8 per
  polynomial-monomial membership, and 8 per output root. Coefficients, phase weights,
  allocator overhead and real-valued arithmetic are excluded from BOTH models.

`summary.mean_per_case_observed_maxima` averages the per-case maxima at the sampled
checkpoints. These are observed representation maxima, NOT whole-process peaks.
XAG and ANF use exactly the same fully captured and fully converted cases; each
representation's maximum may occur at a different checkpoint. The summary also
contains corpus size, paired-complete count, capture truncations, incomplete traces
and ANF budget failures. A killed job lacking an end footer is not complete.
If any recorded checkpoint of a case fails conversion/capture, exclude that case
from BOTH paired means. Never average only its smaller successful snapshots.

A compact two-row table can use columns: `Pairs | XAG nodes | XAG storage |
ANF monomials | ANF storage (est.)`. Use **packed bytes** for the fairest layout
comparison. State the paired-case denominator and omitted-budget count in nearby
text. Do not silently present the subset as the full corpus.

Intermediate ANF term/work limits say only that conversion exceeded its budget.
Future cancellations may shrink the final polynomial, so an exceeded limit does
NOT establish a lower bound on final ANF size or final storage. `null` maxima and
failure statuses are intentional. No extrapolation is used.

## Tests

```sh
cargo test --offline --lib symbolic::boolean::statistics
cargo test --offline --test representation_stats
python3 -B -m unittest discover -s tests/python -p 'test_*.py'
```
