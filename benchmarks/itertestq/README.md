# IterTestQ: first-pass static-unitary selection

Source: [official repository](https://github.com/sola-st/IterTestQ-quantum-platform-testing),
commit `1ee07b1abf2ca0f4b19eb8dd1b158c9f008dda21`, and
[Figshare artifact v1](https://doi.org/10.6084/m9.figshare.33016415.v1), CC BY 4.0.
The full 357,649,414-byte archive is at
`var/benchmark-sources/itertestq-artifact.zip`; `var/benchmark-sources/` is a scratch
directory excluded from version control.
It contains 352,461 ZIP entries and 2,440,311,363 uncompressed bytes.

All 134,607 comparison JSON records were inventoried. Of these, 126,116 have
explicit `equivalent`, `equivalent_up_to_global_phase`, or `not_equivalent`
QCEC labels. No label is inferred from a shared generated-program class,
and timeout/error/no-information results are not relabeled NEQ.

The first-pass manifest contains 180 pairs (120 EQ, 60 NEQ). Selection is
deterministic: the first two distinct directed source pairs, in sorted source
record order, per `(experiment version, exact QCEC label, left platform,
right platform)` after interface filtering. There are 33,590 eligible unique
static pairs; the other eligible pairs have **not** been batch-tested here.

Only measurement/reset/condition/opaque-free OpenQASM 2 sources with identical
ordered quantum-register interfaces and standard includes are selected.
Every quantum input and output is paired explicitly; these are arbitrary-input
unitary comparisons, not zero-input output-distribution tests. Custom gate
declarations are preserved even when the current Irene frontend rejects them.
No gate expansion, float-to-pi rounding, or other semantic rewrite is applied.

QCEC labels are numerical upstream reference results, **not exact mathematical
ground truth under Irene's decimal-angle semantics**. A future opposite verdict
requires adjudication; it must not automatically be called an Irene bug.
The original QCEC string, run-scoped seven-digit equivalence class, program
paths and comparison-record path are retained in the manifest per case.
Full provenance trees and `import-report.json` are archived under
`var/benchmark-sources/import-audits/itertestq/`, written by the import script above.
The complete full-artifact inventory (including excluded records) is at
`var/benchmark-sources/itertestq-inventory.jsonl`, written by the import script above.

Reproduce from the workspace root:

```sh
python3 scripts/benchmarks/import_itertestq.py
python3 scripts/experiments/run.py --tool irene \
  --manifest Irene/benchmarks/itertestq/manifest.toml --timeout 10 --jobs 8
```

The runner resumes existing results. Changing a selection requires a new result
collection to avoid reusing old case IDs. The raw archive is the authoritative
source for all excluded and unselected programs and logs.
