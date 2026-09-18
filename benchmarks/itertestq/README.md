# IterTestQ static-unitary pairs

Source: [official repository](https://github.com/sola-st/IterTestQ-quantum-platform-testing),
commit `1ee07b1abf2ca0f4b19eb8dd1b158c9f008dda21`, and
[Figshare artifact v1](https://doi.org/10.6084/m9.figshare.33016415.v1), CC BY 4.0.
The Figshare artifact contains the complete upstream source archive.

The archive contains 134,607 comparison JSON records, of which 126,116 have
explicit `equivalent`, `equivalent_up_to_global_phase`, or `not_equivalent`
QCEC labels. No label is inferred from a shared generated-program class,
and timeout/error/no-information results are not relabeled NEQ.

The manifest contains 180 pairs (120 EQ, 60 NEQ). Selection is
deterministic: the first two distinct directed source pairs, in sorted source
record order, per `(experiment version, exact QCEC label, left platform,
right platform)` after interface filtering. There are 33,590 eligible unique
static pairs in the source archive.

Only measurement/reset/condition/opaque-free OpenQASM 2 sources with identical
ordered quantum-register interfaces and standard includes are selected.
Every quantum input and output is paired explicitly; these are arbitrary-input
unitary comparisons, not zero-input output-distribution tests. Custom gate
declarations are preserved, including those outside Irene's supported subset.
No gate expansion, float-to-pi rounding, or other semantic rewrite is applied.

QCEC labels are numerical upstream reference results, not exact mathematical
ground truth under Irene's decimal-angle semantics. Label agreement depends on
the comparison semantics and numerical tolerance.
The original QCEC string, run-scoped seven-digit equivalence class, program
paths and comparison-record path are retained in the manifest per case.

The selected program pairs are in `programs/`, with their interfaces and labels
in [manifest.toml](manifest.toml). See [using the corpus](../README.md#using-the-corpus)
for comparison entry points.
