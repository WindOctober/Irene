# Quokka-Sharp official opt/gm/flip pairs

923 tasks from the official [artifact repository](https://github.com/System-Verification-Lab/quokka-sharp-artifacts),
pinned at `53777d525719486eba1038901fbef4a8d8d782ce`:

| Subset | opt (expected EQ) | gm (expected NEQ) | flip (expected NEQ) |
| --- | ---: | ---: | ---: |
| algorithm | 102 | 102 | 83 |
| random/randdepscale | 58 | 58 | 51 |
| random/randqubitscale | 57 | 57 | 57 |
| random/uniform | 100 | 100 | 98 |
| Total | 317 | 317 | 289 |

Each task compares the original circuit to one selected variant. Originals are
shared by path rather than duplicated: 1,240 QASM files total. This collection
does not include shift4, shift7, compound flip+gm, or unrelated artifact suites.
Missing variants are listed in the archived `import-report.json`; no nonexistent pairs are
invented. There is no Cartesian-product expansion of circuit variants.

All cases are static, arbitrary-input, full quantum-output unitary comparisons
(global phase irrelevant), not closed zero-input distribution comparisons.
Every quantum input/output is explicitly mapped. Sixty pairs flatten multiple
source registers into a single register; mappings follow PyZX's declaration-order
wire numbering, not matching register names. No rotations, gates, comments or
barriers are semantically rewritten; only UTF-8/LF text normalization is used.

`truth` records the **upstream expected label**, not an independent exact proof:
`opt` uses PyZX optimization; `gm` deletes a gate; `flip` reverses a CX's control
and target. Neither mutation names nor successful import certify NEQ. Numerical
rotation exports can also differ from exact symbolic-angle semantics. Opposite
Irene results must be adjudicated, not automatically called verifier bugs.

Per-case provenance includes matching official result rows where available
(uniform: qubits/depth/seed/modification; algorithm: official algorithm key,
qubit count and modification). These are tool observations, including timeouts,
not a replacement truth oracle. Official result CSVs and generating/path scripts
are preserved with per-case records under
`var/benchmark-sources/import-audits/quokka/provenance/` at the workspace root.
The import report is in the parent `quokka/` audit directory.
No logs are inferred for uncovered cases.

The complete upstream checkout remains at
`var/benchmark-sources/quokka-sharp-artifacts` relative to the workspace root.
Only the selected three variant families enter this benchmark directory; the
raw checkout still contains other upstream data.

Reproduce the import from the workspace root:

```sh
python3 scripts/benchmarks/import_quokka.py
```

Batch entry point (not a claim that the full collection has been run):

```sh
python3 scripts/experiments/run.py --tool irene \
  --manifest Irene/benchmarks/quokka/manifest.toml --timeout 60 --jobs 8
```

Import smoke results for one uniform instance across all three variants are
under `experiments/irene/quokka-import-smoke/` at the workspace root.
