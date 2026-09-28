# Quokka-Sharp opt/gm/flip pairs

923 tasks from the official [artifact repository](https://github.com/System-Verification-Lab/quokka-sharp-artifacts),
revision `53777d525719486eba1038901fbef4a8d8d782ce`.

| Subset | opt (upstream EQ) | gm (upstream NEQ) | flip (upstream NEQ) |
| --- | ---: | ---: | ---: |
| algorithm | 102 | 102 | 83 |
| random/randdepscale | 58 | 58 | 51 |
| random/randqubitscale | 57 | 57 | 57 |
| random/uniform | 100 | 100 | 98 |
| Total | 317 | 317 | 289 |

Each task pairs an original circuit with one variant. Originals share paths:
1,240 QASM files in total. Shift4, shift7, compound flip+gm and other suites are
excluded; missing variants are listed in the import report.

## Semantics and labels

All pairs compare static unitaries over arbitrary inputs and full quantum outputs,
up to global phase. Sixty pairs flatten multiple registers; their explicit mappings
follow PyZX declaration-order wire numbering. Imports normalize UTF-8/LF text only,
without rewriting gates or angles.

The routing-2 opt label was corrected to NEQ under exact source semantics:
decimal radians differ from rational multiples of pi. Totals after correction:
316 EQ and 607 NEQ. See `BENCHMARK_TRUTH_ERRATA_20260915.md` at the workspace root.

Other labels are upstream expectations: `opt` applies PyZX optimization,
`gm` deletes a gate, and `flip` swaps a CX's control and target. Mutations and
numerical exports do not certify exact EQ/NEQ; disagreements require adjudication.

## Provenance and reproduction

Workspace-relative locations:

- `var/benchmark-sources/quokka-sharp-artifacts/`: upstream checkout, fetched into
  the scratch directory excluded from version control.
- `var/benchmark-sources/import-audits/quokka/import-report.json`: import inventory.
- `var/benchmark-sources/import-audits/quokka/provenance/`: per-case records,
  official CSV observations where available, and generating/path scripts.

Official observations include timeouts and are separate from truth labels.
Run from the workspace root:

```sh
python3 scripts/benchmarks/import_quokka.py
python3 scripts/experiments/run.py --tool irene \
  --manifest Irene/benchmarks/quokka/manifest.toml --timeout 60 --jobs 8
```
