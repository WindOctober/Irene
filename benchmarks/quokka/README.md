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
excluded. [manifest.toml](manifest.toml) lists all included pairs.

## Semantics and labels

All pairs compare static unitaries over arbitrary inputs and full quantum outputs,
up to global phase. Sixty pairs flatten multiple registers; their explicit mappings
follow PyZX declaration-order wire numbering. Imports normalize UTF-8/LF text only,
without rewriting gates or angles.

The manifest contains 316 EQ and 607 NEQ cases. The routing-2 opt case is NEQ
under exact source semantics: its decimal radian angles differ from rational
multiples of pi. Numerical equivalence within a tolerance is distinct from
this exact label.

Other labels are upstream expectations: `opt` applies PyZX optimization,
`gm` deletes a gate, and `flip` swaps a CX's control and target. Mutations and
numerical exports do not certify exact EQ/NEQ.

## Included files

`programs/` contains the original circuits and their variants. The manifest
records upstream paths and explicit input/output mappings. Official runtime
observations are separate from truth labels and available from the artifact
repository linked above.

See [using the corpus](../README.md#using-the-corpus) for comparison entry points.
