# SQbricks source

This source contains 242 tasks and 438 deduplicated programs from the explicit
SQbricks pair lists:

- `sanity-unit`: 42 `neq` cases under unitary equivalence;
- `sanity-hybrid`: 21 `neq` cases under hybrid equivalence;
- `sanity-partial`: 9 `neq` cases under partial/discard equivalence;
- `unit-vs-hybrid`: 170 `eq` cases under hybrid equivalence.

The programs come from Qbricks artifact commit
`e00fc97f14fb9fcbc44bbfbc5e5ec3e483f87367`. The path hierarchy preserves the
original benchmark structure for traceability to QASMBench, VeriQbench,
Feynman, and the SQbricks buggy mutants.

The manifest stores explicit input/output pairs for every task. Unitary cases
compare the full circuit interface, hybrid cases pair measured classical bits
with their corresponding outputs, and partial cases list only logical inputs
and observable outputs, excluding reset ancillas and garbage.

These pairs follow the original program interfaces and the SQbricks transformer
input/output maps; they are not arguments passed explicitly
by the benchmark driver. The SQbricks driver first applies deferred measurement
and then compares all lifted quantum wires with empty pair lists. Its
`sanity-partial` branch also does not propagate the partial-interface parameters.
The manifest preserves the intended partial/discard interface expressed by the
suite instead of reproducing that script behavior.

## Generated program pairs

`generated/manifest.toml` contains 490 cases (487 EQ and 3 NEQ) from the
SQbricks single-program transformation lists. It stores the generated QASM
programs and the input/output maps returned by the SQbricks OWM and
teleportation transformations:

- `qiskit-hybrid`: 88 cases;
- `owm-vs-qiskit`: 55 cases;
- `owm-vs-tele`: 347 cases.

The `owm-vs-tele` list names the Feynman source `qft_4.qasm`; SQbricks packages
the same file as `qft_4_feynman.qasm`, so the materializer resolves that name.

Of the 435 unique source programs, all 34 Feynman files and 398 VeriQbench
files match their source repositories. The remaining three are SQbricks
variants: corrected bit-flip and phase-flip programs derived from VeriQbench,
and a reset-free ancilla version of the QASMBench Shor program.
