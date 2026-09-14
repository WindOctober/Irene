# Irene benchmarks

This directory contains equivalence tasks with reliable `eq` or `neq` ground
truth, plus explicitly marked standalone programs that may become tasks later.
All programs use:

- UTF-8 text;
- LF line endings;
- the `.qasm` extension;
- an `OPENQASM 2.0;` or `OPENQASM 3.0;` header.

The current sources are:

```text
benchmarks/
├── caqr/
├── itertestq/
├── openqasm3-programs/
├── qubit-reuse/
├── qseqsim/
├── quokka/
└── sqbricks/
    ├── manifest.toml
    ├── programs/
    └── generated/
        ├── manifest.toml
        └── programs/
```

See [`SCHEMA.md`](SCHEMA.md) for the manifest schema. The corpus has 1,982 paired
cases: 1,232 `eq` and 750 `neq`. This includes 180 first-pass IterTestQ cases
with **upstream numerical QCEC reference labels**, not exact certificates,
and 111 audited CaQR pairs (108 of which perform no qubit reuse).
The [Quokka collection](quokka/README.md) adds 923 official origin-versus-opt,
gm and flip tasks: 317 expected EQ and 606 expected NEQ. These are upstream
reference labels, not independently certified truth; shift variants are excluded.
QSeqSim additionally contributes 21 unpaired
programs, which are not counted as equivalence cases.

See [the external-source first-pass report](EXTERNAL_IMPORT_REPORT.md) for
coverage, exclusions, reproduction commands, and current Irene results.
The IterTestQ selection is not the full Figshare corpus; the complete archive
and a full comparison inventory are retained locally under
`var/benchmark-sources/` at the workspace root.

## Import audit storage

For CaQR, IterTestQ and Quokka, manifests retain source paths, reference labels
and semantic input/output mappings. Detailed per-case provenance and import
reports live outside the benchmark tree, under
`var/benchmark-sources/import-audits/<collection>/` at the workspace root.
Import scripts write these audit records there as well; they are not solver results.

## Inclusion scope

The corpus includes every task from the SQbricks explicit two-path lists:

- `sanity-unit`: 42 `neq` cases;
- `sanity-hybrid`: 21 `neq` cases;
- `sanity-partial`: 9 `neq` cases;
- `unit-vs-hybrid`: 170 `eq` cases.

The generated manifest materializes three SQbricks transformation suites as
self-contained program pairs:

- `qiskit-hybrid`: 88 cases;
- `owm-vs-qiskit`: 55 cases;
- `owm-vs-tele`: 347 cases.

Qubit reuse contributes 10 generated `eq` pairs whose
right-hand programs use measurement, reset, and physical-qubit reuse.

OpenQASM 3 program transformations contribute fourteen `eq` and twelve `neq`
pairs. They cover inverse QFT, teleportation, IPE, RUS, repetition-code QEC,
fault-tolerant gate teleportation, magic-state injection, MBQC, remote CNOT,
dynamic GHZ preparation, and amplitude-damping environment reuse.

QSeqSim contributes standalone RUS, quantum-random-walk, Grover, and random
while-loop programs. Every QSeqSim entry has `paired = false` and no truth
label.

The SQbricks-packaged name `qft_4_feynman.qasm` is used for the corresponding
Feynman source `qft_4.qasm`.

`truth` is the expected result under the `equivalence` semantics declared in
the manifest. In particular, `sanity-partial` uses the SQbricks partial/discard
semantics and must not be interpreted as full quantum-state equivalence.

Every case explicitly declares `input_pairs` and `output_pairs`. Only bits in
`output_pairs` are compared; unlisted ancillas, intermediate measurement bits,
and garbage are outside the observable interface. A hybrid case may use a
quantum/classical output pair when one side retains a quantum bit and the other
side emits its corresponding measurement result.
