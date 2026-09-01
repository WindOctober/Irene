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
├── openqasm3-programs/
├── qubit-reuse/
├── qumug/
├── qseqsim/
├── sqbricks/
│   ├── manifest.toml
│   ├── programs/
│   └── generated/
│       ├── manifest.toml
│       └── programs/
└── veriqbench-sequential/
```

See [`SCHEMA.md`](SCHEMA.md) for the manifest schema. The corpus has 818 paired
cases: 699 `eq` and 119 `neq`. QSeqSim additionally contributes 21 unpaired
programs, which are not counted as equivalence cases.

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

VeriQBench Sequential contributes 20 OpenQASM 3 sequential-machine pairs:
15 `eq` and 5 `neq`. Qubit reuse contributes 10 generated `eq` pairs whose
right-hand programs use measurement, reset, and physical-qubit reuse.

OpenQASM 3 program transformations contribute fourteen `eq` and twelve `neq`
pairs. They cover inverse QFT, teleportation, IPE, RUS, repetition-code QEC,
fault-tolerant gate teleportation, magic-state injection, MBQC, remote CNOT,
dynamic GHZ preparation, and amplitude-damping environment reuse.

QUMUG contributes 30 static `neq` pairs, one hard GA-generated first-order
mutant for each MQT Bench circuit used in its evaluation.

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
