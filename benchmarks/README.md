# Benchmarks

The corpus contains 1,982 paired cases: 1,228 EQ and 754 NEQ after four audited
EQ-to-NEQ corrections. Labels include upstream references as well as audited
results; see each collection's provenance.

All programs use UTF-8, LF line endings, a `.qasm` extension and an
`OPENQASM 2.0;` or `OPENQASM 3.0;` header. [SCHEMA.md](SCHEMA.md) defines the manifests.

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

## Collections

| Collection | Paired cases | Scope |
| --- | ---: | --- |
| SQbricks explicit lists | 242 | sanity-unit: 42 NEQ; sanity-hybrid: 21 NEQ; sanity-partial: 9 NEQ; unit-vs-hybrid: 170 EQ |
| SQbricks generated | 490 | qiskit-hybrid: 88; owm-vs-qiskit: 55; owm-vs-tele: 347 |
| Qubit reuse | 10 | EQ pairs with measurement, reset and physical-qubit reuse |
| OpenQASM 3 transformations | 26 | 14 EQ and 12 NEQ |
| IterTestQ | 180 | First-pass sample with upstream numerical QCEC reference labels |
| CaQR | 111 | Audited interfaces; 108 pairs perform no qubit reuse |
| Quokka | 923 | Official opt/gm/flip pairs; 316 EQ and 607 NEQ after the routing-2 correction |

QSeqSim adds 21 standalone programs, each with `paired = false` and no truth label.
They cover RUS, quantum random walks, Grover and random while loops.

OpenQASM 3 transformations cover inverse QFT, teleportation, IPE, RUS,
repetition-code QEC, fault-tolerant gate teleportation, magic-state injection,
MBQC, remote CNOT, dynamic GHZ and amplitude-damping environment reuse.
The SQbricks-packaged `qft_4_feynman.qasm` corresponds to Feynman's `qft_4.qasm`.

## Comparison semantics

`truth` is the expected result under the manifest's `equivalence` semantics.
Every pair explicitly specifies `input_pairs` and `output_pairs`; only listed
outputs are observable. Unlisted ancillas, intermediate measurement bits and
garbage are discarded. Hybrid interfaces may pair a quantum output with its
corresponding classical measurement result.

SQbricks `sanity-partial` uses partial/discard semantics, not full quantum-state
equivalence. IterTestQ's numerical reference labels and Quokka's upstream expected
labels are not independent exact certificates.

## Sources and import records

- [IterTestQ](itertestq/README.md) and [CaQR](caqr/README.md): input provenance and selection.
- [Quokka](quokka/README.md): official variants and label correction.
- `var/benchmark-sources/`: scratch directory, excluded from version control,
  that the import scripts below fetch upstream archives and repositories into,
  including the full IterTestQ Figshare archive and comparison inventory.
- `var/benchmark-sources/import-audits/<collection>/`: detailed CaQR, IterTestQ
  and Quokka provenance and import reports, written there by the same scripts. Manifests retain source paths,
  reference labels and semantic mappings; import records are separate from solver results.
