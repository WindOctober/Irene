# Benchmarks

The corpus contains 1,982 paired cases: 1,228 EQ and 754 NEQ.
Label sources and comparison semantics are documented for each collection.

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
| IterTestQ | 180 | Static-unitary sample with upstream numerical QCEC reference labels |
| CaQR | 111 | Explicit output mappings; 108 pairs perform no qubit reuse |
| Quokka | 923 | Official opt/gm/flip pairs; 316 EQ and 607 NEQ |

QSeqSim contains 21 standalone programs, each with `paired = false` and no truth label.
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

## Using the corpus

Program paths in each manifest are relative to that manifest's directory.
All referenced programs are included in this repository. `source_*` fields
identify files in the upstream source; they are provenance, not runtime paths.

The CLI compares declaration-order interfaces and does not load manifests.
For explicit mappings or zero-initialized inputs, construct an
`EquivalenceConfig` from the manifest's interface and call `equivalence::analyze`.
See [interface semantics](../docs/architecture.md#frontend-and-interface).

## Sources

- [IterTestQ](itertestq/README.md) and [CaQR](caqr/README.md): source selection
  and interface semantics.
- [Quokka](quokka/README.md): official variants and exact-angle label semantics.

Each manifest records its source repository, revision, source paths and comparison
interface. Source links and licenses are documented in the collection READMEs.
