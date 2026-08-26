# Manifest schema

Each source directory contains a `manifest.toml` with these top-level fields:

```toml
schema_version = 1
program_format = "openqasm2"

[source]
id = "..."
name = "..."
repository = "..."
commit = "..."

[normalization]
encoding = "utf-8"
line_endings = "lf"
semantic_rewrite = false
```

Each task is represented by one `[[case]]` entry:

```toml
[[case]]
id = "stable-unique-id"
suite = "source-suite"
left = "programs/...qasm"
right = "programs/...qasm"
truth = "eq"                  # Must be eq or neq
equivalence = "hybrid"
input_pairs = [
  "quantum:q[0]=quantum:r[0]",
]
output_pairs = [
  "quantum:q[1]=classical:d[0]",
]
qbircks_compatible = true
source_left = "benchmarks/..."
source_right = "benchmarks/..."
```

`input_pairs` and `output_pairs` explicitly map the interfaces of the left and
right programs bit by bit. Bits absent from `output_pairs` are not observable
and may be discarded as ancillas or garbage. Input pairs must have matching
kinds. An output pair may relate a quantum bit to a classical measurement bit;
this means measuring the quantum endpoint in the Z basis and comparing the
resulting classical values. It does not mean coherence-preserving quantum-wire
equality.

`qbircks_compatible` records only whether the current HQbricks/QbIRcks
OpenQASM 2 frontend can parse both inputs. It is not part of the ground truth.

Allowed `equivalence` values are:

- `unitary`: full unitary equivalence;
- `hybrid`: SQbricks hybrid-circuit equivalence;
- `partial`: partial equivalence with observable/discard semantics.
