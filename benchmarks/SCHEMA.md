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

`program_format` is either `openqasm2` or `openqasm3`.

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

Closed programs may set `initial_state = "zero"` and leave `input_pairs`
empty. Their equivalence is evaluated from the declared initial state.

Allowed `equivalence` values are:

- `unitary`: full unitary equivalence;
- `hybrid`: SQbricks hybrid-circuit equivalence;
- `partial`: partial equivalence with observable/discard semantics.

Standalone programs that do not yet form an equivalence task use `[[program]]`:

```toml
[[program]]
id = "stable-unique-id"
suite = "source-suite"
path = "programs/...qasm"
paired = false
source_path = "original/source/path"
```

An unpaired program has no `left`, `right`, or `truth` field and is not counted
as an equivalence case.
