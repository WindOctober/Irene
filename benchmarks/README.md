# Irene benchmarks

This directory contains only equivalence tasks that form static program pairs
with reliable `eq` or `neq` ground truth. All programs use:

- UTF-8 text;
- LF line endings;
- the `.qasm` extension;
- the `OPENQASM 2.0;` header.

SQbricks is currently the only source:

```text
benchmarks/
├── sqbricks/
│   ├── manifest.toml
│   └── programs/
```

See [`SCHEMA.md`](SCHEMA.md) for the manifest schema. The corpus currently has
242 cases: 170 `eq` and 72 `neq`.

## Inclusion scope

The corpus includes every task from the SQbricks explicit two-path lists:

- `sanity-unit`: 42 `neq` cases;
- `sanity-hybrid`: 21 `neq` cases;
- `sanity-partial`: 9 `neq` cases;
- `unit-vs-hybrid`: 170 `eq` cases.

Transformation lists containing only one circuit are excluded because they
require SQbricks or Qiskit to generate the second circuit at runtime and are
not yet self-contained program pairs.

`truth` is the expected result under the `equivalence` semantics declared in
the manifest. In particular, `sanity-partial` uses the SQbricks partial/discard
semantics and must not be interpreted as full quantum-state equivalence.

Every case explicitly declares `input_pairs` and `output_pairs`. Only bits in
`output_pairs` are compared; unlisted ancillas, intermediate measurement bits,
and garbage are outside the observable interface. A hybrid case may use a
quantum/classical output pair when one side retains a quantum bit and the other
side emits its corresponding measurement result.
