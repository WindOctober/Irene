# CaQR qubit-reuse pairs

Source: [CaQR](https://github.com/ruadapt/CaQR), commit
`0b935d962bffa6e845f2b9548b768f2f558cbe18`.

The manifest contains 111 EQ pairs from the official generator and repository:

- 108 generated cases with an empty reuse chain, hence no actual qubit reuse;
- 2 generated reuse cases: `bv_n10`, `cc_n10`;
- 1 committed reuse case: `bv_n10`.

Cases with nonempty reuse chains but no original classical measurement outputs
are excluded. Pairing physical qubit indices cannot preserve their discarded
logical quantum outputs. Included circuits and their map/chain files are in
`programs/`; [manifest.toml](manifest.toml) specifies each comparison interface.

For admitted reuse cases, inputs are closed zero-state inputs (`input_pairs=[]`).
Interface validation checks map/chain agreement, follows physical-wire lifetimes
through every reset, records the logical source of each classical measurement,
and pairs the original final measurements with retained corresponding right
outputs. Outputs overwritten by later measurements are rejected. Unmeasured
ancillas are not declared observable. This is a measured-output equivalence,
not preservation of arbitrary logical quantum inputs or quantum outputs.
No-reuse cases compare every quantum and classical output from zero inputs.

The official generator attaches conditions to inserted measure/reset in memory.
With its requested Qiskit 0.45.0, `QuantumCircuit.qasm()` omits these conditions
in exported QASM. The benchmark checks **the actual exported QASM**, not the
in-memory circuit. Official validation compares operation names/parameters/wires
but ignores conditions, so the importer separately rejects conditional reuse
operations in exported files.

Generation uses the official `main.py`, default weights, Qiskit 0.45.0 and a
20-second per-program timeout. Outputs must pass `validate.py`, including its
success-message check. The committed `bv_n10_reuse.qasm` is a separate source
case from its generated counterpart.

The included programs can be compared without regenerating them or installing
CaQR. Use the explicit zero-input and output mappings described in
[using the corpus](../README.md#using-the-corpus).
