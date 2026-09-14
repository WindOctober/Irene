# CaQR official generation and audited output mapping

Source: [CaQR](https://github.com/ruadapt/CaQR), commit
`0b935d962bffa6e845f2b9548b768f2f558cbe18`.

All 168 official `benchmarks/*.qasm` inputs were attempted with the unchanged
official `main.py`, default weights, Qiskit 0.45.0, and a 20-second per-program
generation timeout. There were 158 completed generations and 10 generation
timeouts. All completed outputs passed official `validate.py` (its success
message was checked, not just its exit code). The separately committed
`bv_n10_reuse.qasm` is preserved as its own case, not overwritten by regeneration.

The manifest admits 111 EQ pairs:

- 108 generated cases with an empty reuse chain, hence no actual qubit reuse;
- 2 generated reuse cases: `bv_n10`, `cc_n10`;
- 1 committed reuse case: `bv_n10`.

The 48 other completed generations have nonempty chains but no original
classical measurement outputs. Their discarded intermediate logical quantum
outputs cannot be represented as preserved outputs just by pairing qubit
indices. They remain quarantined, without invented truth labels or vacuous
empty-output tasks. All originals, generated QASM, map/chain files, and
generation/validation logs remain in `var/benchmark-sources/caqr-generated/`.

For admitted reuse cases, inputs are closed zero-state inputs (`input_pairs=[]`).
The mapping audit checks map/chain agreement, follows physical-wire lifetimes
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
operations in exported files. No upstream code was patched.

Reproduce from the workspace root (the isolated environment needs Qiskit 0.45,
networkx, matplotlib and pylatexenc):

```sh
var/benchmark-sources/caqr-env/bin/python scripts/benchmarks/materialize_caqr.py
var/benchmark-sources/caqr-env/bin/python -m unittest discover \
  -s scripts/benchmarks -p test_external_imports.py -v
python3 scripts/experiments/run.py --tool irene \
  --manifest Irene/benchmarks/caqr/manifest.toml --timeout 10 --jobs 8
```

Generation logs are cached, including timeouts. The archived `import-report.json` records
every attempted input, official validation output, admission decision and mapping.
Source provenance distinguishes the committed example from locally generated
outputs at the pinned revision.
Detailed per-case provenance and the import report are stored under
`var/benchmark-sources/import-audits/caqr/` at the workspace root.
The manifest retains the semantic mappings and source paths; map/chain files
remain alongside the programs.
