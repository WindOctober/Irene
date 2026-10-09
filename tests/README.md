# Tests

Rust files directly under this directory are standalone Cargo integration tests.
They import `irene` as a library; `common/` contains test-owned helpers, including
a small independent matrix oracle. Run the workspace suite with:

```sh
cargo test --workspace
```

The equivalence suite is organized by observable behavior:

| Target | Contract |
| --- | --- |
| `equivalence` | Channel equality, density witnesses, exact aggregation and SMT regressions |
| `equivalence_channels` | Hidden histories, coherent inputs, nonlinear measurement feedback |
| `equivalence_interface` | Input/output pairing, initialization and invalid interfaces |
| `equivalence_intervals` | Conservative distance certificates, phase and preprocessing error |
| `dependency_rewrites` | Operator preservation and certified approximate rewriting |
| `unitary_miter`, `miter_construction` | Inversion and unitary admission |

These replace the former `tests/unit/equivalence` modules. Public-facing cases
were migrated and private-algorithm cases consolidated into channel/operator
contracts. This is not one-for-one internal branch coverage: private cache
layout, node counts, forced backend schedules and synthetic internal states are
no longer tested directly. Existing end-to-end regression tests remain in place.
No verifier internals are made public for testing, and no implementation source
is included in a test crate.

Other subsystems retain their existing library unit tests; this migration is
limited to equivalence verification.
