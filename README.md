# Irene: IQIR and IreneQ

Irene checks the equivalence of hybrid quantum programs written in supported
subsets of OpenQASM 2 and 3, including measurement and classical feedback.
It reports equivalence, non-equivalence, or an inconclusive result; unsupported
language features and invalid programs may produce errors.

## Workspace

This repository contains two Rust crates with a one-way dependency:

- **IQIR** (`iqir/`, package/library `iqir`): Irene Quantum IR, its node
  allocator, OpenQASM 2/3 import support, traversal utilities, and pure unitary
  validation/miter helpers. It has no dependency on the verifier or external solvers.
- **Irene** (repository root, package/library `irene`): symbolic execution,
  equivalence checking, and the `irene` command.
  Its equivalence-verification component is called **IreneQ**;
  this is not a separate Cargo package or library name.
  `irene::ir` re-exports IQIR's types without conversion or duplication.
  `irene::frontend` re-exports IQIR's import layer for existing callers.

The split does not change the IR's operations, source metadata, phase
conventions, or verification semantics. See [IQIR](iqir/README.md) for its
construction API. Existing Rust consumers continue to use `irene::...`
without a dependency alias.

## Build and run

```sh
cargo build --release
cargo run --release -- left.qasm right.qasm
```

Both programs must use the same OpenQASM major version. SMT-backed checks require
external solvers; see the [architecture guide](docs/architecture.md#exact-coefficients-and-smt).

## Documentation

- [Architecture and semantics](docs/architecture.md)
- [Language support and limitations](docs/language-support.md)
- [Benchmarks](benchmarks/README.md)

Run both crates' test suites with `cargo test --workspace --release`.
The default workspace members also include both crates.
Use `cargo test -p iqir` to test only the standalone IR, or
`cargo test -p irene` for the verifier.
