# Irene

Irene checks the equivalence of hybrid quantum programs written in supported
subsets of OpenQASM 2 and 3, including measurement and classical feedback.
It reports equivalence, non-equivalence, or an inconclusive result; unsupported
language features and invalid programs may produce errors.

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

Run the test suite with `cargo test --release`.
