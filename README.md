# Irene: An Equivalence Checker for Hybrid Quantum Programs

Irene checks the equivalence of hybrid quantum programs written in supported
subsets of OpenQASM 2 and 3, including measurement and classical feedback.
It reports equivalence, non-equivalence, or an inconclusive result; unsupported
language features and invalid programs may produce errors.

## News

- **2026-10-07** · [Solver refinements](docs/architecture.md#numerical-hps-certificates): certified counterexample search on three inputs, gate-block fusion, shared DAG nodes with fused elimination, incremental budget accounting, and early phase checks reduce repeated work. **Solved: 1691/1982 (+5) · Average time: 3.134 s.**

- ⭐ **2026-10-07** · [Faster certified matrices](docs/architecture.md#numerical-hps-certificates): Arb complex-ball arithmetic and fused short dot products accelerate matrix contraction while retaining rigorous error bounds. **Solved: 1686/1982 · Average time: 3.824 s.**

- ⭐⭐ **2026-10-07** · [Hidden affine recovery](docs/architecture.md#algebraic-reductions): complex Boolean representations can obscure valid path-elimination opportunities, so we reuse Davio decomposition to expose hidden constant and affine functions in guards and phase selectors, enabling existing elimination rules to apply. **Solved: 1665/1982 · Average time: 5.31 s.**

  For arbitrary Boolean expressions $A,B$, even over many path variables:

  $$G=(\neg A\land\neg B)\oplus(A\land B)\oplus A\oplus B\oplus1=0.$$

  Recovering this identity removes the redundant guard $G=0$ and simplifies a phase selector $G\oplus y$ to $y$, revealing elimination opportunities hidden by apparent dependencies on $A$ and $B$.

  Scheduling: try HPS for five seconds before matrix contraction; if the HPS probe times out and the matrix cannot decide, retry HPS with its normal resource budget.

- ⭐ **2026-10-06** · [Certified unitary contraction](docs/architecture.md#numerical-hps-certificates): shared HPS semantics for exact and interval backends, with full-operator contraction up to 10 qubits under resource budgets. **Solved: 1635/1982 · Average time: 5.09 s.**
- **2026-10-05** · [Local gate rewriting](docs/architecture.md#verification-flow): shared exact identities, including native Hadamard and local SWAP reductions, applicable to supported fragments within mixed-angle circuits. **Solved: 1590/1982 · Average time: 3.67 s.**
- ⭐⭐⭐ **2026-09-28** · [Paper version](https://arxiv.org/abs/2609.36065v1): the implementation accompanying the paper is maintained on the [FSE-Ver](https://github.com/WindOctober/Irene/tree/FSE-Ver) branch. **Solved: 1584/1982 · Average time: 3.93 s.**

Average time is the arithmetic mean of final-attempt wall time for solved pairs
only, including certified approximate verdicts and excluding interrupted retries.
Each entry reports its historical full-suite run; +5 is relative to the matrix update.

## Workspace

- **[IQIR](iqir/README.md)**: a reusable intermediate representation for hybrid
  quantum programs, currently focused on importing OpenQASM 2 and 3.
- **IreneQ**: Irene's equivalence checker, using symbolic execution and solver-backed
  reasoning to compare programs represented in IQIR.

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

## Citation

If you use Irene in your research, please cite our
[paper](https://arxiv.org/abs/2609.36065):

```bibtex
@misc{ke2026irene,
  title         = {{Irene}: Equivalence Checking of Hybrid Quantum Programs via Structure-Preserving Symbolic Reduction},
  author        = {Jingyu Ke and Jingyang Li and Guoqiang Li},
  year          = {2026},
  eprint        = {2609.36065},
  archivePrefix = {arXiv},
  primaryClass  = {cs.PL},
  url           = {https://arxiv.org/abs/2609.36065}
}
```
