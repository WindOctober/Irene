# IQIR — Irene Quantum IR

IQIR is the solver-independent IR and OpenQASM 2/3 import layer extracted from
Irene. It represents quantum gates, classical data, structured control flow and
specification annotations. It does not depend on Irene or an SMT solver, and is
not the LLVM-based QIR Alliance format.

## Import OpenQASM

```rust
use iqir::frontend;

let program = frontend::parse_str(
    "OPENQASM 3.0; include \"stdgates.inc\"; qubit q; h q;",
    "example.qasm",
)?;
// Alternatively: let program = frontend::parse_file("example.qasm")?;
# Ok::<(), frontend::ImportError>(())
```

Both functions select the frontend from the declared OpenQASM version and return
`iqir::Program`. Version-specific APIs are available under
`frontend::openqasm2` and `frontend::openqasm3`.

## IR model

Programs contain declarations and statement blocks. Statements represent gates,
measurement/reset, classical assignments, `if`, `while`, and grouped operations.
Numeric gate parameters and classical scalar expressions have distinct types.

Construct nodes with `AstIdGenerator::node` and access their identities through
`AstNode::ast_id()`:

```rust
use iqir::{AstIdGenerator, Gate, Qubit, StatementKind, SymbolId};

let mut ids = AstIdGenerator::default();
let h = ids.node(StatementKind::Apply {
    gate: Gate::H,
    parameters: vec![],
    qubits: vec![Qubit { register: SymbolId(0), index: 0 }],
});
assert_eq!(h.ast_id().index(), 0);
```

Use one generator per program; start at `program.ast_id_bound()` when extending
an existing program. IDs index analysis tables and do not affect node equality.
Cloning preserves IDs; `clone_numeric_expr` allocates fresh expression IDs.
Gate arities are available through `iqir::gate_shape`. Node construction itself
does not validate operands, scopes or numeric domains.

## Frontend support

The supported OpenQASM subset includes custom gates and broadcasts, controlled
and inverse/powered gate bodies, structured loops, typed classical scalars, and
constant evaluation. Import preserves supported constructs; it does not execute
loops or assume termination.

See [OpenQASM frontend semantics](docs/frontend.md) for lowering rules, numeric
semantics and unsupported constructs.

## Specification annotations

The OpenQASM 3 frontend recognizes `@saria.requires`, `@saria.ensures`,
`@saria.invariant` and `@saria.terminates`, plus pure auxiliary functions defined
with `pragma saria.def`. Annotations attach
to statements and use a separate, typed mathematical expression AST.

Import checks syntax, names and types—not whether a specification holds.
Annotations do not change executable semantics or equivalence checking.
See [Specification annotations](docs/spec-annotations.md) for syntax, examples,
helper functions and checking boundaries.

## Verification boundary

Import success is not an equivalence or termination proof. The separate IreneQ
verifier accepts `iqir::Program` and checks its own supported subset.
Full-unitary admission and miter construction belong to
`irene::equivalence::unitary_miter`, not IQIR.

Irene re-exports the IR as `irene::ir` and the frontend as `irene::frontend`.
See [Irene's architecture](../docs/architecture.md) for verification details.

## Development

```bash
cargo test --locked -p iqir
cargo clippy --locked -p iqir --all-targets -- -D warnings
cargo check --locked --workspace --all-targets
cargo test --locked -p irene --lib
cargo run --locked -p iqir --example import -- input.qasm
```
