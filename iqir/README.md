# IQIR — Irene Quantum IR

IQIR is the solver-independent IR and OpenQASM import layer extracted from Irene. Its initial version
preserves the existing gate-level program model: static registers, numeric
gate expressions, Boolean assignments, measurement, reset, conditional blocks,
and grouping scopes. Existing OpenQASM version metadata and phase conventions
are unchanged; this is not the LLVM-based QIR Alliance format.

Use `AstIdGenerator::node` to build nodes, and `AstNode::ast_id()` to read
their identities. Use one generator per program. To extend an existing program,
start a generator at `program.ast_id_bound()`. Ordinary cloning preserves IDs;
`clone_numeric_expr` allocates fresh IDs for an expression tree.

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

Node IDs index analysis tables; they do not affect semantic equality.
The allocator does not validate operands, scopes, or numeric domains. Existing
validation boundaries are preserved; constructing an IR does not imply that
IreneQ can verify it. The `unitary` module retains its restricted full-unitary
validation and miter contract.

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

Both functions select the OpenQASM 2 or 3 frontend using the declared version
and return `iqir::Program`. The version-specific
`frontend::openqasm2::parse_str` and `frontend::openqasm3::parse_str` APIs
retain their original error types. Existing supported subsets, numeric
lowering, and include restrictions are unchanged. Importing does not perform
equivalence checking.

IQIR owns the OpenQASM parser dependencies, exact decimal/rational arithmetic,
and the `rug` arithmetic used by the existing angle lowering. It does not
depend on Irene or an SMT solver.

The separate `irene` crate contains the equivalence-verification component,
IreneQ, which accepts `iqir::Program` directly. It re-exports the IR types as
`irene::ir`, the import layer as `irene::frontend`, and the original source
loading utilities through `irene::utils`.
