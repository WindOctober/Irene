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

## OpenQASM 3 gates

- OpenQASM 3 `gate` definitions, including formal numeric parameters,
  nested previously declared gates and register broadcasting. Definitions
  have their signatures checked at declaration and their bodies checked/lowered
  when called, like subroutines. Call-site checking retains definition-time name
  visibility; unused bodies are not expanded. Invalid captures, arity, qubit aliasing,
  recursion, forward calls, non-unitary bodies and incompatible broadcasts
  fail with diagnostics. Expansion has statement/depth budgets.
- `ctrl`, `inv`, and static integer `pow` on custom gates and builtin `U`.
  A `Unitary { controls, power, body }` node represents the **entire** modified
  body. Negative powers reverse and adjoint the sequence; powers must never
  be distributed over noncommuting constituent gates. Positive controls are
  prepended source operands, and all must be one. `GlobalPhase` is retained
  under control, where it becomes a relative phase.
- Builtin `U(theta, phi, lambda)` and `gphase`. OpenQASM 3 specifies
  `U = exp(i*(theta+phi+lambda)/2) Rz(phi) Ry(theta) Rz(lambda)`;
  the time-ordered emitted sequence is global phase, Rz(lambda), Ry(theta),
  Rz(phi). In particular, **theta/2 cannot be discarded**. This differs from
  OpenQASM 2 / Qiskit U3. Imported AutoQ gate definitions are honored, not
  ignored like the upstream AutoQ comments describe.

### Backend support

Plain custom gates expand into existing Apply/Scope nodes. Composite controls,
inverse and integer powers retain a Unitary node, and gphase/U retain explicit
GlobalPhase nodes. Consumers must preserve sequence order and controlled phases.
IreneQ and IQIR's unitary miter currently reject these two node kinds explicitly
before optimization/execution; parsing them is not a verification result.

Gate bodies are checked when called, not via a temporary checker. Unused bodies
are not expanded. Definition-time lexical visibility is retained at calls, so
recursion, forward gate calls and captures of caller locals are rejected.
Expansion depth is limited to 64, modifier count to 16 and total expansion/copy
work to 65,536. Runtime numeric parameters, negctrl and non-integer powers remain
unsupported.

Run `cargo test -p iqir` and `cargo test -p irene --test gate_capabilities`.

## OpenQASM 3 while loops

The frontend preserves `while (condition) body` as `While { condition, body }`.
Nested loops and braced/single-statement bodies reuse existing Boolean lowering
and lexical scopes. Conditions are re-evaluated before each iteration by an IR
consumer; no finite unrolling or termination assumption is made.

Known-bit facts are cleared before lowering a loop and after it, so gate powers
cannot be specialized using stale entry values across a back edge. Facts newly
established inside an iteration can still be used by subsequent statements.
Loop nesting is limited to 64; this is not a runtime iteration bound.
`break` and `continue` remain unsupported.

Whole `bit[n]` registers can be compared to representable integer literals,
including `bit[1] c; while(c == 1) {}`. Comparison uses every bit in
little-endian order, rejects out-of-range literals, and also works in `if`.

IreneQ and the unitary miter reject loops explicitly, including loops in dead
branches, before optimization or execution. Frontend import is not a loop proof.
