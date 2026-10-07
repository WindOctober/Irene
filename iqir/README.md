# IQIR — Irene Quantum IR

IQIR is the solver-independent IR and OpenQASM import layer extracted from Irene. Its program model includes static registers, numeric
gate expressions, Boolean assignments, measurement, reset, conditional blocks,
while loops, typed scalars, composite gates and grouping scopes. Existing OpenQASM version metadata and phase conventions
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
retain their original error types. The include restrictions are unchanged. Importing does not perform
equivalence checking.

IQIR owns the OpenQASM parser dependencies, exact decimal/rational arithmetic,
and the `rug` arithmetic used by the existing angle lowering. It does not
depend on Irene or an SMT solver.

The separate `irene` crate contains the equivalence-verification component,
IreneQ, which accepts `iqir::Program` directly. It re-exports the IR types as
`irene::ir`, the import layer as `irene::frontend`, and the original source
loading utilities through `irene::utils`.

## OpenQASM 3 control flow and gates

- `while (condition) { ... }`, including nested loops, measurement-driven
  control, and single-statement bodies. A loop remains one `While` node;
  there is no finite unrolling and no termination assumption. Block-local
  declarations are allocated afresh on each entry. Entry facts are cleared
  before lowering a loop body and after a loop for `pow` specialization.
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
- Mutable `int[n]` with `1 <= n <= 64`, and `float[32]` /
  `float[64]`: declarations, initializers, assignment, unary minus, `+ - * /`,
  integer `%`, corresponding compound assignments, and all six comparisons.
  Boolean combinations of comparisons can control `if` and `while`.
- `bit[n]` versus representable integer literal comparisons use the complete
  little-endian register, including the `bit[1] c; while(c == 1)` spelling
  produced by Qiskit. Width/shape are not reduced to the lowest bit.

## Scalar types, declarations and constant evaluation

`ScalarType` describes integer signedness/width or floating precision, not
when a value is evaluated. Const and variable declarations share the same
type parser, expression builder, promotions and arithmetic. Scope bindings
store const qualification, assignability and an optional known `ScalarValue`
separately. A specialized for-loop index can be known without being const;
a variable's known initializer does not make it admissible in const contexts.

`ScalarDeclare`, `ScalarAssign` and `ScalarCompare` integrate with the ordinary
statement and Boolean-expression IR. Constants are evaluated from the same
`ScalarExpr` tree and stored in the symbol table, without executable storage.
Static integer specialization shares the checked integer arithmetic with that
evaluator. Floating constant arithmetic no longer has a separate AST evaluator.
The existing exact symbolic `NumericExpr` representation remains for gate
parameters; it is a different numeric domain, not a non-runtime scalar type.

The target defaults are 32-bit signed integers and binary64 floats.
Explicit versus omitted widths are retained as declaration metadata, not type
identity: `int` and `int[32]` are compatible on this target. Integers are **not**
unbounded mathematical integers. Signed overflow and integer division by zero
must be diagnosed by consumers.
Integer division truncates toward zero. Out-of-range literals are rejected.
Literal-only integer subexpressions use the existing checked static-integer
frontend before conversion to a destination width. Signed scalar operands
must have the same width; broader promotions are not yet admitted.

Float literals use binary64 like the existing constant frontend. Float binary
operations promote to the wider operand precision; explicit `FloatCast` nodes
record widening and assignment narrowing. Each operation is IEEE binary32 or
binary64, not exact rational arithmetic. For example, `(a+b)-a` with two
binary32 variables rounds after the addition; replacing `b` with literal `1.0`
promotes the operation to binary64. The target rounding profile is nearest,
ties-to-even with gradual underflow. Signed zero, subnormals and float encoding
are retained. Arithmetic/conversion can produce infinities or NaNs; comparisons
must follow IEEE behavior (`NaN != value`, other comparisons false).
Nonfinite source literals are rejected.

Declarations without initializers stay uninitialized. The frontend does not
prove definite initialization or execute runtime arithmetic. Backends must
check reads, overflow, zero division, and allocation lifetimes; they must not
invent zeros or reuse a previous iteration's local value.

This remains a supported subset, not a full OpenQASM implementation: `break`,
`continue`, runtime array indexing, variable numeric gate parameters, numeric
subroutine parameters/returns, mixed signed/unsigned arithmetic, int/float
variable conversions, non-floating scalar casts, integer bitwise/shift operations
in the new scalar representation, non-integer gate powers, `negctrl`, and
non-gate bodies inside gate definitions remain explicitly unsupported.
Unsigned `uint[n]` keeps the existing word/bit lowering, including indexed reads,
measurement writes, bitwise operations, shifts and comparisons. Addition and
subtraction (including compound assignments) reuse the modular word adder also
used for angles; assignments read all operands before writing destination bits.
Integer literals must fit the word; unsigned operands must have equal widths.
It is not rerouted through the signed/float scalar representation; runtime uint arithmetic
other than addition/subtraction remains unsupported.

## Validation

```bash
cargo test --locked -p iqir
cargo clippy --locked -p iqir --all-targets -- -D warnings
cargo check --locked --workspace --all-targets
cargo test --locked -p irene --lib
cargo run --locked -p iqir --example import -- input.qasm
```

Tests inspect actual IR and use small independent classical/state-vector
interpreters for loop execution, scope, signedness, float promotion/rounding,
whole-register comparisons, controlled U phases, composite inverse/power and
negative admissions. Frontend tests check unique/dense AST IDs.
The local Saria suite has 122 `program.qasm` inputs. Its
`benchmark/iqir-parse-report.*` files record the earlier Git-dependent run,
not unpublished changes in this checkout.

Semantic references:
[OpenQASM 3 gates](https://openqasm.com/versions/3.0/language/gates.html),
[types and casts](https://openqasm.com/versions/3.0/language/types.html),
[classical instructions](https://openqasm.com/versions/3.0/language/classical.html).

## Verifier support

Frontend import and verification share one IR. Import success is not an equivalence or termination
proof. IreneQ currently rejects while loops, scalar storage/comparisons,
explicit global phases and composite unitary modifiers before slicing or symbolic
execution, even in dead branches. IQIR's unitary miter also reports unsupported
statements explicitly. These diagnostics mark backend capabilities, not a second
frontend. Plain custom gates that expand entirely to supported gate nodes can
use the existing verifier.
