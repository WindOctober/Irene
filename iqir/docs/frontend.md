# OpenQASM frontend semantics

This document describes the supported subset and lowering rules. For import
APIs and examples, see the [IQIR overview](../README.md). Specification syntax
is documented separately in [Specification annotations](spec-annotations.md).

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

## Validation notes

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
execution, even in dead branches. IreneQ's unitary miter also reports unsupported
statements explicitly. These diagnostics mark backend capabilities, not a second
frontend. Plain custom gates that expand entirely to supported gate nodes can
use the existing verifier.
