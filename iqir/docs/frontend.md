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
The symbolic `NumericExpr` representation remains for gate angle parameters.
OpenQASM 3 floating literals, builtin float constants (`pi`, `tau`, `euler`),
and machine arithmetic inside gate arguments first use the same typed scalar
evaluator as classical declarations. Only the final finite IEEE value is
embedded as an exact rational for the mathematical gate; decimal `0.1` is
therefore not the rational `1/10`. Closed floating subexpressions in symbolic
angle expressions follow this rule too. Gate formals retain angle algebra;
this does not add a finite-width angle hardware model.

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

Closed calls to `sin`, `cos`, `tan`, `arcsin`, `arccos`, `arctan`, `sqrt`,
`exp`, `log`, `floor`, and `ceiling` are evaluated at import. Calls may nest;
each result is rounded to its argument's binary32/binary64 precision (integer
arguments promote to binary64). Assignment narrowing happens afterwards.
This target uses correctly rounded, nearest/ties-to-even results (except the
explicit directed rounding in floor/ceiling), using native IEEE basic operations
or directed MPFR bounds for transcendental functions; it does not assume every device math library
implements that profile. Domain errors, nonfinite results, and unresolved
rounding are rejected for closed calls. `floor`/`ceiling` still return floats; a separate
`int[n](...)`/`uint[n](...)` cast truncates toward zero and checks the range.
Gate arguments containing these calls use the same floating evaluator and
export the rounded binary value as an exact rational. A flow-sensitive scalar
analysis also evaluates calls/casts/gate parameters using known mutable values:
declarations and assignments propagate typed values; branch joins retain only
bit-identical facts; while headers and exits forget possibly written variables
and preserve read-only ones. This is not const qualification: mutable reads
remain illegal in const declarations and const-required sizes. Ordinary scalar
reads remain in executable IR. Unknown arguments to `floor`, `ceiling`,
`sqrt`, `arccos`, `sin`, `arcsin`, and `log` remain as `ScalarExprKind::FloatUnary` nodes; explicit floating-to-integer
casts remain as `IntFromFloat`. The shared constant evaluator and symbolic
consumer use the same precision and truncation semantics. Unary IEEE operations
preserve signed zero and special values; integer conversions require a finite,
representable truncated integer. Consumers must prove these conditions even for
unused or overwritten conversions. `arccos` and `arcsin` denote principal branches on
[-1,1]; `sin` takes finite radians; `log` is natural logarithm on finite positive
arguments. All round to operand precision, rather than
denoting exact-real functions. Their shared closed evaluator uses directed MPFR
rounding bounds. Saria preserves symbolic calls
but both SMT and Rocq currently reject dependent goals; a future checked model
must establish domain and rounding semantics. Pending transcendental evaluation is not
erased when its result is overwritten. Unknown arguments to other math functions
(including measurement-driven statistics and loop-carried values) are still
rejected rather than approximated or replaced by a first-iteration value.
Typed arithmetic and integer-to-float casts can remain dynamic, including
inside gate parameters as described below.

Declarations without initializers stay uninitialized. The frontend does not
prove definite initialization or execute runtime arithmetic. Backends must
check reads, overflow, zero division, and allocation lifetimes; they must not
invent zeros or reuse a previous iteration's local value.

Runtime bit-string casts to `int[n]` / `uint[n]` retain the original Boolean
reads. When entering scalar IR, `ScalarExprKind::FromBits` represents these
reads: bit zero is least significant and signed results use two's complement.
OpenQASM requires matching source/destination widths for this cast. For a
nonnegative four-bit measurement result use `int[32](uint[4](bits))`, not
`int[32](bits)` or `int[32](int[4](bits))`.
`IntWiden` supports value-preserving integer conversions: same signedness to
an equal/wider width, or unsigned to a strictly wider signed integer. It does
not silently truncate or reinterpret out-of-range values. These nodes preserve
the original bit dependencies; consumers must retain uninitialized-read errors
and classical/quantum correlations rather than create fresh unconstrained
integers. Closed bit values can fold; runtime values remain symbolic.

Integer-to-float conversion reuses `FloatCast` (numeric conversion, not bit
reinterpretation). The target profile uses round-to-nearest, ties-to-even
(RNE); constants and symbolic execution share `ScalarValue::to_float`, and SMT
uses signed `to_fp` or unsigned `to_fp_unsigned` with the same rounding mode.
Conversion goes directly to the requested precision, avoiding double rounding
through binary64 when the target is binary32. `int[32]` and `uint[32]` values
are exactly representable in binary64; wider integers may round. Integer
subexpressions retain their arithmetic before promotion: `float[64](n / 2)`
performs integer division, whereas `float[64](n) / 2.0` performs float division.
Explicit intermediate casts such as `float[64](float[32](n))` remain visible.

Dynamic typed float gate parameters use `NumericExprKind::Scalar`, preserving
all intermediate IEEE operations and current classical-memory reads. Only the
final finite float value is interpreted as a real angle. Saria's SMT encoding
uses `fp.to_real` with explicit non-NaN/non-infinite definedness requirements;
it never assumes those requirements. Uninitialized reads and undefined integer
operations remain errors/obligations. CoqQ currently rejects these parameters
instead of replacing IEEE computations with real arithmetic; Irene's
equivalence backend also rejects this unsupported machine-number fragment.

This remains a supported subset, not a full OpenQASM implementation: `break`,
`continue`, runtime array indexing, numeric
subroutine parameters/returns, mixed signed/unsigned arithmetic, narrowing/reinterpreting scalar integer casts, runtime scalar
shifts, non-integer gate powers, `negctrl`, and
non-gate bodies inside gate definitions remain explicitly unsupported.
Unsigned `uint[n]` keeps the existing word/bit lowering, including indexed reads,
measurement writes, bitwise operations, shifts and comparisons. Addition and
subtraction (including compound assignments) reuse the modular word adder also
used for angles; assignments read all operands before writing destination bits.
Integer literals must fit the word; unsigned operands must have equal widths.
It is not rerouted through the signed/float scalar representation; runtime uint arithmetic
other than addition/subtraction remains unsupported.

## Validation notes

### Shared constant-specialization interface

Classical conditions, scalar values, unsigned-word initializers and typed
integer gate arguments share the checked static-integer evaluator also used
by ranges and indices. Closed `&`, `|`, `^`, `~`, shifts and remainder are
evaluated before selecting a runtime Boolean-word or scalar encoding.
`closed_integer` distinguishes "not a closed integer" from an invalid closed
computation. Only the former can fall through to runtime lowering; overflow,
zero division, invalid shifts and incompatible signedness remain errors.
Computed values retain width and signedness when passed to classical consumers.
Signed shifts are restricted to nonnegative operands and representable results;
unsigned shifts use the declared width and wrap. Unknown scalar shift operands
are not lowered by this constant-specialization path.

Boolean constants and known-bit flow analysis share one bounded evaluator.
`ScalarExpr::constant_value_with` reads a typed known-value environment without
cloning and substituting the expression tree. Each node checks its type and
operation before evaluating operands: mixed-width/signedness arithmetic requires
explicit conversions, even when operands are unknown. Malformed IR returns an
error. Floating remainder in the public scalar IR is an explicit `todo!()`
(panic), for both known and unknown operands; it must never be treated as an
unknown value or a successful proof. Evaluation budget exhaustion remains an
error, not evidence of program invalidity.

Known-value propagation preserves evaluation errors and aborts import with a
scalar-evaluation diagnostic; it no longer converts errors to unknown values.
This includes overflow or integer division by zero revealed by current flow
facts. Import can conservatively reject errors in branches being lowered even
if a later analysis could establish that they are unreachable. Unknown runtime
values still require backend definedness checks; import is not such a proof.
Comparison folding uses this
same evaluator, preserving integer checks and each floating rounding step.
Declarations and assignments propagate typed values; branch joins retain only
bit-identical facts; while headers and exits forget possibly written variables
and preserve read-only ones. This is not const qualification: mutable reads
remain illegal in const declarations and const-required sizes. Ordinary scalar
reads remain in executable IR. Both source branches are still lowered and
checked; this is not an unchecked dead-source elimination pass.
Source-level consumers temporarily overlay known scalar values on the scope
and restore it afterwards; this adapter still copies the scope, unlike the
read-only IR evaluator. Typed IEEE floats, exact-real gate expressions and
Boolean-word storage retain their distinct semantics.

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
