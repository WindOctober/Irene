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

## Classical subroutine parameters and results

`def` supports numeric `int[n]`, `uint[n]`, `float[32/64]`, `bool`, `bit`,
and `bit[n]` parameters, alongside scalar/register qubit parameters. Classical
arguments are evaluated in the caller and copied into fresh mutable callee
locals before executing the body. Assigning a formal never updates the caller;
passing the same classical variable twice creates two independent copies.
Quantum parameters still reference caller wires and cannot overlap.

Numeric and bool/bit results can initialize a declaration or be the entire
right-hand side of an assignment. A final `return another_call(...)` can forward a result.
Return targets must match the declared numeric type/width or compatible bit
shape. A direct `if (predicate(...))` executes the call once before branching,
including its quantum effects. Nested calls through separate statements are
supported; recursive calls and exponential expansion are bounded/rejected.

Known actual values feed existing constant math and static `for` range
evaluation without making the formal `const`. Loop-carried values and unknown
actuals remain runtime values; `while` back edges invalidate flow facts. Lexical
lookup uses definition-time visibility, not caller locals or mutable globals.

This does not add general effectful calls inside arithmetic, call arguments,
short-circuit expressions or `while` conditions, nor non-final/conditional
returns, array-reference parameters, or missing scalar integer bitwise
operators. Those constructs still fail explicitly; refactoring cannot assume termination
or erase function side effects. Numeric `uint` storage follows the frontend's scalar-preservation option;
parameters, locals and return targets use the same choice. The default entry
uses Boolean words; bool/bit parameters also use the bit IR.

## Runtime integer for ranges

Compile-time integer ranges retain static expansion. An unknown
integer range `[start:stop]` or `[start:1:stop]` instead lowers to a scoped
`while` using the existing scalar IR. Both endpoints are evaluated once, before
declaring the source iterator. A hidden `limit` retains the original endpoint
even if the body changes the variable used to compute it.

The generated loop uses a private cursor and an active flag. Initially it is
active exactly when `start <= limit`. After the body, it stops if the cursor
equals the inclusive limit; otherwise it increments the cursor and restores
the source iterator for the next iteration. This avoids an extra increment at
the maximum representable endpoint, and body assignments to the source iterator
cannot change the range being traversed. Iterator and implementation locals
leave scope together. Entry-only constant facts are cleared for body lowering
so loop-carried updates cannot be incorrectly constant-folded.

This subset accepts integer endpoints compatible with the iterator's type and
width and a known step of positive one. Runtime descending/general-stride or
open-ended ranges and dynamic array/qubit indices remain
unsupported. It does not introduce a symbolic integer-shift or gate-angle
implementation merely because such an expression occurs inside the loop.

Loop annotations on a runtime `for` bind to the generated `while`, with the
source iterator visible in contracts. Existing loop-contract requirements still
apply; lowering does not assume a contract or prove termination. Attached ghost
declarations/assignments are unsupported;
declare ghosts in the enclosing scope instead. Import success alone does not
mean the loop or its assertions have been verified.

## Break and continue

`break` and `continue` target the innermost source loop, including static
integer `for`, runtime unit-step `for`, and `while`. Transfers cannot cross a
subroutine boundary. A callee can use transfers inside its own loops; a bare
transfer in a called body is rejected even when the caller is inside a loop.

The frontend emits native `Break` / `Continue` nodes. It creates no jump flags
and does not cache a while's source guard. Executors use `ExecutionFlow<T>`:
normal successors, break successors, and continue successors. These are
path-local control outcomes, not program variables or new SMT symbols. Only
normal successors execute a block suffix; lexical cleanup applies to all three.
No probability mass is discarded or renormalized when paths change outcome.

Static specialization preserves a finite `UnrolledLoop` boundary and its
iteration blocks, so a break skips subsequent iterations and a continue advances
to the next specialized iteration. Static qubit indices remain supported.
Runtime for retains the existing range snapshot/cursor/endpoint bookkeeping;
its `LoopBody { body, step }` routes continue to the update and break past it.
The endpoint's existing `active` bit is range bookkeeping, not a break/continue
flag. No wrapping final step is introduced.

Ordinary while keeps the source guard. A break never re-evaluates that guard
(it may now be undefined) and does not imply its negation. Contracts attach to
the actual While node without a jump-specific setup scope.

Irene executes finite specialized control flow. Until exit-sensitive liveness
is implemented, programs containing transfers use conservative unsliced
execution and project outputs only at program exit. Existing restrictions on
runtime loops and scalar storage in Irene's equivalence backend remain.

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

### Numeric boundary of gate parameters

There are three distinct domains, not one interchangeable representation of pi:

- Classical `float[32/64]` expressions, including source `pi` (binary64),
  retain their typed IEEE rounding steps.
- Explicit `angle[m]` values encode an integer `k` with mathematical value
  `2*pi*k/2^m`. Converting `float[n]` to `angle[m]` uses the source format's
  `float_n(2*pi)` period, nearest/even rounding, and reduction modulo one turn.
  This conversion uses exact rational arithmetic on the finite IEEE values;
  its output bit weights use mathematical pi, not the floating period.
  The source precision is retained, including for binary32 expressions.
- Standard-library gates have their specified mathematical matrices. `S`
  remains `diag(1,i)`, and controlled-standard-gate decompositions may use
  exact pi. They must not acquire source-level floating evaluation error.

For gate parameters without an explicit fixed-width angle conversion, Irene
currently chooses a continuous-radian verification profile: embed the final
IEEE value exactly in the mathematical gate, without further angle quantization.
This is an explicit modeling policy, NOT a claim that OpenQASM requires this
unique interpretation of unspecified-size gate angles. OpenQASM permits
arbitrary-precision gate algebra or a target-specific fixed angle precision.
The existing default width 32 applies to an `angle` declaration/cast without
a designator; it is not silently applied to every gate argument.

Consequently, under this profile `p(pi/2)` and `s` are not exactly identical.
`p(angle[32](pi/2))` and `s` ARE identical. The same distinction applies to
`t` and `p(pi/4)`. An `Unknown` result is not a proof of inequivalence, and
exact-equivalence tests must not be mass-updated to expect `Unknown`.
Changing the unspecified-size gate profile requires a separate, consistent
target decision across frontend and backends; it must not be approximated by
snapping nearby floating values to special angles. In particular, reducing a
continuous rotation argument modulo 2*pi can lose a controlled global phase.

References: [gate parameters](https://openqasm.com/language/gates.html#hierarchical-gates-definitions),
[float-to-angle casts](https://openqasm.com/language/types.html#casting-from-float),
and [standard gate matrices](https://openqasm.com/language/standard_library.html).

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

This remains a supported subset, not a full OpenQASM implementation: runtime array indexing, numeric
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
