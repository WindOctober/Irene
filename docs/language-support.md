# Language support

Irene accepts subsets of OpenQASM 2 and 3.

## Barriers and gate extensions

Barriers, including `barrier;`, are semantic no-ops. Supplied operands still
undergo name, type and bounds validation.

Both frontends accept the corpus extension `ccz`: three distinct qubits, no
parameters, and a minus sign only on the `|111>` amplitude. OpenQASM 3 also
accepts `ctrl @ cz` and `ctrl(2) @ z`.

## Constants

OpenQASM 3 constants support `int`/`uint`, `bool`, `bit` up to 64 bits,
`float[32/64]` and `angle`. Constants are immutable and lexically scoped;
integer widths and indices may use constant expressions.

Floating constants use IEEE binary32/64 arithmetic and retain rounded dyadic
values at gate-parameter use sites; they are not replaced by ideal multiples
of pi. Defaults: 64-bit float, 32-bit int/uint and angle.

## Runtime angles

`angle[n]`, for n=1–61, represents `2*pi*k/2^n` exactly with arithmetic modulo
`2^n`. Supported operations:

- Indexed measurement and assignment.
- Same-width addition, subtraction, comparisons and bitwise operations.
- Negation, static shifts and explicit same-width `bit[n]` reinterpretation.
- `p/rx/ry/rz` and their controlled forms, including `inv`, through exact
  conditional rotations without enumerating angle values.

Float initialization uses certified nearest/even rounding with MPFR intervals.
Word assignments snapshot RHS bits before writing. Uninitialized reads are errors.

## Unsigned integer storage

Mutable `uint[n]` supports compile-time widths 1–64, exactly representable static
initializers, same-width copies/comparisons and explicit same-width `bit[n]` casts.
Explicitly sized words also support bit indexing, bitwise operations and static
logical shifts, including compound assignments.

Shifts discard shifted-out bits. Word assignments preserve simultaneous reads.
Unsized `uint` defaults to 32 bits and retains its restriction on bit-level
operations. Mutable values cannot determine type widths, even with constant
initializers. Uninitialized storage is not zero-initialized.

## Gate powers

Integer `pow(k)` accepts literal/const exponents and values proved constant by
known-bit propagation through assignments, static loops and branch joins.
Products of `pow` modifiers and `inv` compose exactly.

| Gate family | Lowering |
| --- | --- |
| Phase and axis rotations | Scale the parameter exactly, without re-rounding typed floats |
| S/T families | Reduce exponent modulo 4/8 |
| Involutions | Reduce exponent modulo 2 |
| Supported controlled forms | Preserve controls; controlled S/T, H and SWAP lower to existing exact gates |

Overflow, unknown/noninteger exponents, arbitrary user-defined circuit powers,
fractional matrix powers and dynamic exponent synthesis are unsupported.
Lowering introduces neither a new kernel operator nor repeated-gate expansion.
Zero powers still validate parameter domains and classical reads.

The four-parameter `cu` decomposition contains noncommuting rotations.
`inv @ cu` and combined integer powers outside `{0, 1}` are rejected rather
than implemented by scaling its individual rotations.

## Remaining limitations

Unsupported operations include mutable floating-point and integer arithmetic,
general constant functions, angle multiplication/division, dynamic shifts and
width-changing angle casts. The 61-bit angle limit preserves the exact phase
denominator range, including half-angle rotations. Symbolic numeric `input`
parameters use a separate interface.

The frozen IPE example's `pow(power)` calls are supported, but its left program
reads an uninitialized angle and its right program requires U with runtime-angle
parameters. The benchmark inputs retain these limitations.
