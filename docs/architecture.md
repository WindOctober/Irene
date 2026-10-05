# Architecture

## Crate boundary

The root `irene` package depends on the standalone `iqir` workspace member.
IQIR owns OpenQASM 2/3 importing, program representation, and pure unitary
transformations. The root Irene crate owns symbolic execution, proof strategies, and solver
integration; its equivalence-verification component is called IreneQ.
The `irene::ir` re-export is the same API and types as `iqir`.
The `irene::frontend` re-export preserves the existing parser API. Independent
clients can use `iqir::frontend::parse_str` or `parse_file` to obtain a
`iqir::Program` without depending on Irene.

## Verification flow

Entry point: `equivalence::analyze(left, right, &interface)`.
The returned `Analysis` contains a verdict and `Evidence` identifying the proof route.

```text
OpenQASM 2 / 3 -> Program IR + input/output interface
                       |
                       +-- Full-unitary interface: L†R -> HPS -> normalized trace
                       |     Closed-form/local contraction or small-width matrix contraction
                       |     Return a proof, or continue below
                       v
                prepare_comparison -> two HPS representations + observable outputs
                       |
                       +-- Exact HPS / affine support / deterministic / pathwise XAG
                       v
                DensityKernel -> WorkingTerm
                       v
                Path reductions, factor proofs, guard grouping, coefficient aggregation
                       v
                Complete exact encoding -> SMT -> EQ / NEQ
                Unsupported encoding / exhausted resources / incomplete proof -> Unknown
```

Proof routes stop on sufficient evidence; a failed EQ shortcut does not establish NEQ.
Parsing and interface errors are reported separately from Unknown.

Before HPS execution, validated unitary programs use a shared
[exact rule set](../src/equivalence/unitary_rewrite/rules.rs): pair fusion and
cancellation, H conjugations, and `S; Rx(pi/2); S -> H` (also its adjoint).
The default `adjacent` strategy checks only neighboring live gates. `scan`,
`wire`, dependency-miter, and optional port matching discover wider candidates
but share the same rule matcher and exact crossing checks. The legacy `off`
setting means adjacent-only, with nonlocal search disabled.
The native scan/wire/DAG schedulers prioritize existing local triple shapes
before pair fusion can hide them; this is shared scheduling, not a separate
normalization pass for each identity.

Rules preserve full operator phase and numeric domains. Native Hadamard
matching uses the rotation's 4pi period, never rounds decimal angles, and does
not require unrelated circuit angles to be dyadic. Approximate dependency-miter
removals remain separate and retain their explicit diamond-error ledger.

Local basis reductions such as `H; Rx(theta); H -> Rz(theta)` (including
controlled-target variants) preserve the original angle and do not require a
whole-circuit Clifford/dyadic domain. They also benefit the general-channel
fallback. Trace-specific Rx/Ry expansion checks the bounded dyadic domain per
rotation, leaving unsupported angles unchanged. Backend admission is checked
after local processing; a remaining unsupported gate can still make trace
decline, but does not disable the shared local reductions. Diagonal rotations
are not rewritten back into mixing rotations, avoiding a lowering/rewrite cycle.

## Frontend and interface

- [Frontend](../iqir/src/frontend): names, scopes, types, constants, gate modifiers and source expansion.
- [Program IR](../iqir/src/lib.rs): gates, measurement, reset, classical expressions and control flow.
- [Interface](../src/equivalence/interface.rs): paired inputs, initialized ancillas and observable outputs.

`EquivalenceConfig::positional` constructs declaration-order input/output pairs.
Explicit pairs support partial and differently shaped interfaces. Arbitrary quantum
inputs, zero-initialized ancillas, classical observations and discarded outputs have
distinct semantics. The reversible route requires a full-unitary interface; it
does not invert measurement, reset or discard channels.

Typed floating constants retain their declared precision. Decimal radians are not
inferred to be rational multiples of pi. See [language support](language-support.md).

## HPS: paths and histories

A [Component](../src/symbolic/executor.rs) stores:

| Field | Meaning |
| --- | --- |
| `path_support` | Bound coherent summation variables |
| `guard` | Boolean conditions enabling this amplitude contribution |
| `scalar` | Real expression, including conditional, trigonometric and radical terms |
| `phase` | P in `exp(2πi P)` |
| `output.quantum/classical` | Current Boolean wire values and classical storage |
| `output.history` | Measurement/discard records that determine interference compatibility |

For each history h, sum component and path amplitudes into `A_h(q;x)`, then form
`Σ_h A_h(q;x) conjugate(A_h(q';x'))`. Components sharing a history may interfere;
they are not necessarily independent probabilistic branches. Empty history does
not imply empty path support.

[Region summaries](../src/symbolic/executor/region.rs) execute small regions on
fresh boundary inputs before composing them with the prefix. Boundaries include
all relevant live wires. Local branch merging is separate from whole-HPS rules
that require a single component.

## Boolean representation and matching

[`BooleanPolynomial`](../src/symbolic/boolean.rs) stores a shared XOR/AND graph
(XAG). `Monomial` is an algebraic view; AND construction does not distribute over
XOR. Construction folds constants and cancels duplicate XOR terms.
[xag.rs](../src/xag.rs) adds graph simplification, Davio decomposition and SMT lowering.

HPS and kernel reuse this representation with separate variable namespaces.
Structural identity proves equality; structural difference does not prove
functional inequality. Phase expressions are sums of Boolean selectors with exact
coefficients. Coefficient arithmetic uses a separate DAG: real addition is not XOR.

### Bound-path matching

The Exact-HPS route uses petgraph VF2 on colored syntax graphs. Only bound paths
may be renamed; fixed inputs, exact coefficients, guard multiplicity and ordered
output/history slots are preserved. Each proposed bijection is validated by
reconstructing every HPS field, consuming each component once.

Already aligned or uniquely named paths use a direct reconstruction check.
Otherwise VF2 is the sole matcher. Failure or resource exhaustion falls through
to kernel routes. Matching proves structural alpha-equivalence, not Boolean
functional equality or path-sum elimination.

## Algebraic reductions

[HPS optimization](../src/symbolic/optimize/mod.rs) and
[term aggregation](../src/equivalence/aggregate.rs) apply rules at their respective
semantic boundaries:

| Rule | Preconditions and effect |
| --- | --- |
| Fourier | `Σ_y (-1)^(yf) = 2[f=0]`; f may be nonlinear, but other summand fields must not depend on y |
| Omega, vacuous, history | Each has its own phase, scalar and observability conditions and normalization factor |
| Guard row space | bitgauss treats nonlinear monomials as formal columns, not new free variables |
| Unique-solution substitution | Prove `v=F` with v absent from F; substitute through guard, phase, scalar, output and history; no factor of two |
| Davio | Rewrite `F=F(0) XOR v*(F(0) XOR F(1))`; this is not summation over v |
| Contraction/cofactors | Sum both outcomes and retain every coherent contribution |

Only bound paths may be eliminated as summation variables. Refused reductions
retain the original expression or fall back; incomplete sums cannot certify a verdict.

## Density kernel and WorkingTerm

[kernel.rs](../src/equivalence/kernel.rs) introduces input/output variables and
ket/bra paths, with history compatibility, discarded-wire pairings and observable
output constraints. `WorkingTerm` organizes each term as:

```text
paths + constraints + coefficient + phase
```

Guards may overlap. Contributions with the same guard are summed before comparison.
Equal sums under corresponding guards prove equality even when groups overlap;
a failed group comparison cannot prove global NEQ because groups may cancel.

Implementations: [guard grouping](../src/equivalence/aggregate/exact_smt/guard_groups.rs),
[factor proofs](../src/equivalence/aggregate/factored.rs),
[graph reduction](../src/equivalence/aggregate/graph.rs).

## Exact coefficients and SMT

[exact_smt.rs](../src/equivalence/aggregate/exact_smt.rs) aggregates complete path
contributions into cyclotomic exponents and coefficients. Its supported fragment
is narrower than the general expression representation.

- General sparse exact encoding and closed cyclotomic arithmetic serve trace,
  local contraction and density comparisons.
- [coefficient_dag.rs](../src/equivalence/aggregate/exact_smt/coefficient_dag.rs)
  provides an optional Q(ζ8) route. Its four rational-valued basis coefficients
  use `Constant / Select / Add / Multiply / Scale` nodes, with XAG Select conditions.

Both kernels share one coefficient DAG; identical subexpressions are reused before
forming L−R. Every basis coefficient must be identically zero to prove EQ.
Guards remain in Select nodes and conditional coefficients.

Bit-vector phase arithmetic is intentionally modular. Integer/rational coefficient
arithmetic needs enough width to prevent overflow. SAT proves NEQ only for a
complete exact difference query, not an EQ-only sufficient test or an unsupported
expression represented by an arbitrary UF model.

Exact density/graph queries use Bitwuzla through [smt.rs](../src/equivalence/smt.rs).
Other routes may use a solver portfolio: one SAT/UNSAT answer suffices, non-answers
do not veto it, and conflicting answers produce an error. Solvers are resolved
as `bitwuzla`, `z3` and `cvc5` on `PATH`. The default per-solver limit is 30 seconds,
configurable through `IRENE_TUNE_SOLVER_SECONDS` and independent of any outer timeout.

### Numerical HPS certificates

[interval_hps.rs](../src/equivalence/interval_hps.rs) checks full-unitary identity
using 256-bit directed MPFR intervals. Boolean guards remain exact; all bound paths
and symbolic inputs contribute to the normalized operator trace. Supported constant
sin/cos coefficients and linear pi/radian phases need not be cyclotomic.

The arithmetic DAG retains XAG predicates rather than truth tables. It traverses
scalar products iteratively, aligns identical/complementary Select conditions,
folds constants and extracts common products. Path elimination uses both symbolic
cofactors. Half-turn phases split via `(-1)^(f XOR g) = (-1)^f * (-1)^g`;
AND subgraphs are not expanded into ANF. Equal interval enclosures do not establish
expression equality. Structural growth remains resource-limited; diagnostics count
allocated DAG nodes.

For dimension d and normalized trace t, the channel diamond-distance bounds are:

```text
upper = min(2, 2*sqrt(2*d*(1-|t|)))
lower = 2*sqrt(1-|t|²)
```

The upper bound uses an interval lower bound on |t|. The lower bound comes from
a normalized maximally entangled input, using the upper endpoint of |t|² and
downward-rounded arithmetic. If the enclosure permits |t|=1, the lower bound is zero.
These bounds include the full summed amplitude and ignore global phase.

Add certified preprocessing error to the upper bound; subtract it from the lower
bound and clamp at zero with `corrected_lower_bound`:

| Condition | Certificate |
| --- | --- |
| Corrected upper ≤ tolerance | Approximate EQ |
| Corrected lower > 0 | Exact NEQ |
| Corrected lower > tolerance | NEQ at that tolerance |

Exact NEQ and approximate EQ can coexist. A large upper bound or an uncancelled
symbolic term alone proves neither NEQ nor an error lower bound. This optional API
leaves exact `analyze` unchanged and declines dynamic channels, numeric inputs,
unsupported constants and exhausted contractions.

## Options and tests

| Option | Behavior |
| --- | --- |
| `IRENE_ALPHA_STATS=1` | Per-call bound-path matching diagnostics |
| `IRENE_XAG_DAVIO=reverse` | Default deterministic-output preprocessing; `forward` changes order, `off` disables it |

Davio preprocessing uses a shared ordered positive-Davio DAG before the Bitwuzla
miter. Input/node/work limits retain the original query on refusal or growth.
The exact-SMT encoder normally conditions later bound paths first, then applies
exact reductions and independent-factor decomposition. Both outcomes are summed;
free inputs remain free.

- `tests/equivalence.rs`, `tests/unitary_miter.rs`: comparisons and inverse-circuit admission.
- `src/symbolic/tests.rs`, `src/symbolic/optimize/tests.rs`: HPS execution and reductions.
- `src/equivalence/aggregate/exact_smt/tests.rs`, `exact_smt/coefficient_dag/tests.rs`
  and `exact_smt/frontier/tests.rs`: encoding and contraction.
- `tests/angles_constants.rs`, `tests/static_integers.rs` and frontend tests: source semantics.
