# Architecture

## Crate boundary

The root `irene` package depends on the standalone `iqir` workspace member.
IQIR owns OpenQASM 2/3 importing, program representation, and generic gate
metadata (`iqir::gate_shape`). The root Irene crate owns symbolic execution,
proof strategies, and solver integration; its equivalence-verification component
is called IreneQ. Full-unitary admission, positional wire pairing, and miter
construction live in `irene::equivalence::unitary_miter`. This is an executable
IR-to-IR transformation, but its interface and admission policy belong to the
verifier, not to the common IR.
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
cancellation, H conjugations, `S; Rx(pi/2); S -> H` (also its adjoint),
and `CX(a,b); CX(b,a); CX(a,b) -> SWAP(a,b)`.
The default `adjacent` strategy checks only neighboring live gates. `scan`,
`wire`, dependency-miter, and optional port matching discover wider candidates
but share the same rule matcher and exact crossing checks. The legacy `off`
setting means adjacent-only, with nonlocal search disabled.
The native scan/wire/DAG schedulers prioritize actual local triple matches
(including wires and angles) before pair fusion can hide them. They apply the
selected triple itself, not a competing pair at its endpoint; this is shared
scheduling, not a separate normalization pass for each identity.

The three-CX/SWAP identity is handled by the shared local rule matcher, including
dependency-miter reduction. There is no global wire-map propagation: SWAP gates
are not moved to the end of the circuit and later gates are not relabeled.
Global routing and common-prefix/suffix cancellation remain experimental and
are not enabled in the main version.

For a full-unitary exact trace certificate with rational squared modulus r,
`interval_hps::exact_trace_distance_lower` exposes the conservative rational
diamond-distance lower bound `2*(1-r)` (0 <= r <= 1). Consumers can reuse this
without recomputing the trace, but must subtract any preprocessing error.
The external experiment worker reports unified EQ/NEQ labels with separate
proof metadata; the library's `analyze` verdicts remain exact.

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

Local HPS analysis indexes phase selectors by their variables and reuses guard,
output and history dependencies while the component is unchanged. Every accepted
rewrite and subsequent simplification invalidates this snapshot. The original
candidate order and round-admission policy are preserved. An incidence budget
bounds the index; overflow falls back to scanning all selectors. Cheap and joint
phase analysis share lazily constructed cofactors for each candidate.

Before building cofactors, a bounded exact check may reject an impossible local
phase profile: Fourier/Omega require `4*(P(1,z)-P(0,z))` to be integral for every
assignment of the remaining variables. A nonintegral rational value at either
uniform assignment rules out these unconditional profiles. Quarter-turn terms
cannot affect this test; all other rational contributions are combined before
checking integrality. Unsupported coefficients or exhausted work make the check
inconclusive. Passing the check still requires the original exact proof, and
failing it is not a program non-equivalence certificate.

When the HPS path rules reach a fixed point, affine recovery checks whether a
guard or phase selector hides a constant or XOR of variables. A shared ordered
positive-Davio graph recognizes these functions without enumerating assignments;
its iterative evaluator is bounded by graph nodes and actual work, not input
count. Bounded sparse ANF is a fallback after a diagram refusal. Only proved
affine results are substituted, and phase coefficients are preserved exactly.
Recovered guards re-enter ordinary substitution before phase recovery. Queries
share a work budget within the reduction. Completed affine/non-affine conclusions
are cached on immutable Boolean nodes and reused across later reductions while
those nodes remain alive; the cache does not retain discarded source graphs.
Budget refusals are memoized only within the current attempt, so a later attempt
can retry. Cached facts do not include context-dependent elimination permission:
guards, outputs, coefficients and history are checked at the point of use.
Refusal leaves the original predicate intact. This is Boolean normalization,
not an extra path sum.

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
using directed MPFR intervals. Boolean guards remain exact; all bound paths
and symbolic inputs contribute to the normalized operator trace. Supported constant
sin/cos coefficients and linear pi/radian phases need not be cyclotomic.

Symbolic identity, contraction strategy, and numerical evaluation are separate:

- IQIR numeric expressions and HPS scalar/phase expressions retain their exact
  semantics. Interval endpoints never replace source expressions or identify them.
- [operator.rs](../src/equivalence/operator.rs) lowers local blocks with the ordinary
  HPS executor and visits every coherent input/path contribution. Both the exact
  and interval physical-wire backends consume this same semantics.
- [numeric.rs](../src/equivalence/numeric.rs) owns directed real/complex arithmetic,
  shared by approximate gate cancellation, structural HPS evaluation and the
  physical-wire frontier. An enclosure context chooses precision, not meaning.
- The exact backend retains coefficient polynomials; the structured backend
  retains its predicate DAG; the interval frontier uses dense complex enclosures.
  These internal data structures are deliberately not forced into one type.

Joint phase analysis maintains incremental node/edge budget counters for its
phase selectors and modular bit expressions. Replacing a root adds its new
reachable graph before removing the old one, so unchanged live subgraphs are
not traversed again. Counters retain their roots while using node identities;
removed nodes and retired roots are released. The original per-root accounting
(including repeated roots and sharing within each root), thresholds, and budget
check boundaries are unchanged. Budget refusal remains an inconclusive local
rule attempt, never an equivalence verdict.

Before constructing modular phase-addition expressions, joint analysis checks
sub-quarter bits on 64 exact Boolean assignments evaluated in parallel on the
existing XAG. A nonzero complete low-bit residue is a counterexample to the
unconditional Fourier/Omega precondition, not a program verdict. All-zero
probe results establish nothing: full symbolic analysis remains the fallback.
The symbolic adder never constructs carry out of its highest retained bit,
since arithmetic is modulo the phase denominator. Neither change approximates
phase coefficients or removes a contributing summand.

The structured interval backend interns arithmetic nodes in a `hashbrown`
unique table containing arena IDs; canonical node keys are stored only in the
arena. A separate computed table caches normalization results. Boolean predicates
have local IDs, cached supports and complement orientations, so arithmetic
constructors do not recursively compare predicates. Constants remain separate
owned enclosures: equal interval endpoints do not establish source equality.
Supports use sorted small vectors of local variable IDs, with the original
variable order retained for elimination tie breaking.

Contraction restricts operands before constructing their product and combines
the two eliminated branches immediately. Paired restriction shares the DAG
walk and skips unreachable selector branches; its node-indexed cache is tagged
by variable and stores only completed pairs. Sums and negation admit recursive
sum-out, while products stay factored and inverse/square-root operations are
restricted before evaluation, not commuted with summation. Variables absent
from the residual expression still contribute their factor of two. This is a
lightweight sum-product adaptation of the recursive fusion used by
[CUDD's matrix multiplication](https://github.com/ivmai/cudd/blob/master/cudd/cuddMatMult.c),
not a conversion to an ordered ADD or a new numerical backend. Resource refusal
does not cache an incomplete contraction or certify a verdict.

Full-unitary candidates of at most ten qubits can also contract their complete
operator on the physical wires. All input columns survive; this is not basis-state
sampling. The interval route first attempts
structured HPS trace contraction with a five-second cooperative deadline covering
execution, trace simplification and contraction, in addition to existing work
limits. Checks occur between complete rewrites and operations; a single operation
or cleanup may overrun the deadline. Expiry is inconclusive, never a contradiction,
and the scoped deadline is removed before any fallback. If the attempt expires
or its enclosure does not settle the target, it tries
the complete matrix frontier. If the short HPS probe expired and the matrix
refuses or remains inconclusive, a fresh HPS attempt runs with its ordinary
resource limits and without the five-second deadline. This reconstructs the HPS
rather than resuming an interrupted stack. A probe that completed within five
seconds is not repeated: its ordinary work limits have not changed. Certified
enclosures retain the tighter upper and lower bounds. Remaining queries continue
through the existing exact verification flow, including kernel reasoning when needed.
The interval frontier admits at most 1.5 billion projected cell/block steps and
uses a 180 s cooperative time budget. It first propagates three fixed normalized
inputs (basis states 0 and 1, and uniform plus). A phase-invariant pure-state
distance lower bound exceeding the target plus preprocessing error certifies
NEQ; agreement never certifies EQ. Otherwise it falls back to the complete
operator. Witness attempts, full contraction and precision retries share the
same work/time budget. Initialization and propagation errors bound the full
rectangular state matrix, without assuming its three columns are orthogonal.

Base contiguous blocks contain at most 64 gates and one mixing gate. The interval
frontier fuses adjacent pairs without changing gate order, using the shared HPS
lowering for their sparse transitions. Each fused block charges two original
block units, conservatively including an odd last singleton. Sparse rows use
rigorous short dot products, including gathered rows of three through eight terms.
Matrix arithmetic uses
FLINT/Arb complex balls, initially at 64-bit precision, with a 128-bit retry only
when the certificate is inconclusive and the shared time/work budget permits.
Gate coefficients still come from the shared certified numerical interpretation.
After each unitary block, the midpoint matrix is retained and the discarded
radii are accumulated as a rigorous operator-norm error. Specifically,
`||G U - midpoint(G M)|| <= ||U-M|| + ||G M-midpoint(G M)||` because `G` is unitary;
the new error is bounded by `sqrt(max_row_sum * max_column_sum)` of entry radii.
This avoids repeatedly propagating independent entry intervals through mixing
gates. A direct residual certificate `2*(||M-z I|| + error)`, for an enclosed
unit-modulus phase `z`, complements the trace upper bound without subtracting
nearly equal trace magnitudes. The normalized trace is separately widened by
the accumulated error before deriving its certified lower bound. Exceeding a
budget or failing to enclose a useful result
does not certify a verdict. Independently certified bounds may be intersected.
`identity_bound_with_tolerance` exposes this refinement target; the compatibility
entry point uses 1e-12. `identity_bound_with_error` also accepts the preprocessing
error for witness stopping; returned bounds still describe the supplied circuit
and must be corrected by the caller. Reports identify method and precision.

The exact frontier also admits ten qubits and up to 64 million projected table
steps (previously six qubits/one million steps); its separate coefficient-work
budget remains in force. Admitted exact frontiers are attempted before whole-HPS
construction and are not repeated after a budget refusal.

The complete interval contractions share trace-distance certificate code; the
three-input search instead certifies a particular input's output distance.
Exact `analyze` still accepts only exact evidence; interval certificates
are consumed by callers that explicitly request distance/tolerance reasoning.

The arithmetic DAG retains XAG predicates rather than truth tables. It traverses
scalar products iteratively, aligns identical/complementary Select conditions,
folds constants and extracts common products. Path elimination uses both symbolic
cofactors. Half-turn phases split via `(-1)^(f XOR g) = (-1)^f * (-1)^g`;
AND subgraphs are not expanded into ANF. Equal interval enclosures do not establish
expression equality. Structural growth remains resource-limited; diagnostics count
allocated DAG nodes. This route retains its 256-bit default precision.

For dimension d and normalized trace t, the channel diamond-distance bounds are:

```text
upper = min(2, 2*sqrt(2*d*(1-|t|)))
lower = 2*sqrt(1-|t|²)
```

The upper bound uses an interval lower bound on |t|. The lower bound comes from
a normalized maximally entangled input, using the upper endpoint of |t|² and
downward-rounded arithmetic. If the enclosure permits |t|=1, the lower bound is zero.
These bounds include the full summed amplitude and ignore global phase.

For tolerance-oriented callers, use local circuit reduction first, then the
certified interval bounds, and invoke expensive exact analysis only if the
enclosure straddles the tolerance. A strictly positive lower bound proves exact
non-equality but exceeds tolerance only when it is greater than the tolerance.
Keep these two verdicts separate. The `analyze` API and ordinary CLI remain
exact-only; orchestration of tolerance queries is the caller's responsibility.

Boolean-to-arithmetic phase lifting retains wide XORs as exact selectors rather
than enumerating their exponentially many products. Small lifts are bounded
before allocation; half-turn XOR phases can be added directly modulo one.

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
