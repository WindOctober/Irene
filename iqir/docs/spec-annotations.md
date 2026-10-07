# Specification annotations

OpenQASM 3 annotations have their own mathematical expression language in
`iqir::annotation`, distinct from executable IR arithmetic. Pest generates the
parser from [spec.pest](../src/annotation/spec.pest); Pest's
[PrattParser](https://pest.rs/book/precedence.html) handles precedence.
There is no handwritten token scanner.

```qasm
pragma saria.def a(k: int) -> float = 1 / (2*k)!
pragma saria.def remaining(k: int) -> float = cosh(1) - sum(j in 0..k, a(j))
pragma saria.def stop_probability(k: int) -> float = k >= 5 ? 1 : a(k)/remaining(k)
@saria.requires n == 0 && !stop
@saria.invariant n <= 5 && stop_probability(n) > 0
@saria.terminates almost_sure
@saria.ensures stop
while (!stop) { /* original loop body */ }
```

This is a syntax example, not a proof of these properties. `Requires`,
`Ensures`, `Invariant`, and `Terminates` are `AnnotationKind` variants.
`AnnotationPayload` holds either a `SpecExpr` tree or the typed termination
mode `AlmostSure`, never an opaque expression string. Source spans record the
original filename and exclusive UTF-8 byte range. Use
`program.annotations.get(&statement.ast_id())` to inspect a statement's list.

The intended boundaries are statement entry (`requires`), normal exit
(`ensures`), and every while-condition evaluation (`invariant`). `terminates`
is an obligation, not permission to assume termination. A consumer must check
preconditions in context and prove invariants rather than treating annotations
as established facts. Quantum/matrix operator AST variants from the initial
prototype are reserved, not developed further here. Classical import explicitly
rejects them rather than claiming to check their quantum semantics.

## Expression syntax

- Exact decimal/scientific rational literals, Booleans, `pi`, `tau`, `euler`;
  classical program identifiers, bit indexing `c[0]`, scalar list indexing.
  `inf` represents positive mathematical infinity, not IEEE floating infinity.
- `+ - * / %`, right-associative powers `^` or `**`, comparisons, `&&`, `||`,
  prefix `!`, and postfix factorial `!`. Power binds tighter than unary minus;
  factorial/indexing bind tighter than power. Write `0 <= n && n <= 5`, not
  chained comparisons. Division is mathematical, not OpenQASM integer division.
  `%` is integer remainder (truncation-toward-zero convention). `=>` is logical
  implication (lower precedence than `||`); `condition ? a : b` is a piecewise
  expression. Empty/unselected branches do not bypass static sort checking.
- `abs`, `sqrt`, `exp`, `log` (natural), `sin`, `cos`, `tan`, `sinh`, `cosh`,
  `tanh`, `asin`, `acos`, `atan`, `floor`, `ceil`, `min`, `max`, `binom`.
  `ln` aliases `log`. `binom(x,k)` is the generalized binomial coefficient
  for real x and nonnegative integer k, permitting the rewinding formula
  `(-1)^(m+1)*binom(1/2,m)`. Factorial has domain nonnegative integers, with 0!=1.
- `sum(j in 0..n, body)`, `product(j in 1..=n, body)`,
  `forall(j in 0..n, predicate)`, `exists(j in 0..inf, predicate)`,
  `sup(x: float in 0..=1, body)`, `infimum(x: float in 0..1, body)`.
  The lower bound is inclusive; `..` excludes and `..=` includes the upper bound.
  Sum/product use integer indices; an `inf` upper endpoint denotes an infinite
  series/product (not finite unrolling). Empty sums/products are 0/1; empty
  forall/exists are true/false. Supremum/infimum require a defined extremum in
  the chosen mathematical domain; convergence/definedness remain proof obligations.
  The index defaults to `int`, is local to the body and may shadow an outer name;
  bounds are resolved outside that new scope.
- `probability(Boolean-event)` and `expectation(numeric-expression)` are
  symbolic probabilistic terms. They refer to a measure supplied by a future
  verifier, not implicit independent sampling. Stopping-time variables/history
  are not synthesized automatically: pass explicit helper parameters or use
  declared program variables. Parsing does not prove probability/expectation laws.

## Pure auxiliary functions

`pragma saria.def name(parameter: type, ...) -> type = expression` defines a
top-level, non-executable helper. The complete definition occupies one line,
without a semicolon. Definitions are processed in source order and may call
earlier helpers. Duplicate names/parameters, builtin collisions, forward calls,
recursion and implicit capture of program state are rejected, even for unused
helpers. To use program state, pass it explicitly: `stop_probability(n)`.

Parameter/return types are classical scalar categories `bool`, `bit`, `int`,
`uint`, `float`, `angle`. They describe mathematical values, not machine storage:
no sized type spellings, IEEE rounding or wraparound occur in helper arithmetic.
`float`/`angle` admit real-valued formulas; integer arguments can be promoted to
them, not vice versa. `bool`/`bit` are compatible but not implicitly numeric
arithmetic operands; bit-versus-integer equality is admitted. Int/uint conversion
retains a nonnegative-value obligation when targeting uint; this checker does
not prove that obligation. Helpers cannot take or return qubits/matrices/arrays.

`ProgramData::spec_functions` stores bodies/signatures indexed by `FunctionId`.
`Parameter(index)` differs from program `SymbolId` and quantified `BoundVariable`.
`NamedCall` becomes `HelperCall` after resolution and argument/return sort checks.
`instantiate_function` substitutes already-checked arguments, alpha-renaming
callee binders to avoid capture; nested helper calls remain symbolic, not
recursively expanded. The substitution API does not re-check caller argument
types: callers must use `check_expression` first. Budgets bound parsing, checking,
definitions and substitution.

## Name resolution and checking

`parse_expression` parses standalone expressions with unresolved `Name` leaves
and `NamedCall` helper calls; standalone syntax parsing alone cannot reject a
call just because its definition has not been supplied. `check_expression` and
`define_function` resolve and check them before OpenQASM import returns.
OpenQASM import resolves names in the actual lexical scope into `SymbolId`
references; it substitutes constants and specialized static-loop indices.
Mutable variables are never replaced by their known initializers. Constant
floats retain their already-rounded program value, represented exactly as a
rational. Scalar Boolean constants are substituted as Booleans; constant bit
arrays and fixed-width angle constants are not yet admitted in specifications.
Specification operations themselves have no program bit-width wraparound.
Unknown names/functions/annotation kinds, trailing tokens, wrong arities,
misplaced loop annotations and dangling annotations are errors. Resource budgets
limit expression bytes, nodes, nesting and numeric exponent size.

## Statement attachment and transformations

Annotations bind to the whole lowered source operation: a broadcast keeps one
annotation on its grouping `Scope`, not a copy on each gate. Static-loop body
annotations get separate attachments and specialized indices for each instance.
AST-ID compaction remaps the annotation table. Specification-preserving rewrites
must preserve/remap attachments or explicitly reject the input. Equivalence
checking ignores annotations and specification helpers: they are not assumptions
or executable operations. The unitary miter leaves both source programs unchanged
and generates executable-only programs without specification metadata, since
inversion/composition changes specification boundaries.

## Supported scope and proof boundaries

Initial scope: executable statements at top level and in control-flow blocks.
`invariant` and `terminates` require a retained `while`, not an expanded `for`.
Annotations on declarations/definitions and inside gate/subroutine definitions
are explicitly rejected, including unused definitions. Other annotation namespaces
and pragmas other than top-level `saria.def` are unsupported. Each annotation occupies
one line; a trailing `//` is part of its payload and is not a supported comment.

**Import checks syntax, arity, placement, binding and classical sorts.** Function
domains, index bounds, integer-to-uint obligations, factorial nonnegativity,
nonzero denominators, convergence, infinity arithmetic and actual predicates are
not proved. Parsing `n!` does not evaluate it. No quantum state/operator algebra,
complex amplitudes, automatic HSL translation or theorem proving is implemented.
See `Saria/benchmark/classical-spec-coverage.md` in the surrounding workflow for
the corpus inventory and the distinction between formula coverage and proofs.

Back to the [IQIR overview](../README.md).
