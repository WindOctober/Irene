# Specification syntax

The standalone `iqir::annotation` API parses mathematical syntax independently
of executable IR. Pest recognizes the grammar in
[spec.pest](../src/annotation/spec.pest), and its
[PrattParser](https://pest.rs/book/precedence.html) handles operator precedence.

## Entry points

- `parse_expression(text)` returns a `SpecExpr`.
- `parse_annotation(text, span)` returns an `Annotation` with an
  `AnnotationKind`, typed payload, and caller-supplied source span.
- `parse_function(text, span)` returns a `SpecFunction` signature and body.

For example, `n! >= x` becomes a comparison whose left operand is a factorial
and whose right operand is a name. Neither the names nor the factorial are
evaluated. `0.5` and `5e-1` both become the exact rational number 1/2.

Annotation kinds are `Requires`, `Ensures`, `Invariant`, and `Terminates`.
The first three carry an expression; `terminates` currently accepts only
`almost_sure`, represented by a dedicated termination enum. A `SourceSpan`
records the original filename and a half-open UTF-8 byte range.

## Auxiliary-function syntax

```text
pragma saria.def a(k: int) -> float = 1 / (2*k)!
pragma saria.def remaining(k: int) -> float = cosh(1) - sum(j in 0..k, a(j))
@saria.invariant n <= 5 && remaining(n) > 0
```

A signature uses classical categories `bool`, `bit`, `int`, `uint`, `float`,
and `angle`. These describe mathematical values rather than machine widths or
IEEE rounding. Function parsing stores the signature and expression body only.

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
  expression. Parsing retains both branches; type checking is a separate consumer task.
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


## Parsing boundaries

These APIs parse syntax, not proofs or executable operations. They do not yet
provide name/type checking or OpenQASM statement attachment. Parsing
`@saria.requires 1`, for example, is not a claim that its payload is Boolean;
that obligation belongs to the checking layer.

Names remain `Name`, unknown calls remain `NamedCall`, and binder IDs remain
unassigned. Known mathematical function arities are checked by the parser.
Malformed syntax, unknown annotation kinds, trailing tokens, and exceeded
resource budgets produce errors. Budgets cover input bytes, operator count,
nesting, parse-tree size and numeric literal/exponent size.

Quantum/matrix AST variants are reserved syntax, not implemented quantum
semantics. Likewise, accepting probability, infinite series or factorial syntax
does not establish definedness, convergence, nonnegativity or any stated result.
The mathematical conventions above are obligations for consumers, not numerical
evaluation performed by the parser.

Back to the [IQIR overview](../README.md).
