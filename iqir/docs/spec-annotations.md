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


## Pure auxiliary functions

Use `parse_function` on
`pragma saria.def name(parameter: type, ...) -> type = expression`, then pass the
result to `define_function` with a caller-owned function table. Helpers are
non-executable. Definitions are registered in source order and may call
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

The caller-owned `Vec<SpecFunction>` stores bodies/signatures indexed by `FunctionId`.
`Parameter(index)` differs from program `SymbolId` and quantified `BoundVariable`.
`NamedCall` becomes `HelperCall` after resolution and argument/return sort checks.
`instantiate_function` substitutes already-checked arguments, alpha-renaming
callee binders to avoid capture; nested helper calls remain symbolic, not
recursively expanded. The substitution API does not re-check caller argument
types: callers must use `check_expression` first. Budgets bound parsing, checking,
definitions and substitution.


## Name resolution and checking

`check_expression` uses the same checker as helper definitions. Its resolver
callback supplies program-variable bindings and classical types. Local binder
names take precedence over helper parameters, which take precedence over the
resolver. Bounds are checked before entering the new binder's scope.

Parsing alone retains `Name` and `NamedCall`. Checking turns them into
`Symbol`/constant values, `Parameter`, `BoundVariable`, and `HelperCall`
references. Arithmetic, logical operators, mathematical functions, helper calls
and binder bodies have their argument/result sorts checked. Both branches of a
conditional are checked, even when its condition is a constant.

For example, factorial requires an integer operand, probability requires a
Boolean event, and sum/product require integer indices with numeric bodies.
Quantifiers require Boolean bodies. Quantum/matrix operators are explicitly
rejected by the classical checker.

## Checking boundaries

The standalone APIs do not attach specifications to OpenQASM statements.
A caller checking a precondition/invariant must also require a Boolean result
from `check_expression`; the generic expression checker admits numeric results.

Syntax errors, unresolved names/functions, wrong arities and incompatible sorts
are rejected. Parsing, checking, helper definitions and substitution have resource
budgets. Checks do not discharge factorial nonnegativity, uint nonnegativity,
index bounds, nonzero denominators, convergence or any asserted property.
They do not evaluate helpers or infer a probability measure.

Back to the [IQIR overview](../README.md).
