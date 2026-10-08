# Specification annotations

OpenQASM 3 annotations have their own mathematical expression language in
`iqir::annotation`, distinct from executable IR arithmetic. Pest generates the
parser from [spec.pest](../src/annotation/spec.pest); Pest's
[PrattParser](https://pest.rs/book/precedence.html) handles precedence.
There is no handwritten token scanner.

```qasm
pragma saria.def a(k: int) -> float = 1.0 / (2*k)!
pragma saria.def remaining(k: int) -> float = \cosh(1) - \sum(j in 0..k, a(j))
pragma saria.def stop_probability(k: int) -> float = k >= 5 ? 1 : a(k)/remaining(k)
@saria.requires n == 0 && !stop
@saria.invariant n <= 5 && stop_probability(n) > 0
@saria.loop_counter n
@saria.exit_probability == stop_probability(n)
@saria.terminates almost_sure
@saria.ensures stop
while (!stop) { /* original loop body */ }
```

This is a syntax example, not a proof of these properties. `Requires`,
`Ensures`, `Assert`, `Invariant`, `Terminates`, `LoopCounter`, and `ExitProbability` are
`AnnotationKind` variants. `AnnotationPayload` stores typed expressions,
termination modes, counter bindings, probability relations, and ghost updates,
never opaque expression strings. Source spans record the
original filename and exclusive UTF-8 byte range. Use
`program.annotations.get(&statement.ast_id())` to inspect a statement's list.

The intended boundaries are statement entry (`requires`), normal exit
(`ensures`), and every while-condition evaluation (`invariant`). `terminates`
is an obligation, not permission to assume termination. A consumer must check
preconditions in context and prove invariants rather than treating annotations
as established facts. [Quantum expressions](quantum-expressions.md) include typed
state literals, Pauli matrices, symbolic linear algebra, and comparisons between
program quantum references and same-width kets, such as `q == |0>`.
`\avg_density` and `\trace_distance` describe ensemble output comparisons.
General matrix constructors `\diag`, `\trace`, and `\normalize` remain reserved.

## Standalone assertions

`@saria.assert P` observes its own program point and requires a Boolean predicate.
It does not attach to the next statement and may end a block or file. Names are
resolved before leaving that block's scope. A preceding statement-attached
annotation still needs its executable statement; an assert cannot consume it.

IQIR anchors each assertion to an empty `Scope` sequence in the existing
annotation table. This preserves source order, AST identity, and spans without
adding an executable gate or a new statement kind. Consumers generate a proof
goal there; the annotation is not an assumption.

## Counter-indexed exit probability

`@saria.loop_counter n` selects one existing `int`/`uint` program or ghost
variable. It neither initializes nor updates it; resetting or decreasing the
counter is allowed. The payload resolves the name to its lexical `SymbolId`.
Constants, bit registers, and expressions such as `n + 1` are not counters.

`@saria.exit_probability R p` accepts `==`, `>=`, or `<=` and an `int`, `uint`,
`float`, or `real` expression, using the ordinary specification name and helper resolver.
Each annotated `while` must designate its own counter; nested loops do not
inherit one. Multiple probability clauses are conjunctive. Counter designation
and probability clauses may appear in either order, with names declared before use.

For every admissible active loop-head state, `p` uses this iteration's entry
values and bounds the probability of normal exit during the iteration: a `break`
targeting this loop or reaching the next guard with that guard false. Divergence
and other control transfers contribute no normal-exit probability. This is not
cumulative or eventual termination probability. An initially false guard starts
no iteration. Proving the bound defined, within `[0, 1]`, and satisfied is the
consumer's task; these annotations do not imply `terminates almost_sure`.

## Expression syntax

All built-in mathematical functions, binders and constants use a backslash:
`\sqrt(x)`, `\forall i in 0..n; p(i)`, `\pi`, `\inf`. Bare calls such as
`f(x)` resolve only to user-defined helpers. These namespaces are separate:
a helper named `sqrt` may coexist with `\sqrt`, but `sqrt(x)` without a helper
definition is an error. Unknown backslash names are parser errors, never helper
calls. Program identifiers remain unprefixed. Boolean literals `true`/`false`,
type names and annotation/pragma syntax are unchanged.

- Exact decimal/scientific rational literals, Booleans, `\pi`, `\tau`, `\euler`;
  classical program identifiers, bit indexing `c[0]`, scalar list indexing.
  `\inf` represents positive mathematical infinity, not IEEE floating infinity.
- `+ - * / %`, right-associative powers `^` or `**`, comparisons, `&&`, `||`,
  prefix `!`, and postfix factorial `!`. Power binds tighter than unary minus;
  factorial/indexing bind tighter than power. Write `0 <= n && n <= 5`, not
  chained comparisons. Classical division follows OpenQASM operand types:
  `1 / 2` is integer division; `1.0 / 2.0` is floating-point division.
  `%` is integer remainder (truncation-toward-zero convention). `=>` is logical
  implication (lower precedence than `||`); `condition ? a : b` is a piecewise
  expression. Empty/unselected branches do not bypass static sort checking.
- `\abs`, `\sqrt`, `\exp`, `\log` (natural), `\sin`, `\cos`, `\tan`, `\sinh`, `\cosh`,
  `\tanh`, `\asin`, `\acos`, `\atan`, `\floor`, `\ceil`, `\min`, `\max`, `\binom`.
  `\ln` aliases `\log`. `\binom(x,k)` is the generalized binomial coefficient
  for real x and nonnegative integer k, permitting the rewinding formula
  `(-1)^(m+1)*\binom(0.5,m)`. Factorial has domain nonnegative integers, with 0!=1.
- Aggregates: `\sum(j in 0..n, body)`, `\product(j in 1..=n, body)`,
  `\sup(x: float in 0..=1, body)`, `\infimum(x: float in 0..1, body)`.
  Quantifiers: `\forall j in 0..n; predicate`,
  `\exists j in 0..\inf; predicate`. Quantifiers do not wrap their declaration
  and body in parentheses; a semicolon separates them.
  The lower bound is inclusive; `..` excludes and `..=` includes the upper bound.
  Sum/product use integer indices; sums also admit complex scalars, kets, bras
  and operators of a fixed dimension. Products admit real/complex scalars only.
  An `\inf` upper endpoint denotes an infinite
  series/product (not finite unrolling). Empty sums yield the additive zero of
  the body type, including zero vectors/operators; empty scalar products are 1. Empty
  forall/exists are true/false. Supremum/infimum require a defined extremum in
  the chosen mathematical domain; convergence/definedness remain proof obligations.
  The index defaults to `int`, is local to the body and may shadow an outer name;
  bounds are resolved outside that new scope.
- `\probability(Boolean-event)` and `\expectation(numeric-expression)` are
  symbolic probabilistic terms. They refer to a measure supplied by a future
  verifier, not implicit independent sampling. Stopping-time variables/history
  are not synthesized automatically: pass explicit helper parameters or use
  declared program variables. Parsing does not prove probability/expectation laws.

### Quantifier scope

The backslash keywords and semicolon separator follow the
[ACSL convention](https://www.frama-c.com/html/acsl.html). The right-extending
body also follows the familiar binder style of
[Rocq](https://rocq-prover.org/doc/V9.2.0/refman/language/core/assumptions.html).
This is not an ACSL or Rocq parser: IQIR retains its own `name: type` declarations,
explicit numeric ranges, and `=>` implication operator.

The body consumes the complete expression to its right, including implication,
Boolean connectives, a conditional expression, and further quantifiers. An
enclosing delimiter (such as a closing parenthesis or an argument comma) ends
that expression. For example:

```text
\forall i in 0..n; \exists j in i..n; j >= i
\forall i: int in 0..n; i >= 0 => \sum(j in 0..=i, j) >= 0
(\forall i in 0..n; p(i)) && q(n)
```

The first example needs no parentheses for nesting. In the last example the
parentheses are necessary to keep `q(n)` outside the quantifier. Without them,
both sides of `&&` belong to its body. Similarly, `a => \forall i in 0..n; p(i)`
puts only the consequent under the quantifier. Helper names such as `p` and `q`
must be defined before use.

Each annotation/pragma still occupies one OpenQASM source line; quantifier
semicolons belong to the payload, not to executable OpenQASM statements.
Nested declarations bind one variable each and may depend on outer variables.
Range and sort checks are unchanged; quantification over an entire type without
an explicit range is not currently supported.

Use these backslash spellings instead of the former `forall(i in ..., body)`
and `sum(i in ..., body)` syntax. Built-in calls likewise require `\sin(x)` and
`\cosh(x)`. In Rust ordinary string literals, escape the backslash
as `\\forall`, or use a raw string such as `r"\forall i in 0..n; i >= 0"`.
OpenQASM source uses a single backslash.

## Pure auxiliary functions

`pragma saria.def name(parameter: type, ...) -> type = expression` defines a
top-level, non-executable helper. The complete definition occupies one line,
without a trailing semicolon (quantifier separators are allowed inside the
expression). Definitions are processed in source order and may call
earlier helpers. Duplicate names/parameters, reserved Boolean names, forward calls,
recursion and implicit capture of program state are rejected, even for unused
helpers. To use program state, pass it explicitly: `stop_probability(n)`.

Parameter/return types are classical scalar categories `bool`, `bit`, `int`,
`uint`, `float`, `angle`, with optional numeric widths such as `int[32]` and
`float[64]`. These are OpenQASM types: helpers and ghosts use the same finite-width
arithmetic, IEEE rounding, conversions and default widths as program variables.
Helpers additionally accept the widthless mathematical type `real`; ghost storage
does not. `\real(e)` embeds a finite machine value after evaluation: `\real(1/2)`
is zero, whereas `\real(1)/2` is exact one-half. `\real(0.1)` preserves the
binary64 value; use `\real(1)/10` for exact one-tenth. A real result type alone
does not change machine operations inside a helper body. There is no implicit
real-to-float conversion. `\factorial(n)` is exact and real-valued, with
nonnegative integer domain; postfix `n!` retains its machine result type.
Analytic builtins on real arguments return real results. Probability, real
expectation and trace distance are also real-valued quantities.
`bool`/`bit` are compatible but not implicitly numeric arithmetic operands;
bit-versus-integer equality is admitted. Source helper signatures cannot take or return
qubits, quantum vectors/operators, complex scalars or arrays. Their bodies may
contain quantum expressions whose final result has a classical signature type,
such as `\abs(<0| * (\cos(t)*|0> + \sin(t)*|1>))^2` returning `float`.

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
Quantum variables retain their program symbol IDs and their qubit/register
checking types. Equality/inequality with matching-width kets is admitted without
requiring a purity or state-equality proof. Register indexing and conditional ket
targets are supported; program quantum references are not general vector operands.
Mutable variables are never replaced by their known initializers. Constant
floats retain their already-rounded program value, represented exactly as a
rational. Scalar Boolean constants are substituted as Booleans; constant bit
arrays and fixed-width angle constants are not yet admitted in specifications.
Classical operations preserve the types and widths of their operands.
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
`invariant`, `terminates`, `loop_counter`, and `exit_probability` require a
retained `while`, not an expanded `for`.
Annotations on declarations/definitions and inside gate/subroutine definitions
are explicitly rejected, including unused definitions. Other annotation namespaces
and pragmas other than top-level `saria.def` are unsupported. Each annotation occupies
one line; a trailing `//` is part of its payload and is not a supported comment.

**Import checks syntax, arity, placement, binding, sorts and quantum dimensions.** Function
domains, index bounds, integer-to-uint obligations, factorial nonnegativity,
nonzero denominators, convergence, infinity arithmetic and actual predicates are
not proved. Parsing `n!` does not evaluate it. Quantum algebra is represented,
not evaluated or proved: there is no normalization proof, circuit-state extraction,
automatic HSL translation or theorem prover in this frontend.

Back to the [IQIR overview](../README.md).
