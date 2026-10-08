# Quantum specification expressions

Quantum notation uses the same Pest grammar, expression AST, scope resolver and
type checker as [classical specification annotations](spec-annotations.md).
It describes mathematical vectors and operators, not executable gates or an
implicit query of a program's qubits. Parsing and checking do not prove equations.

## Literals

| Notation | Meaning | AST |
| --- | --- | --- |
| `\i` | Imaginary unit | `ImaginaryUnit` |
| `\I`, `\X`, `\Y`, `\Z` | One-qubit identity and Pauli matrices | `Pauli(Pauli)` |
| `\|0>`, `\|1>` | Computational basis kets | `Ket(Vec<QubitState>)` |
| `\|+>`, `\|->` | `(\|0> +/- \|1>)/\sqrt(2)` | `Ket` with `Plus` / `Minus` |
| `\|+i>`, `\|-i>` | `(\|0> +/- \i * \|1>)/\sqrt(2)` | `Ket` with `PlusI` / `MinusI` |
| `<0\|`, `<+\|`, `<+i\|` | Conjugate transposes of the corresponding kets | `Bra(Vec<QubitState>)` |

The backslashes before vertical bars in the table are Markdown escapes; source
code writes `|0>` and `<0|`, without those backslashes. Unicode delimiters
`|0⟩`, `⟨0|` and the minus label `|−⟩` are accepted as well. `|+i>` is one
Y-basis qubit, not a two-qubit product.

In the ordered basis `|0>`, `|1>`, the Pauli matrices have their standard meaning:
`I = [[1,0],[0,1]]`, `X = [[0,1],[1,0]]`, `Y = [[0,-i],[i,0]]`,
`Z = [[1,0],[0,-1]]`. See IBM's introductions to
[state vectors](https://learning.quantum.ibm.com/course/basics-of-quantum-information/single-systems)
and [Pauli operations](https://quantum.cloud.ibm.com/learning/en/courses/foundations-of-quantum-error-correction/stabilizer-formalism/pauli-operations-and-observables).
Plain `X`, `Y`, `Z`, `I` and `i` remain ordinary identifiers; only the backslash
spellings denote these constants.

`|01+->` stores four factors in written order and denotes
`|0> \otimes |1> \otimes |+> \otimes |->`. The leftmost factor is the leftmost
tensor factor; no program-register indexing or endianness convention is implied.
The AST preserves this literal without expanding a state vector. Named or
parameterized ket labels such as `|psi>` and `|n>` are not yet supported.

## Operations and types

```text
(|00> + |11>) / \sqrt(2)
\cos(theta)*|0> + \i*\sin(theta)*|1>
\X * |0>
(\X \otimes \Z) * |01>
|+> * <+|
\re(<+| * \X * |+>)
\sum(k in 0..n, (1/(k+1))*|0>)
```

In addition to classical types, the checker infers `Complex`, `Ket(n)`,
`Bra(n)` and `Operator(n)`, where `n` counts qubits, not vector entries.
Literals and tensor products currently support 1 through 64 qubits; they never
allocate exponentially sized vectors or matrices.

- `+`, `-` and unary `-` support like-dimensional vectors/operators and complex
  scalars. Real scalars promote to complex scalars when needed.
- `*` means scalar scaling, operator composition, operator-on-ket application,
  bra-on-operator application, bra-ket inner product, or ket-bra outer product.
  Inner products return `Complex`; outer products require matching qubit counts
  and return a square operator. Use explicit `*`: juxtaposition, `<0|0>` and
  `|0><0|` are not accepted.
- `\otimes` (also `⊗`) takes two kets, two bras, or two operators and adds their
  qubit counts. Multiplication/division bind more tightly than tensor product,
  which binds more tightly than addition. Parenthesize operator tensors before
  applying them, as in `(\X \otimes \Z) * |01>`.
- `/` supports division by real or complex scalars, with a nonzero-denominator
  proof obligation. Complex powers currently require an integer exponent.
- `\adjoint(expr)` conjugate-transposes a vector/operator or conjugates a scalar;
  `\conj`, `\re`, `\im` operate on real/complex scalars. `\abs` also accepts complex
  scalars and returns their real magnitude, not a vector norm.
- Equality checks compatible scalar types or identical quantum dimensions;
  ordered comparisons require real scalars. Conditions must remain Boolean.
  Sums allow fixed-dimensional vector/operator bodies. Quantifiers still bind
  numeric variables, not quantum states.

These are typing rules, not simplification rules: `\X * |0> == |1>` remains an
equation AST. Other real mathematical functions are not automatically extended
to complex arguments.

## Boundaries

Kets describe vectors, which may be unnormalized or zero. `==` is exact vector
or operator equality, not physical equivalence modulo global phase. For example,
`|0>` and `-|0>` are different vectors even though their outer products describe
the same pure-state density matrix. Normalization, positivity, Hermiticity,
unitarity, nonzero norms and series convergence remain proof obligations.

Classical program values and helper parameters may occur in amplitudes; ordinary
lexical binding and capture-avoiding helper substitution apply. Quantum leaves
do not introduce program symbol IDs. Source helper signatures remain classical.

Program-state queries such as `state(q)` and `\avg_density(q)` are not implemented.
In particular, `q == |0>` is not accepted: a program qubit is not implicitly a
pure-state vector. General matrix functions `\diag`, `\trace`, `\normalize` and
`\trace_distance` remain reserved. Equivalence checking continues to ignore all
specification annotations; this frontend does not change circuit semantics.
