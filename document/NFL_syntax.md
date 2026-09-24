# NFL Syntax Reference

NFL (Natural Formal Language) represents mathematical objects, assumptions,
and propositions. In this benchmark, an NFL file specifies a single proof
gap. A candidate proof is written separately in the [proof DSL](DSL_guide.md).

## Reading a benchmark gap

```text
PROOF GAP @1
ASSUM:

GOAL:
forall (n), n ∈ NonNegIntegerSet ∧ n = 1 ⇒ 1 = frac(n * (n + 1) * (2 * n + 1), 6)

METHOD:
```

`ASSUM:` lists premises as `hypothesis 1. ...`, `hypothesis 2. ...`, and so on.
It may be empty. `GOAL:` gives the proposition to prove. `METHOD:` is the
method field, which may also be empty. The identifier after `PROOF GAP` is
local to the exercise. Preserve the complete gap when running the verifier.

This reference describes mathematical term syntax, including the explicit
function forms found in the printed benchmark. It does not require writing
a full NFL proof narrative: the submitted answer is a DSL script.

### Text conventions

- Files use UTF-8. Use explicit `*` for multiplication and parentheses to
  make grouping clear.

- Implication is `⇒` or `=>`; equivalence is `⇔` or `<==>`.
  `→` / `->` is used for an approach relation or a function type, not implication.

- Conjunction is `∧` or `/\`; disjunction is `∨` or `\/`.
  ASCII comparisons `<=`, `>=`, and `!=` are also accepted.

- Bind variables explicitly. For example, write
  `forall (x), x ∈ RealSet ⇒ P(x)` and
  `exists (x), x ∈ RealSet ∧ P(x)`.
  The implication and conjunction in these examples have different meanings.

- A backtick-quoted name is a variable. Do not quote built-in constants or
  operators such as `π`, `RealSet`, or `PowerSet` as variables.


## 1. Grammar Specification

The grammar specification is written in Extended Backus-Naur Form (EBNF).

### Symbol Conventions

- Terminal symbols are enclosed in double quotes, e.g., `" ... "`.
- Repetitive constructs are enclosed in curly braces, `{ ... }`, indicating the contained sub-expression can appear zero or more times.
- Optional constructs are enclosed in square brackets, `[ ... ]`, indicating the contained sub-expression can appear zero or once.
- Grouping is enclosed in parentheses, `( ... )`, used to treat multiple sub-expressions as a whole.
- Comments are indicated by `(* ... *)`.

### Main Non-terminal Symbols

- `term`: A mathematical object or a proposition.
- `infinity`: An infinite endpoint.
- `interval`: An interval with specified open or closed endpoints.
- `big_oper`: A mathematical operator with a bound variable or range.
- `lambda_binder`: A variable bound by an anonymous function.

### EBNF Definition of Term
Uses `string` for strings, `integer` for decimal integers, and `decimal` for decimal fractions.

```ebnf
term =
| string
(* Variable names, e.g., `x`, `A0`, `φ'`; can also be predefined constant, function, or predicate symbols. Predefined symbols should refer to the symbol table below *)
| integer
(* Decimal integer *)
| decimal
(* Decimal fraction *)
| infinity
(* Infinity *)
| interval
(* Interval *)
| "(" , term , ")"
(* Parenthesized `term`, used to change operation precedence or eliminate ambiguity *)
| term , "(" , term , { "," , term } , ")"
(* Function application, predicate application; the `term` on the left of the parenthesis should be a function or predicate symbol, applied to the arguments inside the parenthesis *)
| "+" , term
(* Identity operation *)
| term , "+" , term
(* Addition *)
| "-" , term
(* Negation *)
| term , "-" , term
(* Subtraction *)
| "±" , term
(* Plus-minus sign *)
| term , "±" , term
(* Addition-subtraction sign *)
| term , "*" , term
(* Multiplication *)
| term , "/" , term
(* Division *)
| term , "mod" , term
(* Modulo operation *)
| term , "!"
(* Factorial *)
| term , "^" , "{" , term , "}"
(* Exponentiation, superscript; if the superscript is a simple `term`, braces can be omitted *)
| term , "_" , term
(* Subscript; if the subscript is a simple `term`, braces can be omitted *)
| "|" , term , "|"
(* Absolute value, norm, cardinality *)
| "frac" , "(" , term , "," , term , ")"
(* Fraction notation, `frac(numerator, denominator)` used for explicit fraction layout in proofs *)
| "sqrt" , "(" , term , ")"
(* Square root *)
| "sqrt" , "(" , term , "," , term , ")"
(* N-th root, first argument is the root index, second is the radicand *)
| "max" , "(" , term , { "," , term } , ")"
(* Maximum *)
| "min" , "(" , term , { "," , term } , ")"
(* Minimum *)
| "sup" , "(" , term , ")"
(* Supremum, the `term` in parenthesis should be a set *)
| "inf" , "(" , term , ")"
(* Infimum, the `term` in parenthesis should be a set *)
| "ln" , "(" , term , ")"
(* Natural logarithm *)
| "lg" , "(" , term , ")"
(* Base-10 logarithm *)
| "log" , "(" , term , "," , term , ")"
(* Logarithm: base first, argument second *)
| "∅"
(* Empty set *)
| term , "∈" , term
(* Set membership (in) *)
| term , "∉" , term
(* Set non-membership (not in) *)
| "{" , term , { "," , term } , "}"
(* Set defined by enumeration *)
| "{" , term , "|" , term , { "," , term } , "}"
(* Set defined by description (set-builder notation), left is the generator, right is one or more conditions *)
| term , "∩" , term
(* Intersection *)
| term , "∪" , term
(* Union *)
| term , "\" , term
(* Set difference *)
| "fun" , lambda_binder , { "," , lambda_binder } , [ "[" , term , "]" ] , "." , term
(* Anonymous function, with an optional domain condition *)
| term , "∘" , term
(* Function composition, relation composition *)
| term , "'"
(* First derivative, or part of a variable name *)
| "NthDeri" , "(" , term , "," , term , ")"
(* Higher-order derivative; ordinary powers are not derivatives *)
| "diff" , [ "^" , "{" , term , "}" ] , "(" , term , ")"
(* Differential symbol *)
| "pdiff" , [ "^" , "{" , term , "}" ] , "(" , term , ")"
(* Partial differential symbol *)
| big_oper , "(" , term , ")"
(* Operator application, e.g., `lim_{n → +∞} (1 / n)` *)
| term , "|" , "_" , "{" , term , "}" , "^" , "{" , term , "}"
(* Vertical bar evaluation, represents the difference of a univariate function or expression evaluated at two endpoints *)
| "bar" , "(" , term , ")"
(* Closure, conjugation, overline notation *)
| "(" , term , { "," , term } , ")"
(* Ordered tuple *)
| term , "·" , term
(* Vector dot product *)
| term , "×" , term
(* Vector cross product *)
| "cases" , "{" , term , "if" , term , { ";" , term , "if" , term } , [ ";" , "otherwise" , term ] , "}"
(* Piecewise function *)
| "..."
(* Ellipsis, indicating pattern continuation *)
| term , "=" , term
(* Equality *)
| term , "≠" , term
(* Inequality *)
| term , ">" , term
(* Greater than *)
| term , "≥" , term
(* Greater than or equal to *)
| term , "<" , term
(* Less than *)
| term , "≤" , term
(* Less than or equal to *)
| term , "→" , term , [ "^-" | "^+" ]
(* Approaches *)
| term , "→" , "_" , "{" , term , "→" , term , [ "^-" | "^+" ] , "}" , term
(* Approaches with subscript condition *)
| term , "∼" , "_" , "{" , term , "→" , term , [ "^-" | "^+" ] , "}" , term
(* Asymptotic equivalence with subscript condition *)
| term , "≈" , term
(* Approximately equal *)
| term , "≡" , term
(* Identically equal *)
| "¬" , term
(* Logical negation *)
| term , "∧" , term
(* Logical conjunction (AND) *)
| term , "∨" , term
(* Logical disjunction (OR) *)
| term , "⇒" , term
(* Logical material implication *)
| term , "⇔" , term
(* Logical equivalence *)
| "forall" , { "(" , term , ")" } , "," , term
(* Universal quantifier *)
| "exists" , { "(" , term , ")" } , "," , term
(* Existential quantifier *)
| term , { "," , term } , "∈" , term
(* Membership relation *)
| term , { "," , term } , "⊆" , term
(* Subset relation *)
| term , ":" , term , "→" , term
(* Function type annotation *)
| term , "[@scope" , term , "@]"
(* Conditional qualification *)
;

lambda_binder =
| string
| string , ":" , type_name
(* Optional type, e.g. Real or Integer; printed gaps often put domains in [ ... ] *)
;

infinity =
| "∞"
| "+∞"
| "-∞"
;

interval =
| "(" , term , "," , term , ")"
(* Open interval *)
| "[" , term , "," , term , ")"
(* Left-closed right-open interval *)
| "(" , term , "," , term , "]"
(* Left-open right-closed interval *)
| "[" , term , "," , term , "]"
(* Closed interval *)
;

big_oper =
| "sum" , "_" , "{" , term , "}" , [ "^" , "{" , term , "}" ]
(* Summation operator *)
| "prod" , "_" , "{" , term , "}" , [ "^" , "{" , term , "}" ]
(* Product operator *)
| "union" , "_" , "{" , term , "}" , [ "^" , "{" , term , "}" ]
(* Union operator *)
| "inter" , "_" , "{" , term , "}" , [ "^" , "{" , term , "}" ]
(* Intersection operator *)
| "seqlim" , "_" , "{" , term , "→" , term , "}"
(* Sequence limit *)
| "seqlimsup" , "_" , "{" , term , "→" , term , "}"
(* Sequence limit superior *)
| "seqliminf" , "_" , "{" , term , "→" , term , "}"
(* Sequence limit inferior *)
| "lim" , "_" , "{" , term , "→" , term , [ "^-" | "^+" ] , "}"
(* Limit (left/right) operator *)
| "limsup" , "_" , "{" , term , "→" , term , [ "^-" | "^+" ] , "}"
(* Limit superior (left/right) operator *)
| "liminf" , "_" , "{" , term , "→" , term , [ "^-" | "^+" ] , "}"
(* Limit inferior (left/right) operator *)
| "int" , [ "_" , "{" , term , "}" , "^" , "{" , term , "}" ]
(* Integral operator *)
| "bigO" , "_" , "{" , term , "→" , term , [ "^-" | "^+" ] , "}"
(* Big O notation *)
| "littleo" , "_" , "{" , term , "→" , term , [ "^-" | "^+" ] , "}"
(* Little o notation *)
;
```

### Grammar Rules Explanation

- **Sequence representation**: Use function notation `a(n)` for the `n`-th term of sequence `a`.
- **Limit information**: Limit information in approach relations, asymptotic equivalence, etc., must be written in subscripts.
- **Derivatives**: `f'` denotes a first derivative. Use `NthDeri(f, n)` for a higher-order derivative, or the explicit `FunDeri` / `ValDeri` forms below. A power such as `f^{2}` is not a second derivative.
- **Differential notation**: `diff(term)`, `pdiff(term)` use function form; multiple differentials are connected by multiplication (e.g., `diff(x) * diff(y)`).
- **Integrals**: An integral operator applies to one parenthesized integrand including its differential factors, e.g., `int_{a}^{b}(2 * x^{2} * diff(x))`. Join multiple differential factors with `*`.
- **Conditional qualification**: `[@scope term @]` is used to specify variable ranges.

### Notes

- The EBNF summarizes the term language; named operators also use the general function-application rule. Parsing a term does not establish its mathematical truth or guarantee solver support.
- Propositions are also treated as `term`.
- Parentheses must be used to clarify precedence when ambiguity exists.

---

## 2. Forms used in printed gaps

### Functions and domains

```text
f : RealSet → RealSet
I : CartesianProd(RealSet, RealSet) → RealSet
fun x [x ∈ RealSet ∧ x ≥ 0] . (x^{2} + 1)
fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . (x + y)
```

The expression after `.` is the body; the bracketed condition specifies the
local domain. Parenthesize a compound body when embedding it in another term.
`RealSet` denotes the set of real numbers in a proposition. A typed binder
such as `fun x: Real . (x^{2})` uses a type name instead.
`type_name` in the grammar denotes such a binder type, for example `Real`,
`Integer`, or a function type such as `Real -> Real`.

### Calculus

| Form | Meaning |
| --- | --- |
| `FunDeri(f, i, n)` | Derivative function of order `n` with respect to argument position `i` |
| `FunDeri(f, 1, 1)(a)` | Value of the first derivative of a unary function at `a` |
| `FunDeri(I, 1, 1)(a, b)` | Partial derivative of `I` in its first argument, evaluated at `(a, b)` |
| `ValDeri(f, x, n)` | Derivative of an expression `f` of order `n` with respect to variable `x` |
| `DefInt(a, b, integrand)` | Definite integral, with differential factors included in `integrand` |
| `lim_{x → a}(f(x))` | Function limit |
| `lim_{x → a^+}(f(x))`, `lim_{x → a^-}(f(x))` | Right and left limits |
| `seqlim_{n → +∞}(a(n))` | Sequence limit |
| `sum_{k = 1}^{n}(a(k))` | Sum over the stated index range |

For example, a printed integral may have the form:

```text
DefInt(0, +∞,
  (fun x [x ∈ RealSet ∧ x ≥ 0] . frac(1, 1 + x^{2}))
  * diff(fun x [x ∈ RealSet ∧ x ≥ 0] . x))
```

The differential is part of the mathematical expression. Keep the variable,
domain, and bound-variable scope when copying formulas into DSL commands.
Do not replace a local bound variable with a same-named global parameter.

### Intervals and piecewise terms

Both endpoint notation and named interval constructors may appear:

| Constructor | Interval |
| --- | --- |
| `IntervalLoRo(a, b)` | `(a, b)`, both endpoints open |
| `IntervalLcRo(a, b)` | `[a, b)`, left closed, right open |
| `IntervalLoRc(a, b)` | `(a, b]`, left open, right closed |
| `IntervalLcRc(a, b)` | `[a, b]`, both endpoints closed |

An open interval `(a, b)` can be visually confused with an ordered pair.
Retain `IntervalLoRo(a, b)` when it appears in a gap.

```text
cases{ x if x ≥ 0; -x if x < 0 }
```

## 3. Symbol Table

Besides symbols defined in the grammar specification, see the table below for meanings of other symbols.

### Constant Symbols

| Mathematical Object | Formal Language Representation |
|---|---|
| Imaginary unit | `__IMAGINARY_UNIT__` |
| Pi | `π` |
| Base of natural logarithm | `e` |
| Set of natural numbers | `NonNegIntegerSet` |
| Set of positive integers | `PosIntegerSet` |
| Set of integers | `IntegerSet` |
| Set of rational numbers | `RationalSet` |
| Set of positive rational numbers | `PosRationalSet` |
| Set of real numbers | `RealSet` |
| Set of positive real numbers | `PosRealSet` |
| Set of complex numbers | `ComplexSet` |
| Set of prime numbers | `PrimeSet` |

The printed numeric sets also include `NegIntegerSet`, `NonPosIntegerSet`,
`NegRationalSet`, `NonPosRationalSet`, `NonNegRationalSet`, `NegRealSet`,
`NonPosRealSet`, and `NonNegRealSet`. These names distinguish strict sign
conditions from non-strict ones. `NonNegIntegerSet` includes zero.

### Function Symbols

| Mathematical Object | Formal Language Representation |
|---|---|
| Cube root of $x$ | `cbrt(x)` |
| Sine of $x$ | `sin(x)` |
| Cosine of $x$ | `cos(x)` |
| Tangent of $x$ | `tan(x)` |
| Cotangent of $x$ | `cot(x)` |
| Secant of $x$ | `sec(x)` |
| Cosecant of $x$ | `csc(x)` |
| Arcsine of $x$ | `arcsin(x)` |
| Arccosine of $x$ | `arccos(x)` |
| Arctangent of $x$ | `arctan(x)` |
| Arccotangent of $x$ | `arccot(x)` |
| Arcsecant of $x$ | `arcsec(x)` |
| Arccosecant of $x$ | `arccsc(x)` |
| Hyperbolic sine of $x$ | `sinh(x)` |
| Hyperbolic cosine of $x$ | `cosh(x)` |
| Hyperbolic tangent of $x$ | `tanh(x)` |
| Hyperbolic cotangent of $x$ | `coth(x)` |
| Hyperbolic secant of $x$ | `sech(x)` |
| Hyperbolic cosecant of $x$ | `csch(x)` |
| Sign of $x$ | `sgn(x)` |
| Floor of $x$ | `floor(x)` |
| Ceiling of $x$ | `ceil(x)` |
| Gradient of scalar field $f$ | `grad(f)` |
| Divergence of vector field $F$ | `div(F)` |
| Curl of vector field $F$ | `rot(F)` |
| Nabla operator | `nabla` |
| Union of set | `SetUnion(S)` |
| Intersection of set | `SetInter(S)` |
| Power set | `PowerSet(S)` |
| Set difference | `SetMinus(A, B)` |
| Cartesian product | `CartesianProd(A, B)` |
| Domain | `Dom(f)` |
| Inverse function | `InverseFunc(f)` |
| Maximum point | `MaximumPoint(f)` |
| Minimum point | `MinimumPoint(f)` |
| Restriction function | `RestrictFunc(f, S)` |
| Oscillation | `OscillationAt(f, x)` |
| Set of accumulation points | `AccumulationPointSet(a)` |
| Radius of convergence | `RadiusOfConvergence(a)` |

### Predicate Symbols

| Mathematical Object | Formal Language Representation |
|---|---|
| Exists unique | `ExistsUnique(x, P(x))` |
| Non-existent | `NonExistent(x)` |
| Odd/Even | `Odd(x)` / `Even(x)` |
| Big enough / Small enough | `BigEnough(x)` / `SmallEnough(x)` |
| Set properties | `FiniteSet(S)`, `CountableSet(S)`, etc. |
| Function injective/surjective/bijective | `InjectiveFunc(f)`, `SurjectiveFunc(f)`, `BijectiveFunc(f)` |
| Periodic function | `PeriodicFunc(f, T)` |
| Convex/Concave function | `ConvexFunc(f)`, `ConcaveFunc(f)` |
| Boundedness | `BoundedFunc(f)`, `BoundedAboveFunc(f)`, etc. |
| Monotonicity | `MonoIncFunc(f)`, `StrictMonoDecFunc(f)`, etc. |
| Continuity | `ContinuousFunc(f)`, `UniformContinuousFunc(f)`, etc. |
| Differentiability | `DiffableFunc(f)`, `ContinuouslyDiffableFunc(f)` |
| Integrability | `IntegrableFunc(f)`, `SquareIntegrableFunc(f)` |
| Sequence properties | `IsSeq(a)`, `ConvergentSeq(a)`, `CauchySeq(a)` |
| Series properties | `ConvergentSeries(S)`, `AbsoluteConvergentSeries(S)` |

## Using NFL formulas in proofs

NFL describes the formulas inside DSL descriptors, such as
`(hypothesis 1: {x ∈ RealSet})` and `(GOAL: {x = x})`.
Use the exact current hypothesis or goal when a command asks for it. A
well-formed formula alone is not a proof; follow the [DSL guide](DSL_guide.md)
and the [verifier instructions](../ProofGap_nfl/README.md#run-the-verifier).
The allowed named theorems are listed in the
[theorem library](../ProofGap_nfl/thm/all_lib_idx.md).
