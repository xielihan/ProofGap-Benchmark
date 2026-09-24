# DSL Proof Guide

The proof DSL is a sequence of commands that transforms a proof gap until
its goal is verified. Formulas inside commands use [NFL syntax](NFL_syntax.md).
The target and assumptions come from the selected benchmark gap; named
theorems must match the [bundled library](../ProofGap_nfl/thm/all_lib_idx.md).

## Quick start

Save a UTF-8 text file containing the commands themselves, one command per
line. Optional prefixes such as `1.` and `2.` label steps; `#` starts a
comment. Markdown fences in this guide display examples and are not part of
the proof file. A local `assert ... by proof` block spans multiple lines.

For [exercise 2, gap 1](../ProofGap_nfl/exercise_2/gap_1/gap.txt), the following
script introduces the quantified variable and premise, extracts the equality,
and simplifies the goal:

```dsl
1. get_forall (GOAL: {forall (n), n ∈ NonNegIntegerSet ∧ n = 1 ⇒ 1 = frac(n * (n + 1) * (2 * n + 1), 6)}) (n := {n1})
2. get_condition (hypothesis 1: {n1 ∈ NonNegIntegerSet ∧ n1 = 1}) in (GOAL: {n1 ∈ NonNegIntegerSet ∧ n1 = 1 ⇒ 1 = frac(n1 * (n1 + 1) * (2 * n1 + 1), 6)})
3. destruct_and (hypothesis 1: {n1 ∈ NonNegIntegerSet ∧ n1 = 1}) as (hypothesis 2: {n1 ∈ NonNegIntegerSet}) (hypothesis 3: {n1 = 1})
4. rewrite (left_to_right, equation) (hypothesis 3: {n1 = 1}); from (GOAL: {1 = frac(n1 * (n1 + 1) * (2 * n1 + 1), 6)}) to (GOAL: {1 = frac(1 * (1 + 1) * (2 * 1 + 1), 6)})
5. autosolve all_hypothesis
```

Run from the repository root:

```sh
python3 ProofGap_nfl/check.py \
  ProofGap_nfl/exercise_2/gap_1/gap.txt \
  ProofGap_nfl/exercise_2/gap_1/dsl.txt
```

Replace the last path with your candidate script to check your own proof.
Acceptance requires `PASS`, a verified and finished proof, zero admits, and
zero remaining split gaps. Parsing successfully or making progress is not
sufficient. See the [verifier guide](../ProofGap_nfl/README.md) for platform
requirements, timeouts, configuration, and result logs. Packaged platform
binaries differ; command support and behavior depend on the selected build.

## Writing commands

- Hypothesis numbers identify the current proof state. Use the next available
  index when a command adds a new hypothesis, unless it explicitly permits
  updating an existing one.

- The formula in a descriptor must match the referenced hypothesis or goal.
  `from` and `to` describe the change to check; they do not grant permission
  to replace a formula arbitrarily.

- Use `⇒` or `=>` for implication, not `→` or `->`.
- `get_forall` and `get_exists` introduce fresh names; `get_prop` specializes
  a universal premise, and `exists` supplies a witness for an existential goal.

- Solver calls and `obvious` conditions still require verification.
  A failed command is not an accepted proof step.

- Examples below may show a single step in an assumed proof state. A complete
  submission must start from its actual gap and finish the proof.

## Proof-gap state
A Proof Gap is a structure consisting of known premises and a goal to be proved. Example format:
```text
ASSUM:
hypothesis 1. A ⊆ B
hypothesis 2. X ∈ PowerSet(A)
hypothesis 3. X ⊆ A

GOAL:
X ⊆ B
```

`ASSUM:` contains the premises of the proof problem, including `hypothesis`:

1. `hypothesis`: A premise in the problem; the number indicates its index.

`GOAL:` contains the conclusion to be proved.

Note: The symbol `<==>` is equivalent to `⇔`, and `=>` is equivalent to `⇒`.

## Command reference

### Commands
The DSL (domain-specific language) introduced below is a series of proof commands.
Types include:

1. `autoreplace`
2. `not_normalize`
3. `autosolve`
4. `get_prop`
5. `exists`
6. `destruct_and`
7. `rewrite`
8. `rewrite_in limit`
9. `rewrite_in sum`
10. `rewrite_in setdesc`
11. `apply`
12. `use_condition`
13. `get_exists`
14. `get_forall`
15. `get_condition`
16. `assert`
17. `case_analysis`
18. `or_intro`

The examples use `dsl` code blocks for display. Use `# ...` for comments in a proof file.

### DSL Command Usage

#### `autoreplace`

**Semantics**: Transform a specified `hypothesis` or `GOAL` by replacing a term.

**Usage**:
```dsl
    # 1. Invoke all hypotheses or no hypothesis; transform a specified hypothesis.
    autoreplace <scope>; from <target_term> to <replacement_term>; from (hypothesis <old_idx>: {<old_desc>}) to (hypothesis <new_idx>: {<new_desc>})

    # 2. Declare required hypotheses; transform a specified hypothesis.
    autoreplace (hypothesis <idx>: {<desc>}) ... ; from <target_term> to <replacement_term>; from (hypothesis <old_idx>: {<old_desc>}) to (hypothesis <new_idx>: {<new_desc>})

    # 3. Invoke all hypotheses or no hypothesis; transform the GOAL.
    autoreplace <scope>; from <target_term> to <replacement_term>; from (GOAL: {<old_desc>}) to (GOAL: {<new_desc>})
```

**Parameters**:

- `<scope>`: `all_hypothesis` or `no_hypothesis`.
- `<target_term>`: The specific term/sub-expression to find.
- `<replacement_term>`: The new term to replace with.

`autoreplace` can replace terms, with actions including but not limited to:

1. Differentiation
2. Indefinite integration
3. Polynomial merging and calculation
4. Definitional root-to-rational-power conversion
5. Local `not_normalize`: if `<target_term>` and `<replacement_term>` become alpha-equivalent after fully unfolding `not`, the local replacement is accepted

Examples:
```dsl
    # Suppose hypothesis 1 is `(x ^ 2)' = a`. We want to differentiate `x ^ 2`. We don't need any premises. If there are currently 3 hypotheses, the new index should be 4:
    autoreplace no_hypothesis; from ((x ^ 2)') to (2 * x); from (hypothesis 1: {(x ^ 2)' = a}) to (hypothesis 4: {2 * x = a})
    # This results in new hypothesis 4: 2 * x = a

    # Suppose the GOAL is `(e ^ x)' = a`. To differentiate `e ^ x`, no premises are needed:
    autoreplace no_hypothesis; from ((e ^ x)') to (e ^ x); from (GOAL: {(e ^ x)' = a}) to (GOAL: {e ^ x = a})
    # This results in new GOAL: e ^ x = a

    # Suppose hypothesis 1 is `X ⊆ A` and hypothesis 2 is `A ⊆ B`. To get `X ⊆ B`, we need both hypotheses. If there are 6 hypotheses, the new index should be 7:
    autoreplace (hypothesis 1: {X ⊆ A}) (hypothesis 2: {A ⊆ B}); from (A) to (B); from (hypothesis 1: {X ⊆ A}) to (hypothesis 7: {X ⊆ B})
    # This results in new hypothesis 7: X ⊆ B

    # Local not_normalize: these two local propositions have the same fully unfolded-not normal form, so the local sub-expression can be replaced:
    autoreplace no_hypothesis; from (¬ (a > 0) \/ ¬ (b < 0)) to (¬ ((a > 0) /\ (b < 0))); from (GOAL: {(¬ (a > 0) \/ ¬ (b < 0)) \/ (c = c)}) to (GOAL: {¬ ((a > 0) /\ (b < 0)) \/ (c = c)})
```

#### `not_normalize`

**Semantics**: Check that two `GOAL` forms are equivalent under negation-normalization rules, then replace the current `GOAL` with the user-written target form.

**Usage**:
```dsl
    not_normalize from (GOAL: {<old_goal>}) to (GOAL: {<new_goal>})
```

Execution rules:

- `from` must be alpha-equivalent to the current proof gap `GOAL`.
- The system fully not-unfolds both `<old_goal>` and `<new_goal>`, then checks that the normalized results are alpha-equivalent.
- `<new_goal>` must actually change the current `GOAL`; alpha-equivalent no-op transformations are rejected.
- If the check succeeds, the current `GOAL` is replaced by the user-written `<new_goal>`.
- This command performs only a local structural transformation check. It does not call `autosolve` and does not call LRA.
- The current version only supports `GOAL`-to-`GOAL` transformations. It does not modify hypotheses directly.

The rules include:

- Double negation: `¬¬P <=> P`
- Negation as implication to false: `P => False <=> ¬P`
- De Morgan: `¬(P /\ Q) <=> ¬P \/ ¬Q`, `¬(P \/ Q) <=> ¬P /\ ¬Q`
- Negated implication: `¬(P => Q) <=> P /\ ¬Q`
- Negated biconditional: `¬(P <==> Q) <=> (P /\ ¬Q) \/ (¬P /\ Q)`
- Quantifier negation: `¬ forall (x), P <=> exists (x), ¬P`, `¬ exists (x), P <=> forall (x), ¬P`
- Atomic predicate negation, for example `¬(a > b) <=> a <= b`, `¬(a = b) <=> a != b`, `¬(a ∈ e) <=> a ∉ e`

Example 1: unfold one visible negation layer.
```dsl
not_normalize from (GOAL: {¬ ((a > 0) /\ (b < 0))}) to (GOAL: {¬ (a > 0) \/ ¬ (b < 0)})
```

Example 2: both directions are allowed. This folds an unfolded goal back into the user-specified form; the check only requires both sides to have the same full not-unfold normal form.
```dsl
not_normalize from (GOAL: {¬ (a > 0) \/ ¬ (b < 0)}) to (GOAL: {¬ ((a > 0) /\ (b < 0))})
```

Example 3: with nested negations, the user may choose an intermediate form. The checker fully normalizes both sides, but the proof gap receives exactly the user-written `<new_goal>`.
```dsl
not_normalize from (GOAL: {¬ (((a > 0) /\ (b < 0)) /\ (c = 0))}) to (GOAL: {¬ ((a > 0) /\ (b < 0)) \/ ¬ (c = 0)})
```

#### `autosolve`

**Semantics**: Select hypotheses that you believe are "obvious enough" to derive the GOAL.

**Usage**:
```dsl
    # 1. Invoke all hypotheses
    autosolve all_hypothesis

    # 2. Declare required hypotheses
    autosolve (hypothesis <index>: {<description>}) (hypothesis <index>: {<description>}) ...
```

`autosolve` can handle cases including but not limited to:

1. LRA (Linear Real Arithmetic), calling a linear solver
2. Polynomial solver to check equality
3. Basic set theory problems
4. Basic propositional logic operations

Examples:
```dsl
    # Suppose GOAL is `Q`, hypothesis 1 is `P=>Q`, and hypothesis 2 is `P`. Using both hypotheses can prove the GOAL.
    autosolve (hypothesis 1: {P=>Q}) (hypothesis 2: {P})
    # Successfully proved

    # Suppose hypothesis 1 is `a > b` and hypothesis 2 is `c < b`. GOAL is `a > c`. To prove the GOAL, use hypothesis 1 and 2:
    autosolve (hypothesis 1: {a > b}) (hypothesis 2: {c < b})
    # Successfully proved

    # Suppose the GOAL is `1 + x ^ 2 + x = x + 1 + x ^ 2`:
    autosolve all_hypothesis
    # Successfully proved
```
Examples:

pg1:
```
ASSUM:
hypothesis 1. A ⊆ B
hypothesis 2. X ⊆ A

GOAL:
X ⊆ B
```

pg2:
```
ASSUM:
hypothesis 1. a > c
hypothesis 2. b = x
hypothesis 3. x > a

GOAL:
c <= b
```

pg3:
```
ASSUM:
hypothesis 1. a > c
hypothesis 2. b = x
hypothesis 3. x > a

GOAL:
2 + 3 = 5
```

Available commands:
pg1:
autosolve (hypothesis 1: {A ⊆ B}) (hypothesis 2: {X ⊆ A})

pg2:
autosolve (hypothesis 1: {a > c}) (hypothesis 2: {b = x}) (hypothesis 3: {x > a})

pg3:
autosolve all_hypothesis


If a solver cannot be used, consider the following DSL commands:

#### `get_prop`
**Semantics**: Instantiate a premise, introduce a new theorem, or instantiate a theorem as a new premise.
Note: The number of consecutive universal quantifiers must not be less than the number of terms following `get_prop` in the DSL.

**Usage**:
```dsl
    get_prop (<source>) (<bound_var> := {<value>}) ... as (hypothesis <new_idx>: {<new_desc>})
```
Where `<source>` is either:

- `hypothesis <idx>: {<desc>}`
- `theorem '<name>': {<desc>}`

**Example**:
```dsl
    # Instantiate 'y' in hypothesis 1 as 'z' and add it as new hypothesis 2.
    get_prop (hypothesis 1: {forall (y), (y > x => y > 0)}) (y := {z}) as (hypothesis 2: {z > x => z > 0})
```
`<bound_var>` is parsed as a term and matched structurally against the outer universal-quantifier binder, so subscripted binders are supported as well. For example:

```dsl
    get_prop (hypothesis 1: {forall (x_{0}), x_{0} > 1}) (x_{0} := {a}) as (hypothesis 2: {a > 1})
```

The outer formula braces must still be balanced; malformed input such as `x_{0}}` fails during DSL parsing.

If the instantiated variable is used as a function and the replacement is an anonymous function, `get_prop` performs beta reduction after instantiation. For example:

```dsl
    get_prop (hypothesis 1: {forall (f) (a), f(a) = f(a)}) (f := {fun x . (x + 1)}) (a := {c}) as (hypothesis 2: {c + 1 = c + 1})
```

Here `f(a)` first becomes `(fun x . (x + 1))(c)`, then reduces to `c + 1`. Prefer parenthesizing the anonymous-function body, such as `fun x . (x + 1)`, to avoid ambiguity around the function body boundary.

`get_prop` also supports multi-argument anonymous functions. Parameters are matched to function-application arguments in written order. For example:

```dsl
    get_prop (hypothesis 1: {forall (f) (a) (b), f(a, b) = f(a, b)}) (f := {fun x, y . (x + y)}) (a := {c}) (b := {d}) as (hypothesis 2: {c + d = c + d})
```

Here `f(a, b)` first becomes `(fun x, y . (x + y))(c, d)`, then reduces to `c + d`. If the anonymous-function body contains binders such as `sum`, `lim`, `forall`, or another lambda, `get_prop` performs capture-avoiding beta reduction and alpha-renames inner binders when needed.

After instantiation, beta-normalization also merges pointwise arithmetic between anonymous functions of the same arity. The supported operators are `+`, `-`, `*`, and `/`. For example:

```dsl
    get_prop (hypothesis 1: {forall (f) (g), P(f + g) = 0}) (f := {fun x . sin(x)}) (g := {fun y . cos(y)}) as (hypothesis 2: {P(fun x . (sin(x) + cos(x))) = 0})
```

Here `(fun x . sin(x)) + (fun y . cos(y))` normalizes to a function alpha-equivalent to `fun x . (sin(x) + cos(x))`. The merge is performed only when both lambdas have the same arity; adding a unary lambda to a binary lambda keeps the original `Plus(lambda, lambda)` shape.

Additionally, we define:
If you want to use a theorem:
```text
    Thm 49. (EquivalenceClassSetBuilder)
    forall (R) (a), EquivClass(a, R) = {b | (a, b) ∈ R}
```
In `get_prop`, use:
```dsl
    # Instantiate 'A' and 'B' in hypothesis 2 as 'y' and 'x', adding as new hypothesis 4.
    get_prop (hypothesis 2: {forall (A), (forall (B), (P(A, x) => Q(B, y)))}) (A := {y}) (B := {x}) as (hypothesis 4: {P(y, x) => Q(x, y)})
```
```dsl
    # If there are two hypotheses, name the new one hypothesis 3. The theorem name should be 'Thm 49. (EquivalenceClassSetBuilder)'.
    get_prop (theorem 'Thm 49. (EquivalenceClassSetBuilder)': {forall (R) (a), EquivClass(a, R) = {b | (a, b) ∈ R}}) as (hypothesis 3: {forall (R) (a), EquivClass(a, R) = {b | (a, b) ∈ R}})
```
```dsl
    # If there are three hypotheses, name the new one hypothesis 4.
    get_prop (theorem 'Thm 49. (EquivalenceClassSetBuilder)': {forall (R) (a), EquivClass(a, R) = {b | (a, b) ∈ R}}) (R := {R0}) (a := {a0}) as (hypothesis 4: {EquivClass(a0, R0) = {b | (a0, b) ∈ R0}})
```

Example:
Suppose current proof gap:

```text
ASSUM:
hypothesis 1. forall (x), (x > 3 => x > 2)
hypothesis 2. a > 3
GOAL:
a > 2
```

Execute: `get_prop (hypothesis 1: {forall (x), (x > 3 => x > 2)}) (x := {a}) as (hypothesis 3: {a > 3 => a > 2})`.
Since hypothesis 1 is `forall (x), (x > 3 => x > 2)`, instantiating x as 'a' yields new premise `hypothesis 3. a > 3 => a > 2`.

Resulting proof gap:

```text
ASSUM:
hypothesis 1. forall (x), (x > 3 => x > 2)
hypothesis 2. a > 3
hypothesis 3. a > 3 => a > 2
GOAL:
a > 2
```

#### `exists`
**Semantics**: Instantiate existential quantifiers in the GOAL with t1, t2, .. tn. The `exists` quantifier must be outermost in the GOAL.
Note: The GOAL must contain `exists`, and the number of existential quantifiers must not be less than the number of terms following `exists` in the DSL.

**Usage**:
```dsl
    exists (<bound_var> := {<value>}) ...
```

Example:
```dsl
    # Suppose GOAL is `exists (x1), (exists (x2), (x1 > x2))`. After instantiation: `exists (x2), (A > x2)`.
    exists (x1 := {A})
```
```dsl
    # Suppose GOAL is `exists (x1), (exists (x2), (x1 > x2))`. After instantiation: `A > B`.
    exists (x1 := {A}) (x2 := {B})
```

Example:
Suppose current proof gap:


```text
ASSUM:
hypothesis 1. x ∈ GeneralUnion(B)
hypothesis 2. x ∈ qvar_0 /\ qvar_0 ∈ B
GOAL:
exists (X), (X ∈ B /\ x ∈ X)
```

Execute: `exists (X := {qvar_0})`

Resulting proof gap:

```text
ASSUM:
hypothesis 1. x ∈ GeneralUnion(B)
hypothesis 2. x ∈ qvar_0 /\ qvar_0 ∈ B
GOAL:
qvar_0 ∈ B /\ x ∈ qvar_0
```

#### `destruct_and`
**Semantics**: Split a conjunctive hypothesis into several new hypotheses named explicitly in the `as` clause.

**Usage**:
```dsl
    destruct_and (hypothesis <source_idx>: {<and_formula>}) as (hypothesis <new_idx_1>: {<part_1>}) ... (hypothesis <new_idx_n>: {<part_n>})
```

**Parameters**:

- The source must be a `hypothesis`, not the `GOAL`.
- The source hypothesis must be a conjunction.
- Each target in the `as` clause must be a concrete hypothesis descriptor.

**Behavior**:

- The split is recursive: nested conjunctions are flattened before matching targets.
- Therefore `((A /\ B) /\ C)` is treated as three parts: `A`, `B`, `C`.
- The number of hypotheses listed after `as` must exactly match the number of flattened conjuncts.
- The generated hypotheses are added to the proof gap as ordinary assumptions.

Examples:
```dsl
    destruct_and (hypothesis 1: {(A > 0) /\ (B > 0)}) as (hypothesis 2: {A > 0}) (hypothesis 3: {B > 0})
```
```dsl
    destruct_and (hypothesis 1: {((a > 0) /\ (b > 0)) /\ (c > 0)}) as (hypothesis 2: {a > 0}) (hypothesis 3: {b > 0}) (hypothesis 4: {c > 0})
```

Note:

- `destruct_and` currently performs full recursive flattening only.
- It does not preserve a shallow left/right block split such as `((A /\ B) /\ C)` -> `(A /\ B)` and `C`.

#### `rewrite`
**Semantics**: Substitute an equation or IFF `hypothesis` into another `hypothesis` or the `GOAL`.
The system automatically verifies if the left side (or right side if `right_to_left`) of the equation is syntactically equivalent to the term being replaced.

**Usage**:
```dsl
    rewrite (<direction>, <type>) (hypothesis <idx>: {<desc>}); from (<target>) to (<result>)
```
**Parameters**:

- `<direction>`: `left_to_right` or `right_to_left`
- `<type>`: `equation` or `iff`
- `<target>`/`<result>`: `(hypothesis <idx>: {<desc>})` or `(GOAL: {<desc>})`

Examples:
```dsl
    # hypothesis 1 is `x = y` (equation), GOAL is `f(x) = f(y)`. To substitute 'x' in f(x), use left-to-right rewrite on hypothesis 1. GOAL becomes `f(y) = f(y)`.
    # 'x' is the left side; the system checks if 'x' matches 'x' in the goal (it does).
    rewrite (left_to_right, equation) (hypothesis 1: {x = y}); from (GOAL: {f(x) = f(y)}) to (GOAL: {f(y) = f(y)})
```
```dsl
    # hypothesis 2 is `y = x` (equation), GOAL is `f(x) = f(y)`. To substitute 'y' in f(y), use left-to-right rewrite on hypothesis 2. GOAL becomes `f(x) = f(x)`.
    # 'y' is the left side; the system checks if 'y' matches 'y' in the goal (it does).
    rewrite (left_to_right, equation) (hypothesis 2: {y = x}); from (GOAL: {f(x) = f(y)}) to (GOAL: {f(x) = f(x)})
```
```dsl
    # hypothesis 3 is `P <==> Q` (IFF), GOAL is `P => R`. To substitute 'P', use left-to-right rewrite. GOAL becomes `Q => R`.
    rewrite (left_to_right, iff) (hypothesis 3: {P <==> Q}); from (GOAL: {P => R}) to (GOAL: {Q => R})
```
```dsl
    # hypothesis 3 is `P <==> Q` (IFF), hypothesis 4 is `Q => R`. To substitute 'Q' in hypothesis 4, use right-to-left rewrite. hypothesis 4 becomes `P => R`.
    rewrite (right_to_left, iff) (hypothesis 3: {P <==> Q}); from (hypothesis 4: {Q => R}) to (hypothesis 4: {P => R})
```
```dsl
    # hypothesis 5 is `InductiveSet(u) <==> (∅ ∈ u /\ (forall n, n ∈ u => n ∪ {n} ∈ u))`. hypothesis 6 is `InductiveSet(u) => u ∈ v`. To substitute `InductiveSet(u)`, use left-to-right rewrite. hypothesis 6 becomes `∅ ∈ u /\ (forall n, n ∈ u => n ∪ {n} ∈ u) => u ∈ v`.
    rewrite (left_to_right, iff) (hypothesis 5: {InductiveSet(u) <==> (∅ ∈ u /\ (forall n, n ∈ u => n ∪ {n} ∈ u))}); from (hypothesis 6:{InductiveSet(u) => u ∈ v}) to (hypothesis 6:{(∅ ∈ u /\ (forall n, n ∈ u => n ∪ {n} ∈ u)) => u ∈ v})
```

Example:
Suppose current proof gap:

```text
ASSUM:
hypothesis 1. sin(2*a) = 2*sin(a)*cos(a)
GOAL:
sin(2*a) + sin(a)^2 + cos(a)^2 = (sin(a)+cos(a))^2
```

Execute: `rewrite (left_to_right, equation) (hypothesis 1: {sin(2*a) = 2*sin(a)*cos(a)}); from (GOAL: {sin(2*a) + sin(a)^2 + cos(a)^2 = (sin(a)+cos(a))^2}) to (GOAL: {2*sin(a)*cos(a) + sin(a)^2 + cos(a)^2 = (sin(a)+cos(a))^2})`
The expression `sin(2 * a)` in the goal matches the left side of the rewrite rule. If another form needs algebraic normalization, perform that as a separate checked step.

Binder protection: before matching a subterm, `rewrite` enriches the target term and both sides of the rewrite rule with implicit binder metadata. If the free variables of the replacement collide with the current binder, rewrite will not cross that binder. For example, `x = y` cannot rewrite `lim_{ x -> +infty } (f(x))` into `lim_{ x -> +infty } (f(y))`; however, `a = b` can rewrite `lim_{ x -> +infty } (f(a) + x)` into `lim_{ x -> +infty } (f(b) + x)`.

The constructs currently treated as implicit binders include (integrals, `ValDeri`, and `SetDesc` are intentionally out of scope for now):

- Limit family: `lim`, left/right limits, `limsup`, `liminf`, and their left/right variants.
- Big-operator family: `sum`, `prod`, `union`, `inter`, and their upper-bound variants.
- Tending/asymptotic family: `TendsTo`, `LeftTendsTo`, `RightTendsTo`, `AsymEquiv`, `LeftAsymEquiv`, `RightAsymEquiv`.
- O/o-notation family: `BigO`, `LeftBigO`, `RightBigO`, `LittleO`, `LeftLittleO`, `RightLittleO`. This family is currently collected in equality contexts.

Resulting proof gap:

```text
ASSUM:
hypothesis 1. sin(2*a) = 2*sin(a)*cos(a)
GOAL:
2*sin(a)*cos(a) + sin(a)^2 + cos(a)^2 = (sin(a)+cos(a))^2
```

Note: Rewriting a hypothesis or theorem with an outermost `exists` or `forall` binding is invalid. Example:
```dsl
    # INVALID.
    rewrite (left_to_right, iff) (hypothesis 7: {forall (S), (InductiveSet(S) <==> (∅ ∈ S /\ (forall n, n ∈ S => n ∪ {n} ∈ S)))}) from (GOAL: {InductiveSet(S)}) to (GOAL: {(∅ ∈ S /\ (forall n, n ∈ S => n ∪ {n} ∈ S))})
```

#### Shared matching rules for `rewrite_in`

`rewrite_in limit`, `sum`, and `setdesc` use the same conservative policy to decide which branches may change:

- The target written in `from` must agree with the current GOAL or hypothesis under metadata-aware alpha-equivalence semantics.
- After rule instantiation, the rewrite endpoints must alpha-match the actual changed location. Every unchanged sibling visited recursively, as well as binders, limit points, sum bounds, and `SetDesc` local-condition identities, must remain alpha-equivalent.
- Composite rule-instance inference records binders introduced inside the rule endpoint. A candidate that depends on one of those local binders is rejected. For a valid candidate, binders in the rule that conflict with candidate free variables are alpha-renamed before capture-avoiding substitution. Thus `forall t, sum_i(t)=h(t)` cannot extract `t:=x+i` from `sum_i(x+i)`, while the corresponding form with `i` genuinely free and the summation binder renamed is safe.
- Algebraic equivalence cannot smuggle extra changes into the same rewrite. For example, `f(x) + frac(a,a) -> g(x) + 1`, changing `lim_{x -> frac(a,a)}` to `lim_{x -> 1}`, or changing `sum_{k = frac(a,a)}^n` to `sum_{k = 1}^n` is rejected; `frac(a,a)` may itself be undefined when `a = 0`.
- Consequently, a rule endpoint `t + 0` does not directly match an actual subterm `t`. Use an explicit additional rewrite or normalization step when that algebraic conversion is intended.

Polynomial equivalence is retained only for normalized eventual conditions in `rewrite_in limit`. The caller first restricts both sides to a safe grammar: variables; integer, decimal, `e`, and `π` constants; unary negation; `+`, `-`, and `*`; and positive-integer powers. Fractions/division, roots, logarithms, and zero or negative powers are excluded. Only then may `poly_rat_eqb` be used. This exception proves an eventual side condition; it is never used to match rewrite endpoints or accept changed siblings.

#### `rewrite_in limit`

**Semantics**: Rewrite inside the body of a limit using a universally quantified equation hypothesis. Unlike ordinary `rewrite`, which protects implicit binders, `rewrite_in limit` explicitly enters the binder scope of `lim` and checks that the rule conditions are eventually true in that limit context.

**Usage**:
```dsl
    rewrite_in limit (<direction>, equation) (hypothesis <idx>: {<forall_eq_rule>}); from (<target>) to (<result>)
```

Current restrictions:

- The rewrite rule must be a hypothesis whose outermost form has exactly one `forall` variable.
- The rule conclusion must be an equation. `iff` parses, but execution reports that it is currently unsupported.
- `from` and `to` use the same target/result style as ordinary `rewrite`; a `GOAL` rewrite must produce `GOAL`, while a hypothesis rewrite may overwrite that hypothesis or append the next hypothesis.
- Simple real-variable limits are supported: `lim_{x -> a}`, `lim_{x -> +infty}`, `lim_{x -> -infty}`, `lim_{x -> a^+}`, and `lim_{x -> a^-}`. Positive-infinity sequence limits `seqlim_{k -> +infty}` are also supported.
- Non-variable limit binders remain out of scope. One-sided infinite forms such as `lim_{x -> +infty^+}` and `lim_{x -> -infty^-}` are also rejected for now, as are finite-point and negative-infinity `seqlim` forms.
- If rule free variables collide with the active limit binder, `rewrite_in limit` alpha-renames the limit binder before matching. When the replacement itself contains such a free variable, the written `to` term must use a different limit binder name so that the free variable is not captured.
- If the rewrite position is under an explicit `forall` / lambda binder and that binder conflicts with a rule free variable, `rewrite_in limit` internally alpha-renames the explicit binder. The written `to` term must still avoid recapturing that free variable; for example, write `forall (u), ... x ...`, not `forall (x), ... x ...`.
- When structural/alpha endpoint matching infers a composite rule instance, such as `t := 1+x` from `f(1+x) -> g(1+x)`, the eventual side condition uses that actual instance `C(1+x)` rather than falling back to the limit binder `C(x)`.
- The command only rewrites in the selected limit body. It will not pass through other implicit binders such as `sum`, `prod`, indexed union/intersection, `limsup`/`liminf`, tends-to/asymptotic predicates, integrals, O/o notation, `SetDesc`, or `ValDeri`.

Side-condition meaning:

- If the rule is `forall (x), C(x) => f(x) = g(x)`, rewriting under `lim_{x -> +infty}` requires `C(x)` to hold for all sufficiently large `x`.
- Under `lim_{x -> -infty}`, `C(x)` must hold for all sufficiently small `x`.
- Under `lim_{x -> a}`, `C(x)` must hold on a punctured neighborhood `0 < |x-a| < δ`.
- Under `lim_{x -> a^+}` or `lim_{x -> a^-}`, `C(x)` must hold on the corresponding right or left neighborhood.
- Under `seqlim_{k -> +infty}`, `C(k)` must hold for all sufficiently large sequence indices `k`.

The automatic side-condition checker is intentionally conservative:

- It handles simple comparisons between the bound variable and finite constants/parameters, such as `x > 0`, `x >= 1`, `x < c`, `x <= 2`, and `x != c`. At finite limit points, symbolic point/parameter relations may also be discharged if the pure sign solver can prove them from the current assumptions.
- At a finite approach point, safe polynomial conditions may first substitute that point and then be solved. For example, at `x -> 0`, `1+x != 0` is eventually true.
- For a finite punctured neighborhood, safe normalization uses `binder-point` as the centered basis. In addition to `1+x != 1` at `x -> 0`, this handles `x+0 != 1` at `x -> 1`. Direction is preserved: `x+0 > 1` holds eventually at `x -> 1^+`, but not at the two-sided limit `x -> 1`. This path remains narrow: it requires the normalized difference to be `±(binder-point)` and the approach point to be in the safe polynomial grammar. Infinite limits continue to use `±binder`.
- Simple sign conditions that do not mention the bound variable are checked with `SgnPureSolver`; this path does not call LRA.
- Before checking side conditions, active binders are alpha-renamed to fresh names that do not collide with free variables in the current proof context. This keeps unrelated parameter assumptions available while preventing shadowed global assumptions from being applied to bound variables.
- `x ∈ Real`, `x ∈ RealPlus`, `x ∈ NonNegRealSet`, `x ∈ NegRealSet`, and `x ∈ NonPosRealSet` are handled using real-limit neighborhood semantics.
- For ordinary `lim`, discrete set conditions such as `x ∈ NatPlus` or `x ∈ Integer` are still not discharged automatically. For `seqlim_{k -> +infty}`, numeric universe conditions such as `k ∈ Integer` and `k ∈ Real` are discharged directly; positive/nonnegative/negative/nonpositive numeric sets are checked with sufficiently-large semantics.
- Boundary comparisons with explicit `+∞` / `-∞` are handled conservatively; for example, `x > +∞` and `x < -∞` are not considered eventually true. A free parameter such as `c` is treated as a fixed finite parameter for `x -> +∞/-∞`.

Example:
```dsl
rewrite_in limit (left_to_right, equation) (hypothesis 1: {forall (x), (x > 0 => f(x) = g(x))}); from (GOAL: {lim_{ x -> +infty } (f(x)) = 0}) to (GOAL: {lim_{ x -> +infty } (g(x)) = 0})
```

Finite right-limit example:
```dsl
rewrite_in limit (left_to_right, equation) (hypothesis 1: {forall (x), (x ∈ RealPlus => f(x) = g(x))}); from (GOAL: {lim_{ x -> 0^+ } (f(x)) = 0}) to (GOAL: {lim_{ x -> 0^+ } (g(x)) = 0})
```

Sequence-limit example:
```dsl
rewrite_in limit (left_to_right, equation) (hypothesis 2: {forall (n), (n ∈ Integer => a(n) = 0)}); from (GOAL: {seqlim_{ k -> +infty } (a(k)) = 0}) to (GOAL: {seqlim_{ k -> +infty } (0) = 0})
```

#### `rewrite_in sum`

**Semantics**: Rewrite inside the summand of a sum using a universally quantified equation hypothesis. As with `rewrite_in limit`, the written `from` / `to` terms identify which sum layer is being rewritten. Unlike limits, sum side conditions must hold on the whole summation range, not merely eventually.

**Usage**:
```dsl
    rewrite_in sum (<direction>, equation) (hypothesis <idx>: {<forall_eq_rule>}); from (<target>) to (<result>)
```

Current restrictions:

- The rewrite rule must be a hypothesis whose outermost form has exactly one `forall` variable.
- The rule conclusion must be an equation. `iff` parses, but execution reports that it is currently unsupported.
- `from` and `to` use the same target/result style as ordinary `rewrite`; a `GOAL` rewrite must produce `GOAL`, while a hypothesis rewrite may overwrite that hypothesis or append the next hypothesis.
- Only interval sums `sum_{ k = L }^{ U } body(k)` are supported. The index must be a simple binder, `L` and `U` may be general terms, and `U` may be `+∞`.
- Constraint sums such as `sum_{ k + l = n } body(k,l)` and sums without an explicit upper bound are not supported yet.
- If rule free variables collide with the active sum binder, `rewrite_in sum` alpha-renames the sum binder before matching. When the replacement itself contains such a free variable, the written `to` term must use a different sum binder name so that the free variable is not captured.
- If the rewrite position is under an explicit `forall` / lambda binder and that binder conflicts with a rule free variable, `rewrite_in sum` internally alpha-renames the explicit binder. The written `to` term must still avoid recapturing that free variable; for example, write `forall (u), ... x ...`, not `forall (x), ... x ...`.
- The command only rewrites in the selected sum body. It will not pass through other implicit binders such as inner `limit`, `prod`, indexed union/intersection, `limsup`/`liminf`, tends-to/asymptotic predicates, integrals, O/o notation, `SetDesc`, or `ValDeri`. Inner sums are selected recursively from the `from` / `to` difference, and one command cannot rewrite both an outer and inner sum.
- Proof gaps, DSL braced terms, and theorem-library terms now all go through the same semantic parse step before implicit binder metadata is attached.
- For bounded big operators such as `sum_{ k = L }^{ U }`, `prod_{ k = L }^{ U }`, and bounded indexed union/intersection, a binder written as `i` is normalized into a real binder variable instead of being left as the imaginary-unit constant `I`.
- As a result, a bare `i` inside `sum_{ i = L }^{ U } (...)` is interpreted as the active sum index. If you need a free `i` inside the body, rename the binder in the written term, for example `sum_{ u = L }^{ U } (i)` rather than `sum_{ i = L }^{ U } (i)`.

Side-condition meaning:

- If the rule is `forall (k), C(k) => f(k) = g(k)`, rewriting under `sum_{ k = L }^{ U } f(k)` requires `C(k)` for every summation index with `L <= k <= U`, or `k >= L` when `U = +∞`.
- This differs from `limit`: initial terms cannot be ignored. For example, `forall (k), k > 0 => f(k)=g(k)` can rewrite `sum_{ k = 1 }^{ +∞ } f(k)`, but not `sum_{ k = 0 }^{ +∞ } f(k)`.

The automatic side-condition checker is conservative and does not call LRA:

| Condition | Check |
| --- | --- |
| `k >= c` | prove lower bound `L >= c` |
| `k > c` | prove lower bound `L > c` |
| `k <= c` | require finite upper bound and prove `U <= c` |
| `k < c` | require finite upper bound and prove `U < c` |
| `k != c` | prove `L > c`, or prove `U < c` for a finite upper bound |
| `k = c` | require a singleton range and prove `L = c` and `U = c` |
| `k ∈ Integer/Rational/Real/Complex` | accepted for a summation index |
| `k ∈ Nat/NonNeg*` | prove `L >= 0` |
| `k ∈ NatPlus/Pos*` | prove `L > 0` |
| `k ∈ Neg*` | require finite upper bound and prove `U < 0` |
| `k ∈ NonPos*` | require finite upper bound and prove `U <= 0` |
| `C1 /\ C2` | check both conditions |
| simple sign condition without the sum index | check with `SgnPureSolver`; this path does not call LRA |

Before checking side conditions, active binders are alpha-renamed to fresh names that do not collide with free variables in the current proof context. This keeps unrelated parameter assumptions available while preventing shadowed global assumptions from being applied to bound variables.

Unsupported conditions fail, for example `k + 1 > 0`, conditions needing contextual linear arithmetic, or conditions relying on monotonicity/positivity of uninterpreted functions.

Example:
```dsl
rewrite_in sum (left_to_right, equation) (hypothesis 1: {forall (k), (k >= 0 => f(k) = g(k))}); from (GOAL: {sum_{ k = 0}^{ n } (f(k)) = A}) to (GOAL: {sum_{ k = 0}^{ n } (g(k)) = A})
```

Infinite-series example:
```dsl
rewrite_in sum (left_to_right, equation) (hypothesis 1: {forall (k), (k > 0 => f(k) = g(k))}); from (GOAL: {sum_{ k = 1}^{ +infty } (f(k)) = A}) to (GOAL: {sum_{ k = 1}^{ +infty } (g(k)) = A})
```

#### `rewrite_in setdesc`

**Semantics**: Rewrite inside the body or conditions of a set description `SetDesc` / `{ x | ... }` using a universally quantified equation hypothesis. Ordinary `rewrite` does not provide local `SetDesc` binder mapping or side-condition semantics; `rewrite_in setdesc` explicitly enters the user-selected set-description scope and uses an explicit binder map to align the rule binder with the set binder.

**Usage**:
```dsl
    rewrite_in setdesc (<direction>, equation) (hypothesis <idx>: {<forall_eq_rule>}) (<rule_var> := {<set_var>}); from (<target>) to (<result>)
```

Current restrictions:

- The rewrite rule must be a hypothesis whose outermost form has exactly one `forall` variable.
- The rule conclusion must be an equation. `iff` parses, but execution reports that it is currently unsupported.
- Exactly one substitution-style binder map is required after the hypothesis and before `; from`, for example `(k := {x})`.
- The left side of the binder map must be the unique `forall` binder of the rule; the right side must be the unique binder of the current target `SetDesc`.
- Only canonical `SetDesc(body, TermList(...))` is supported, and the current `SetDesc` must have exactly one simple-variable binder.
- `from` and `to` use the same target/result style as ordinary `rewrite`; their difference selects the `SetDesc` layer to rewrite. One command may rewrite that layer's body or conditions.
- Before matching and side-condition checking, the active `SetDesc` binder is alpha-renamed to a fresh name that does not collide with proof-context free variables, rule free variables, or outer active binders. The binder map is still validated against the user-written original binder.
- The command does not cross other protected implicit binders. Nested `SetDesc` terms can be selected recursively through the `from` / `to` difference, but one command should still express one clear rewrite.

Side-condition meaning:

- If the rule is `forall (k), C(k) => f(k) = g(k)`, rewriting `f(x)` inside `{ x | P(x) }` requires `C(x)` to be proved in the local set-description context.
- When rewriting the `SetDesc` body, all original SetDesc conditions are available as local assumptions.
- When rewriting a `SetDesc` condition, only unchanged flat conditions are available. If a condition is `C1 /\ C2`, the checker splits the conjuncts; while rewriting `C2`, it may use unchanged `C1`, but it cannot use the very `C2` being rewritten.
- This prevents self-justifying unsound rewrites: `forall (k), k = 1 => k = 1` cannot rewrite `{ x | x = 1 }` into `{ x | 1 = 1 }`, because the only available side condition is exactly the condition being removed.
- Side conditions first pass if they are alpha-equivalent to an available local flat condition. Otherwise the checker builds a temporary context from global assumptions plus the available local conditions and currently tries `SgnPureSolver` and LRA through the existing solver adapters.
- Fresh alpha-renaming prevents global free variables from being mistaken for the set binder. For example, a global `x > 0` cannot prove the local bound `x > 0` for `{ x | f(x) > 1 }`; but with global assumptions `a > x` and `x > 0`, and local set condition `x > a`, the set binder is renamed fresh and the checker can prove the local side condition from `x_local > a > x_global > 0`.

Example: rewrite inside a condition, using another unchanged condition to prove the side condition.
```dsl
rewrite_in setdesc (left_to_right, equation) (hypothesis 1: {forall (k), (k > 0 => f(k) = g(k))}) (k := {x}); from (GOAL: {{ x | x > 0 ∧ f(x) > 1 } = A}) to (GOAL: {{ x | x > 0 ∧ g(x) > 1 } = A})
```

Example: rewrite inside the body.
```dsl
rewrite_in setdesc (left_to_right, equation) (hypothesis 1: {forall (k), f(k) = g(k)}) (k := {x}); from (GOAL: {{ f(x) | x > 0 } = A}) to (GOAL: {{ g(x) | x > 0 } = A})
```

#### `apply`
**Semantics**: Strengthen the GOAL or prove it directly.
**Requirement**: The premise must have the form `p1 => p2 => p3 => ... => pn`. The GOAL must have the form `pi => ... => pn`.
If the premise and GOAL have identical forms `p1 => p2 => ... => pn` (or are exactly the same), the goal is considered proved. `GOAL:` becomes `ALL GOALS HAVE BEEN PROVED.`.

**Usage**:
```dsl
    apply (hypothesis <index>: {<description>})
```

Examples:
```dsl
    # Suppose GOAL is `x > 0`. After this step, GOAL becomes `x > 1`.
    apply (hypothesis 1: {x > 1 => x > 0})
```
```dsl
    # Suppose GOAL is `x > 1 => x > 0`. After this step, GOAL becomes `ALL GOALS HAVE BEEN PROVED.`.
    apply (hypothesis 2: {x > 1 => x > 0})
```
```dsl
    # Suppose GOAL is `Q(x)`. After this step, GOAL becomes `x > 2 /\ P(x)`.
    apply (hypothesis 3: {x > 2 => P(x) => Q(x)})
```
```dsl
    # Suppose GOAL is `P(x) => Q(x)`. After this step, GOAL becomes `x > 2`.
    apply (hypothesis 4: {x > 2 => P(x) => Q(x)})
```
```dsl
    # Suppose GOAL is `R(y, z)`. After this step, GOAL becomes `ALL GOALS HAVE BEEN PROVED.`.
    apply (hypothesis 5: {R(y, z)})
```

Example:
Suppose current proof gap:

```text
ASSUM:
hypothesis 1. A ⊆ B
hypothesis 2. A ⊆ B => X ⊆ B
hypothesis 3. X ⊆ A
GOAL:
X ⊆ B
```

Execute: `apply (hypothesis 2: {A ⊆ B => X ⊆ B})`

Resulting proof gap:

```text
ASSUM:
hypothesis 1. A ⊆ B
hypothesis 2. A ⊆ B => X ⊆ B
hypothesis 3. X ⊆ A
GOAL:
A ⊆ B
```

Continue with: `apply (hypothesis 1: {A ⊆ B})`

Resulting proof gap:

```text
ASSUM:
hypothesis 1. A ⊆ B
hypothesis 2. A ⊆ B => X ⊆ B
hypothesis 3. X ⊆ A
GOAL:
ALL GOALS HAVE BEEN PROVED.
```

#### `use_condition`
**Semantics**: Simplify a hypothesis to obtain a new one.
**Requirement**: Use premises `p1, p2, p3...pi` (matching order) to simplify a hypothesis of form `p1 => p2 => p3 => ... => pn`. Some `pi` may be `obvious` rather than explicitly in `ASSUM`.

**Usage**:
```dsl
    use_condition (<condition_1>) (<condition_2>) ... in (hypothesis <idx>: {<desc>}) as (hypothesis <new_idx>: {<new_desc>})
```
Where each `<condition>` is either:

- `(hypothesis <idx>: {<desc>})`
- `(obvious: {<fact>})` - for premises you believe are evidently true.

Examples:
```dsl
    # Obtain new `hypothesis 3. x > 0`
    use_condition (hypothesis 1: {x > 1}) in (hypothesis 2: {x > 1 => x > 0}) as (hypothesis 3: {x > 0})
```
```dsl
    # Obtain new `hypothesis 6. Q => R`
    use_condition (hypothesis 4: {P}) in (hypothesis 5: {P => Q => R}) as (hypothesis 6: {Q => R})
```
```dsl
    # Obtain new `hypothesis 9. R`
    use_condition (hypothesis 7: {P}) (hypothesis 8: {Q}) in (hypothesis 5: {P => Q => R}) as (hypothesis 9: {R})
```
```dsl
    # Obtain new `hypothesis 9. R`. Since the second condition (1 + 1 = 2) is trivial, use `obvious`.
    use_condition (hypothesis 7: {P}) (obvious: {1 + 1 = 2}) (hypothesis 8: {Q}) in (hypothesis 5: {P => (1 + 1 = 2) => Q => R}) as (hypothesis 9: {R})
```

Example 1:
Suppose current proof gap:

```text
ASSUM:
hypothesis 1. A ⊆ B
hypothesis 2. A ⊆ B => X ⊆ C => X ⊆ B
GOAL:
X ⊆ B
```

Execute: `use_condition (hypothesis 1: {A ⊆ B}) in (hypothesis 2: {A ⊆ B => X ⊆ C => X ⊆ B}) as (hypothesis 3: {X ⊆ C => X ⊆ B})`

Resulting proof gap:

```text
ASSUM:
hypothesis 1. A ⊆ B
hypothesis 2. A ⊆ B => X ⊆ C => X ⊆ B
hypothesis 3. X ⊆ C => X ⊆ B
GOAL:
X ⊆ B
```

Example 2:
Suppose current proof gap:

```text
ASSUM:
hypothesis 1. A ⊆ B
hypothesis 2. A ⊆ B => C ⊆ C => X ⊆ B
GOAL:
X ⊆ B
```

Execute: `use_condition (hypothesis 1: {A ⊆ B}) (obvious: {C ⊆ C}) in (hypothesis 2: {A ⊆ B => C ⊆ C => X ⊆ B}) as (hypothesis 3: {X ⊆ B})`

Resulting proof gap:

```text
ASSUM:
hypothesis 1. A ⊆ B
hypothesis 2. A ⊆ B => C ⊆ C => X ⊆ B
hypothesis 3. X ⊆ B
GOAL:
X ⊆ B
```

#### `get_exists`
**Semantics**: Instantiate a specified number of existentially bound variables in a hypothesis and update it.
Note: New names must not conflict with existing variable names.

**Usage**:
```dsl
    get_exists (hypothesis <idx>: {<desc>}) (<bound_var> := {<name>}) ...
```

Examples:
```dsl
    # hypothesis 1 becomes `P(x1)`. Ensure 'x1' has not been used.
    get_exists (hypothesis 1: {exists (x), P(x)}) (x := {x1})
```
```dsl
    # Content becomes `Q(x2)`. Ensure 'x2' is fresh.
    get_exists (hypothesis 2: {exists (x), Q(x)}) (x := {x2})
```
```dsl
    # hypothesis 4 becomes `exists (y), (P(x3) => Q(y))`.
    get_exists (hypothesis 4: {exists (x), (exists (y), (P(x) => Q(y)))}) (x := {x3})
```
```dsl
    # hypothesis 5 becomes `T(x4) => S(x5)`.
    get_exists (hypothesis 5: {exists (x), (exists (y), (T(x) => S(y)))}) (x := {x4}) (y := {x5})
```

Example:
Suppose current proof gap:


```text
ASSUM:
hypothesis 1. exists (x), ((x > 3) => (x > 2))
GOAL:
a > 2
```

Execute: `get_exists (hypothesis 1: {exists (x), (x > 3 => x > 2)}) (x := {x1})`

Resulting proof gap:

```text
ASSUM:
hypothesis 1. x1 > 3 => x1 > 2
GOAL:
a > 2
```

#### `get_forall`
**Semantics**: Instantiate universally bound variables in the GOAL.
Note: The number of consecutive universal quantifiers must not be less than the terms following `get_forall`. New names must be fresh.

**Usage**:
```dsl
    get_forall (GOAL: {<desc>}) (<bound_var> := {<name>}) ...
```

Examples:
```dsl
    # Instantiate 'y' in GOAL as 'z'. GOAL becomes `z > x => z > 0`.
    get_forall (GOAL: {forall (y), (y > x => y > 0)}) (y := {z})
```
```dsl
    # Instantiate 'A' and 'B' as 'y' and 'x'. GOAL becomes `P(y, t) => Q(x, s)`.
    get_forall (GOAL: {forall (A), (forall (B), (P(A, t) => Q(B, s)))}) (A := {y}) (B := {x})
```
```dsl
    # Instantiate 'A' as 'k'. GOAL becomes `forall (B), (f(k, p) => g(B, q))`.
    get_forall (GOAL: {forall (A), (forall (B), (f(A, p) => g(B, q)))}) (A := {k})
```

Example:
Suppose current proof gap:


```text
ASSUM:
hypothesis 1. exists (x), (x > 3 => x > 2)
GOAL:
forall (P),(forall (Q), (P > 0 => Q > 1 => a > 2))
```

Execute: `get_forall (GOAL: {forall (P) (Q), (P > 0 => Q > 1 => a > 2)}) (P := {x}) (Q := {y})`.

Resulting proof gap:

```text
ASSUM:
hypothesis 1. exists (x), (x > 3 => x > 2)
GOAL:
x > 0 => y > 1 => a > 2
```

Example 2:
Suppose current proof gap:


```text
ASSUM:
hypothesis 1. exists (x), (x > 3 => x > 2)
GOAL:
forall (P),(forall (Q), (P > 0 => Q > 1 => a > 2))
```

Execute: `get_forall (GOAL: {forall (P) (Q), (P > 0 => Q > 1 => a > 2)}) (P := {x})`.

Resulting proof gap:

```text
ASSUM:
hypothesis 1. exists (x), (x > 3 => x > 2)
GOAL:
forall (Q), (x > 0 => Q > 1 => a > 2)
```

#### `get_condition`
**Semantics**: For a GOAL of form `p1 => p2 => ... => pn`, introduce `p1, p2, ..., pi` as new hypotheses, changing the GOAL to `pi+1 => ... => pn`.

**Usage**:
```dsl
    get_condition (hypothesis <index>: {<description>}) (hypothesis <index>: {<description>}) ... in (GOAL: {<description>})
```

Examples:
```dsl
    # If the largest hypothesis index is 3, use 4 and 5 for new ones. ASSUM adds hypothesis 4 and 5. GOAL becomes `R`.
    get_condition (hypothesis 4: {x > 1}) (hypothesis 5: {P}) in (GOAL: {x > 1 => P => R})
```
```dsl
    # If the largest hypothesis index is 2, use 3. GOAL becomes `S => P /\ Q`.
    get_condition (hypothesis 3: {t > 1}) in (GOAL: {t > 1 => S => P /\ Q})
```

Example:
Suppose current proof gap:


```text
ASSUM:
hypothesis 1. exists (x), (x > 3 => x > 2)
GOAL:
P => Q => a > 2
```

Execute: `get_condition (hypothesis 2: {P}) (hypothesis 3: {Q}) in (GOAL: {P => Q => a > 2})`. New indices start from 2.

Resulting proof gap:

```text
ASSUM:
hypothesis 1. exists (x), (x > 3 => x > 2)
hypothesis 2. P
hypothesis 3. Q
GOAL:
a > 2
```

#### `assert`
**Semantics**: Prove an intermediate proposition, then add it as a new hypothesis to the current proof gap.

**Usage**:
```dsl
    assert (hypothesis <new_idx>: {<desc>})
```
With the direct form, the system checks `<desc>` with the automatic solver under the current assumptions. The new hypothesis is added only if that check succeeds.

`assert` can also carry a local DSL proof block. Manual proofs must be introduced explicitly with `by proof`:
```dsl
    assert (hypothesis <new_idx>: {<desc>}) by proof {
      1. <dsl_instruction>
      2. <dsl_instruction>
    }
```

The opening brace may also appear on the next non-empty line:

```dsl
    assert (hypothesis <new_idx>: {<desc>}) by proof
    {
      1. <dsl_instruction>
    }
```

Execution rules:

- The proof block creates a local proof gap whose assumptions are copied from the current gap and whose goal is `<desc>`.
- The block may contain ordinary DSL instructions, including nested `assert ... by proof { ... }`.
- Hypotheses introduced inside the block do not leak to the outer proof gap; only `<desc>` is added outside after it is proved.
- The block must contain at least one DSL instruction.
- The opening `{` may appear on the same line as `by proof`, or alone on the next non-empty line. The closing `}` must appear alone on its own line. Split gaps inside assert proof blocks are not supported yet.
- In the REPL, `assert (...) by proof` without braces enters an interactive assert-proof context. In DSL files, this form must include a `{ ... }` proof block.

Example:
```dsl
    # Introduce `0 ≠ -1`. If max index is 4, use index 5.
    assert (hypothesis 5: {0 ≠ -1})
```

Local proof example:
```dsl
    assert (hypothesis 2: {a = a}) by proof {
      1. get_prop (hypothesis 1: {forall (x), (x = x)}) (x := {a}) as (hypothesis 2: {a = a})
      2. apply (hypothesis 2: {a = a})
    }
    apply (hypothesis 2: {a = a})
```

Example 1:
Suppose current proof gap:

```text
ASSUM:
hypothesis 1. 2 * x < 1

GOAL:
2 * x - 1 < 0
```

Execute: `assert (hypothesis 2: {2 * x - 1 < 0})`

Resulting proof gap:

```text
ASSUM:
hypothesis 1. 2 * x < 1
hypothesis 2. 2 * x - 1 < 0

GOAL:
2 * x - 1 < 0
```

#### `case_analysis`
**Semantics**: Perform case analysis on a hypothesis containing `\/` or `∨` (`P1 \/ P2 \/ ...`). This splits the current proof gap into multiple gaps.

**Usage**:
```dsl
    case_analysis (hypothesis <index>: {<description>})
```

Example:

```text
ASSUM:
hypothesis 1. (a < 0 /\ b > 0) \/ (a > 0 /\ b < 0)
hypothesis 2. x > 0

GOAL:
a * b < x
```

Execute: `case_analysis (hypothesis 1: {(a < 0 /\ b > 0) \/ (a > 0 /\ b < 0)})`

This generates two new proof gaps:

```text
ASSUM:
hypothesis 1. a < 0 /\ b > 0
hypothesis 2. x > 0

GOAL:
a * b < x
```

AND


```text
ASSUM:
hypothesis 1. a > 0 /\ b < 0
hypothesis 2. x > 0

GOAL:
a * b < x
```

#### `or_intro`
**Semantics**: When the current `GOAL` is a top-level binary disjunction `P1 \/ P2` or `P1 ∨ P2`, choose whether to prove the left or right sub-goal. This command does not split the proof gap; it replaces the current `GOAL` with the selected side.

**Usage**:
```dsl
    or_intro left
    or_intro right
```

Example:

```text
ASSUM:

GOAL:
(a = a) \/ (b = c)
```

Execute: `or_intro left`

The proof gap becomes:

```text
ASSUM:

GOAL:
a = a
```
