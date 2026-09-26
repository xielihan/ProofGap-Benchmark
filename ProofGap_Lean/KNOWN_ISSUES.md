# Known Lean statement issues

This list records review status for the snapshot incorporating proofgrader
commit `f40b9866a31419839420e8821c9dfa5b2ba1252a` (2026-09-26), including
Benchmark-specific corrections. It is not an exhaustive semantic audit.

## Outstanding missing assumptions

[Exercise 4330, gap 8](ProofGap_lean_llm/exercise_4330.lean) states
`ρ = 1 → K₂ = 0` with unconstrained real parameters. Taking `ρ = 1` and
`K₂ = 1` disproves this statement. Its NFL context contains prior conditional
equalities that the current Lean statement omits. This gap remains excluded
from mathematical proof-generation evaluation until its premises are restored.

The `issues` array in [known_issues.json](known_issues.json) contains active
exclusions. Resolved encoding issues are kept separately in `resolved_issues`.
The active list is not exhaustive: absence from it does not certify a target's
mathematical meaning, consistency of assumptions, or provability.

## Corrected locally: exercise 4330, gap 5

[Gap 5](ProofGap_lean_llm/exercise_4330.lean) now includes assumptions 12 and
13 from its [NFL source](../ProofGap_nfl/exercise_4330/gap_5/gap.txt):

- `h12`: if `ρ = 1`, then `K₁` equals one half of the cosine integral.
- `h13`: if `ρ = 1`, then one half of that same integral equals zero.

These are the two premises needed for this step. The target remains
`ρ = 1 → K₁ = 0`, and its proof follows by transitivity:

```lean
intro hρ
exact (h12 hρ).trans (h13 hρ)
```

This proof was checked separately under the shared Lean environment, with
`#print axioms` reporting only Lean's standard axioms (`propext`,
`Classical.choice`, and `Quot.sound`), with no `sorryAx` or added axioms.
It uses the explicit hypotheses rather than the admitted theorems for
other gaps. The packaged theorem retains
`sorry` for proof-completion evaluation. The source snapshot records this
local statement correction so it can be preserved during future refreshes.

## Resolved string-length encodings

Upstream commit `6288ac1851` replaced all 125 string-length targets in these
six modules with mathematical statements, preserving their gap IDs:

| Exercise | Gap IDs | Count |
| --- | --- | ---: |
| [4185](ProofGap_lean_llm/exercise_4185.lean) | 1–14 | 14 |
| [4186](ProofGap_lean_llm/exercise_4186.lean) | 1–25 | 25 |
| [4246](ProofGap_lean_llm/exercise_4246.lean) | 1–25 | 25 |
| [4247](ProofGap_lean_llm/exercise_4247.lean) | 1–20 | 20 |
| [4330](ProofGap_lean_llm/exercise_4330.lean) | 1–20 | 20 |
| [4331](ProofGap_lean_llm/exercise_4331.lean) | 1–21 | 21 |

The previous blanket exclusion for string-length encodings is retired.
This resolves that specific encoding defect; it does not certify all 125
statements. Missing-premise issues such as the cases above need separate
review against NFL. No certified evaluation denominator is inferred from
these encoding repairs.

## Backend subsequence index conditions

The refreshed backend modules for exercises 89, 90, 124, 131_1, 131_2, 132_1,
132_2, 382_2, and 752 replace the former `True` encoding of
`IsSubseqIndexFunc` with `StrictMono`. Their 197 affected gap IDs are retained.

## Validation boundaries

All 18 LLM modules in the latest refresh passed complete-module compilation.
Theorem proof bodies still use `sorry` as the intended proof-completion task.
Successful elaboration does not prove the target and does not establish
equivalence with NFL. The backend was originally selected by compilation of
the last gap in each exercise; other gaps may need statement corrections.
Record such corrections separately from proof-generation results.
