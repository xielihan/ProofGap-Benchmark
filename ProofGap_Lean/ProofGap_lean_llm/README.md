# ProofGap_lean_llm

**10,882 Lean gap statements across 1,072 exercise modules.** This variant
uses Codex to formalize Demidovich's mathematical analysis exercises
(吉米多维奇《数学分析习题集》).

NFL and Lean have different logical foundations, so the backend cannot
directly print a Lean version of every NFL proof gap. This variant covers
gaps outside direct backend coverage: Codex converts them to Lean, followed
by ongoing semantic review and correction against the NFL assumptions and goals.
The resulting statements are organized into exercise modules.

The dataset primarily contains theorem statements with `sorry` proof
placeholders. It is intended for inspecting formalized proof obligations
and developing candidate proofs, rather than serving as a collection of
completed reference proofs.

## Data format

```text
ProofGap_lean_llm/
├── README.md
└── exercise_<id>.lean    # Definitions and gap statements for one exercise
```

Each module imports Mathlib and contains its own definitions and theorems.
A target is named `proof_gap_exercise_<id>_<gap_id>`, possibly inside a
namespace. For example, [exercise_100.lean](exercise_100.lean) contains
`proof_gap_exercise_100_1` through `proof_gap_exercise_100_8`.
Treat suffixes such as `exercise_1014_1` and `exercise_1014_2` as distinct
exercise identifiers.

All 1,072 exercise IDs and 10,882 gap IDs occur in `ProofGap_nfl`.
These are identifier correspondences, not a guarantee of semantic equivalence.
Together with the disjoint backend variant, these modules cover all 2,947
NFL exercise IDs and 25,987 NFL gap IDs.

Some modules collect shared assumptions in a `CommonHypotheses` structure.
Its fields are part of each target's allowed context and can be accessed
through the `hcommon` parameter.

## Proof completion

Select a target theorem, preserve its statement and allowed context, and
replace its proof placeholder with a candidate proof. Verify that the target
proof and its dependencies do not rely on `sorry`, `admit`, or newly
introduced axioms.

Some converted statements use simplified definitions or semantic placeholders.
Inspect the definitions and mathematical meaning of selected targets before
using them for proof-generation evaluation. Successful Lean compilation
checks elaboration; it does not establish mathematical fidelity or proof
completion.

## Current snapshot and known issues

The latest 2026-09-26 refresh copies 18 updated modules from proofgrader
commit `f40b9866a3`; across both refreshes, 145 distinct LLM modules were
updated. A full scan of the packaged 1,072 modules finds no proposition
`True` tokens. This does not establish that every statement has been repaired.
Exercises 2196, 2197, 2202, 4186, 4246, and 4247 include local syntax and type
elaboration adjustments for the pinned Mathlib environment, recorded in the
[source snapshot](../source_snapshot.json).

Exercises **4185, 4186, 4246, 4247, 4330, and 4331** now express their
**125 targets** as mathematical statements instead of string-length predicates.
The old blanket exclusion for that encoding is retired. Semantic review is
still needed: for example, exercise 4330, gap 8 still omits its required
premises and is excluded. See the [issue details](../KNOWN_ISSUES.md) and
[active and resolved issue records](../known_issues.json).

Exercise 4330, gap 5 has a local statement correction: NFL assumptions 12
and 13 are explicit hypotheses, while the target remains `ρ = 1 → K₁ = 0`.
Only the two premises needed for this step are included. A separate proof
check confirmed the corrected statement without `sorry` or added axioms; the
packaged theorem retains its proof placeholder.

The benchmark's existing corrections for exercises 3801 and 3802 are retained:
they include 29 and 30 gaps, respectively. The upstream versions contain only
17 each. Keeping these corrections preserves all 10,882 LLM gap IDs and exact
identifier coverage with NFL.

## Check an exercise

After [setting up the shared environment](../README.md#setup), run from
`ProofGap_Lean/`:

```sh
lake build +ProofGap_lean_llm.exercise_100
```

To check an edited exercise directly:

```sh
lake env lean ProofGap_lean_llm/exercise_100.lean
```

To build all LLM-converted exercise modules:

```sh
lake build ProofGapLean
```

The library target retains the name `ProofGapLean`, while individual module
names use `ProofGap_lean_llm.exercise_<id>`. Modules compile separately so
that definitions can reuse names across exercises.

The shared workspace pins Lean and Mathlib to `v4.29.0-rc6`. Individual
exercise checks, including the complete modules for exercises 3801 and 3802,
have been performed; a full-dataset build has not been validated in this
workspace.

After the 2026-09-26 refresh, complete-module checks also passed for exercises
3052 and 3499 and all 18 modules in the latest update. These checks establish
elaboration, not semantic equivalence with NFL.

See the [benchmark overview](../../README.md#evaluation) for evaluation and
reporting guidance.
