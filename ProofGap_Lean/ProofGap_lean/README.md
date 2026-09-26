# ProofGap_lean

**15,105 Lean proof obligations across 1,875 exercises**, based on
Demidovich's mathematical analysis exercises
(吉米多维奇《数学分析习题集》).

The backend prints these Lean statements using the same proof-gap AST
representation as the NFL printer. This variant provides theorem statements
with `sorry` proof placeholders. It shares its environment with the
[LLM-converted variant](../ProofGap_lean_llm/).

NFL and Lean have different logical foundations, which prevents direct
backend printing from covering every NFL proof gap. For gaps outside this
coverage, Codex produces Lean formalizations that undergo semantic review
and correction against NFL. Those exercise modules are provided in
`ProofGap_lean_llm`.

## Data format

Each `exercise_<id>.lean` is a separate Lean module containing imports,
helper definitions, and the exercise's gap theorems. A target is named
`proof_gap_exercise_<id>_<gap_id>`.

For example, [exercise_1000.lean](exercise_1000.lean) contains
`proof_gap_exercise_1000_1`, `proof_gap_exercise_1000_2`, and further targets.
Each theorem's parameters specify the assumptions available for that gap.

This variant and the LLM variant contain disjoint exercise sets. Their union
covers every NFL exercise and gap ID. Preserve exercise suffixes and gap
identifiers when selecting or reporting targets; matching identifiers with
NFL does not guarantee equivalent statements.

## Proof completion

Select a gap theorem, retain its statement and allowed context, and replace
its `by sorry` proof with a candidate proof. Module compilation alone is not
a completion criterion, because Lean accepts `sorry` with a warning. Check
that the target proof and the declarations it relies on contain no proof
placeholders or newly introduced axioms.

## Check an exercise

Set up the [shared environment](../README.md#setup), then run from
`ProofGap_Lean/`:

```sh
lake build +ProofGap_lean.exercise_1000
```

To check an edited module directly:

```sh
lake env lean ProofGap_lean/exercise_1000.lean
```

To attempt a build of all backend exercises:

```sh
lake build ProofGapLeanBackend
```

## Validation scope

Exercises were selected by successful compilation of their last gap. Every
non-internal gap is included, but other gaps may have elaboration errors;
whole-module and full-dataset compilation are not guaranteed.

The 2026-09-26 refresh incorporates proofgrader updates through `32c45ddd63`,
updating 292 modules with printer and Lean/Mathlib compatibility fixes.
The nine exercises 89, 90, 124, 131_1, 131_2, 132_1, 132_2, 382_2, and 752
now use `StrictMono` for subsequence index conditions previously printed as
`True`. This restores the strictly increasing requirement for 197 affected
gap statements. Other `True` occurrences remain, including type predicates;
their presence alone is not a statement-correctness verdict.

Complete-module checks of the refreshed exercises 89, 752, and 1009 passed
under the shared environment. This is a sample check, not a full-dataset build.

For proof-generation evaluation, identify the targets that elaborate before
replacing their proofs. Report any statement corrections separately so that
the evaluated proof obligations remain clear.

See the [benchmark overview](../../README.md#evaluation) for evaluation and
reporting guidance.
