# ProofGap_lean

**15,191 Lean proof obligations across 1,884 exercises**, based on
Demidovich's mathematical analysis exercises
(吉米多维奇《数学分析习题集》).

The backend prints these Lean statements using the same proof-gap AST
representation as the NFL printer. This variant provides theorem statements
with `sorry` proof placeholders. It shares its environment with the
[LLM-converted variant](../ProofGap_lean_llm/).

## Data format

Each `exercise_<id>.lean` is a separate Lean module containing imports,
helper definitions, and the exercise's gap theorems. A target is named
`proof_gap_exercise_<id>_<gap_id>`.

For example, [exercise_1000.lean](exercise_1000.lean) contains
`proof_gap_exercise_1000_1`, `proof_gap_exercise_1000_2`, and further targets.
Each theorem's parameters specify the assumptions available for that gap.

Coverage and some statements differ from the NFL and LLM variants. Preserve
exercise suffixes and gap identifiers when selecting or reporting targets;
matching identifiers across variants do not guarantee equivalent statements.

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

For proof-generation evaluation, identify the targets that elaborate before
replacing their proofs. Report any statement corrections separately so that
the evaluated proof obligations remain clear.

See the [benchmark overview](../../README.md#evaluation) for evaluation and
reporting guidance.
