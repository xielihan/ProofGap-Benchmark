# ProofGap_lean_llm

**10,882 Lean proof gaps across 1,072 exercises.**

This dataset contains Lean statements converted from NFL with Codex for
exercises outside direct backend coverage. Each proof gap consists of a
target statement and its available assumptions, with a `sorry` placeholder
for the proof to be completed.

## Data format

Each `exercise_<id>.lean` file imports Mathlib and contains the definitions
and gap statements for one exercise. Theorems are named
`proof_gap_exercise_<id>_<gap_id>`, with identifiers corresponding to
[ProofGap_nfl](../../ProofGap_nfl/).

To complete a gap, replace its proof placeholder while preserving the
statement, definitions, and allowed assumptions. The resulting proof and
its dependencies must not rely on `sorry`, `admit`, or newly introduced axioms.

## Usage

Both Lean datasets use the [shared Lean environment](../README.md#setup).
After setup, check an exercise from the repository root:

```sh
cd ProofGap_Lean
lake env lean ProofGap_lean_llm/exercise_100.lean
```

To build all modules in this dataset, run `lake build ProofGapLean` from
`ProofGap_Lean/`.

See the [benchmark overview](../../README.md#evaluation) for evaluation and
reporting rules.
