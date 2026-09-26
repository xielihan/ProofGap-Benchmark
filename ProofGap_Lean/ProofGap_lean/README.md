# ProofGap_lean

**15,105 Lean proof gaps across 1,875 exercises.**

The backend prints these Lean statements from the same proof-gap abstract
syntax trees (ASTs) used by the NFL printer. Each theorem has a `sorry`
placeholder for the proof to be completed. Exercises outside direct backend
coverage are provided in the [LLM-converted dataset](../ProofGap_lean_llm/).

## Data format

Each `exercise_<id>.lean` file contains the imports, helper definitions,
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
lake env lean ProofGap_lean/exercise_1000.lean
```

To build all modules in this dataset, run `lake build ProofGapLeanBackend`
from `ProofGap_Lean/`.

See the [benchmark overview](../../README.md#evaluation) for evaluation and
reporting rules.
