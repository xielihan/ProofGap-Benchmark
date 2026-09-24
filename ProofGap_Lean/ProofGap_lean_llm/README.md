# ProofGap_lean_llm

**26,116 Lean gap theorems across 3,015 exercise modules**, with reference
proofs. This variant uses LLM conversion to formalize Demidovich's
mathematical analysis exercises (吉米多维奇《数学分析习题集》).

Each target is a theorem named `gapN` within an exercise module. The dataset
uses the [shared Lean environment](../README.md) and the build target
`ProofGapLean`.

## Data format

```text
ProofGap_lean_llm/
├── ProofGapLean.lean                 # Imports all exercise modules
└── ProofGapLean/
    ├── Prelude.lean                  # Aggregate support import
    ├── Prelude/                      # Shared definitions and support
    └── Exercises/
        └── Exercise<id>.lean         # Definitions, gap targets, and proofs
```

An item is identified by its exercise module and gap theorem, for example
`ProofGap.Exercise2.gap1` in
[Exercise2.lean](ProofGapLean/Exercises/Exercise2.lean).
Treat suffixes such as `Exercise131_1` and `Exercise131_2` as distinct module
identifiers. Coverage and some statements differ from the other variants.

`Prelude/` supplies definitions and support shared by exercises. Some
exercise modules also import other exercises, so selected subsets must keep
their transitive local dependencies.

## Proof completion

For a target theorem:

1. Retain its imports, required definitions, allowed context, and exact
   statement.
2. Withhold the reference proof from model input and replace the target's
   proof body with the generated candidate.
3. Check the reconstructed module in the pinned environment and ensure that
   the target proof and its dependencies do not rely on `sorry`, `admit`, or
   newly introduced axioms.

Reference proofs support evaluation; their presence is not a substitute for
verifying a generated candidate. The repository does not include an automated
Lean proof-submission evaluator.

## Check an exercise

After [setting up the environment](../README.md#setup), run from
`ProofGap_Lean/`:

```sh
lake build +ProofGapLean.Exercises.Exercise2
```

After dependencies are built, check an edited module directly:

```sh
lake env lean ProofGap_lean_llm/ProofGapLean/Exercises/Exercise2.lean
```

To build all exercise modules through the aggregate entry point:

```sh
lake build ProofGapLean
```

The shared workspace pins Lean and Mathlib to `v4.29.0-rc6`. Individual
exercise checks have been performed; a full-dataset build has not been
validated in this workspace.

See the [benchmark overview](../../README.md#evaluation) for evaluation and
reporting guidance.
