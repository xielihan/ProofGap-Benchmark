# ProofGap Lean workspace

A shared Lean environment for the two Lean variants of ProofGap-Benchmark,
based on Demidovich's mathematical analysis exercises
(吉米多维奇《数学分析习题集》).

| Dataset | Contents | Build target |
| --- | --- | --- |
| [ProofGap_lean](ProofGap_lean/) | Backend-printed statements with proof placeholders | `ProofGapLeanBackend` |
| [ProofGap_lean_llm](ProofGap_lean_llm/) | Codex-converted statements with ongoing semantic review and proof placeholders | `ProofGapLean` |

NFL and Lean have different logical foundations, so direct backend printing
does not cover every NFL gap. Gaps outside that coverage are converted to
Lean with Codex and undergo semantic review and correction against their NFL
statements. These exercise modules are collected in `ProofGap_lean_llm`;
`ProofGap_lean` contains the backend-printed modules.

The variants contain disjoint exercise sets and together cover all **2,947
exercises and 25,987 gap IDs** in NFL.

The 2026-09-26 refresh incorporates proofgrader commit `f40b9866a3`.
The latest update copies 18 LLM modules; across both refreshes, 145 distinct
LLM modules and 292 backend modules were updated. Benchmark-specific
gap-coverage corrections for exercises 3801 and 3802 are retained, and gap 5
of exercise 4330 restores NFL assumptions 12 and 13 as explicit hypotheses.
The [source snapshot](source_snapshot.json) records provenance and local changes.
Exercises 2196, 2197, 2202, 4186, 4246, and 4247 also receive syntax and type
elaboration adjustments for the pinned Mathlib environment.

The LLM modules contain no proposition `True` tokens. The six exercises that
used string-length predicates now contain mathematical statements, but
restoring the mathematical expressions does not by itself restore every
required assumption. Consult the
[known issues](KNOWN_ISSUES.md) and [machine-readable exclusions](known_issues.json)
before selecting targets for mathematical proof-generation evaluation.

Both datasets use **Lean and Mathlib `v4.29.0-rc6`** and share the dependency
cache in `.lake/`. Their proof-completion task is described in the
[benchmark overview](../README.md#task).

## Setup

Install Lean through `elan`, then enter this directory from the repository
root and download Mathlib's precompiled cache:

```sh
cd ProofGap_Lean
lake exe cache get
```

Open `ProofGap_Lean/` as the workspace in your Lean editor. All remaining
commands on this page run from this directory.

## Check an exercise

Build one exercise and its dependencies:

```sh
# LLM-converted exercise
lake build +ProofGap_lean_llm.exercise_100

# Backend-printed exercise
lake build +ProofGap_lean.exercise_1000
```

After dependencies are built, check an edited exercise directly:

```sh
lake env lean ProofGap_lean_llm/exercise_100.lean
lake env lean ProofGap_lean/exercise_1000.lean
```

A successful build checks module elaboration. Proof-completion evaluation
also requires checking that the target proof and its dependencies do not
use proof placeholders or introduce new axioms.

## Build a dataset

The default target builds the LLM-converted exercise modules independently:

```sh
lake build ProofGapLean
```

To attempt a build of every backend exercise:

```sh
lake build ProofGapLeanBackend
```

Both datasets compile exercises as separate modules, allowing helper names
to be reused across exercises. Some backend modules may report errors
outside their last gap; see the [backend guide](ProofGap_lean/README.md#validation-scope).

## Reproduce the environment

| File | Role |
| --- | --- |
| [lean-toolchain](lean-toolchain) | Pins the Lean toolchain |
| [lakefile.toml](lakefile.toml) | Defines both dataset targets and the Mathlib requirement |
| [lake-manifest.json](lake-manifest.json) | Locks all dependency revisions |

Mathlib is locked to commit `5c8398df528176d9c87ccd9226ba8f7c8852d59c`.
Keep these configuration files together when reproducing an evaluation.
The first setup may download the pinned toolchain and dependencies.

The two individual exercises above and LLM exercises 3801 and 3802 have been
checked in this environment.
A full build of both datasets has not been validated.

The 2026-09-26 refresh passed complete-module checks for backend exercises
89, 752, and 1009, LLM exercises 3052 and 3499, and all 18 LLM modules updated
in the latest refresh. Exercise 4330, gap 5 was proved separately from its
restored hypotheses without `sorry` or added axioms. The packaged theorem retains
its proof placeholder for evaluation.
