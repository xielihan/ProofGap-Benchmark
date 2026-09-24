# Shared Lean environment

`ProofGap_lean/` contains AST-printed Lean statements; `ProofGap_lean_llm/`
contains LLM-converted formalizations with reference proofs. Both use the
configuration and dependency cache in this `Lean/` directory.

## Setup

Install Lean through `elan` and open `Lean/` as the workspace in your Lean
editor. From the repository root, enter the workspace and fetch Mathlib's
precompiled cache:

```sh
cd Lean
lake exe cache get
```

| File | Purpose |
| --- | --- |
| [lean-toolchain](lean-toolchain) | Lean `v4.29.0-rc6` |
| [lakefile.toml](lakefile.toml) | Mathlib `v4.29.0-rc6` and both dataset targets |
| [lake-manifest.json](lake-manifest.json) | Exact dependency revisions |

Mathlib is locked to commit `5c8398df528176d9c87ccd9226ba8f7c8852d59c`.
Keep the manifest when reproducing the environment. The first setup may
download the pinned toolchain and dependencies. All commands below run from
`Lean/`; both datasets share `Lean/.lake/`.

## Build and check

Build the LLM-converted dataset, also the default target of `lake build`:

```sh
lake build ProofGapLean
```

Build individual exercises with their dependencies:

```sh
lake build +ProofGapLean.Exercises.Exercise2
lake build +ProofGap_lean.exercise_1000
```

After their dependencies have been built, check the files directly:

```sh
lake env lean ProofGap_lean_llm/ProofGapLean/Exercises/Exercise2.lean
lake env lean ProofGap_lean/exercise_1000.lean
```

To attempt compilation of every backend-printed exercise:

```sh
lake build ProofGapLeanBackend
```

Backend exercises are separate modules so generated helper declarations can
reuse names. The source subset was selected by last-gap compilation, so a
full build can report errors in other gaps. `sorry` placeholders do not count
as completed proofs.

The shared workspace was smoke-tested with the two individual exercises above.
It does not certify full-dataset compilation or proof completion.

See the [backend dataset README](ProofGap_lean/README.md),
[LLM dataset README](ProofGap_lean_llm/README.md), and
[benchmark overview](../README.md) for further details.
