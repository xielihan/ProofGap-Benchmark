# ProofGap Lean workspace

A shared environment for the two Lean datasets in ProofGap-Benchmark.

| Dataset | Construction | Build target |
| --- | --- | --- |
| [ProofGap_lean](ProofGap_lean/) | Printed by the backend from the same proof-gap ASTs as NFL | `ProofGapLeanBackend` |
| [ProofGap_lean_llm](ProofGap_lean_llm/) | Converted from NFL with Codex | `ProofGapLean` |

Both datasets use **Lean and Mathlib `v4.29.0-rc6`**. The files
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` pin the shared
toolchain and dependencies.

## Setup

Install Lean through `elan`, then run from the repository root:

```sh
cd ProofGap_Lean
lake exe cache get
```

Open `ProofGap_Lean/` as the workspace in your Lean editor. Run the remaining
commands from this directory.

## Check an exercise

```sh
# Backend-printed exercise
lake env lean ProofGap_lean/exercise_1000.lean

# LLM-converted exercise
lake env lean ProofGap_lean_llm/exercise_100.lean
```

## Build a dataset

```sh
lake build ProofGapLeanBackend
lake build ProofGapLean
```

For proof completion, replace the selected theorem's `sorry` while preserving
its statement and allowed context. See the
[benchmark overview](../README.md#evaluation) for evaluation and reporting rules.
