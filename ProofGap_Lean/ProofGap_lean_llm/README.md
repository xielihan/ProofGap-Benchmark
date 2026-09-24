# ProofGap_lean_llm

ProofGap_lean_llm is the LLM-converted Lean 4 dataset in ProofGap-Benchmark,
built from Demidovich's mathematical analysis exercises
(吉米多维奇《数学分析习题集》) and packaged with reference proofs.
Each benchmark target is a theorem named `gapN` inside an `Exercise*.lean`
module.

The `ProofGap_nfl/` and `ProofGap_lean/` datasets use two printers over common
proof-gap abstract syntax trees; this directory uses the `llm` suffix to
identify LLM conversion. See the [benchmark overview](../../README.md) for
dataset sizes and differences in coverage and statements.
The Lean module namespace and build target remain `ProofGapLean`. Environment
configuration is shared with `ProofGap_lean/` in the parent `ProofGap_Lean/` directory.

## Dataset contents

- **3,015** exercise modules
- **26,116** `gapN` theorems
- Lean **v4.29.0-rc6**
- Mathlib **v4.29.0-rc6**
- One aggregate entry point importing every exercise

Exercise identifiers are strings derived from filenames. This preserves
variants such as `Exercise131_1.lean` and `Exercise131_2.lean` as distinct
benchmark cases.

## Repository layout

```text
ProofGap_lean_llm/
├── README.md
├── ProofGapLean.lean
└── ProofGapLean/
    ├── Prelude.lean
    ├── Prelude/
    │   └── *.lean
    └── Exercises/
        └── Exercise*.lean
```

- `ProofGapLean/Exercises/` contains all exercise modules and gap theorems.
- `ProofGapLean/Prelude/` contains the local definitions and checking support
  required by the exercises.
- `ProofGapLean.lean` imports all 3,015 exercise modules.

## Build

Install Lean through `elan`. From the **Lean workspace root** (`ProofGap_Lean/`, the
parent of this directory), run:

```sh
lake exe cache get
lake build ProofGapLean
```

The shared [toolchain](../lean-toolchain), [Lake configuration](../lakefile.toml),
and [dependency manifest](../lake-manifest.json) pin Lean, Mathlib, and the
transitive dependencies. This dataset uses the `ProofGap_Lean/.lake/` cache alongside
the backend-printed dataset.

To build one exercise and its local dependencies from the `ProofGap_Lean/` directory:

```sh
lake build +ProofGapLean.Exercises.Exercise3591
```

Once its dependencies have been built, check the source file directly with:

```sh
lake env lean ProofGap_lean_llm/ProofGapLean/Exercises/Exercise3591.lean
```

## Benchmark unit

For a theorem such as

```lean
theorem gap7 (...) : target := by
  ...
```

the benchmark input should preserve the module's imports, definitions, helper
declarations, preceding theorem statements, and the exact target statement.
Only the proof body of the selected `gapN` theorem should be replaced by the
candidate proof.

A candidate is successful only if the reconstructed exercise module compiles
under the pinned environment without proof escapes such as `sorry`, `admit`,
new axioms, or unsafe metaprogramming shortcuts.

Each exercise can be checked as a module under the complete source tree. Some
modules import earlier exercise modules, so a reduced subset must retain the
transitive local dependencies of every selected target.
