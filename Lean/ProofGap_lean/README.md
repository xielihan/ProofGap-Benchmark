# ProofGap_lean

This dataset contains 1,884 exercise files printed directly into Lean from
the same proof-gap ASTs used for `ProofGap_nfl/`. It shares its Lean and Mathlib
environment with `ProofGap_lean_llm/`.

## Environment and checking

Install Lean through `elan`, then run these commands from the **Lean workspace
root** (`Lean/`):

```sh
lake exe cache get
lake build +ProofGap_lean.exercise_1000
```

To check a file directly after fetching Mathlib's cache:

```sh
lake env lean ProofGap_lean/exercise_1000.lean
```

To attempt compilation of all backend exercise modules:

```sh
lake build ProofGapLeanBackend
```

Every exercise is compiled as a separate module, so generated helper names
can be reused across files without importing the exercises into one module.

The shared [toolchain](../lean-toolchain) pins Lean to `v4.29.0-rc6`.
The [Lake configuration](../lakefile.toml) and
[dependency manifest](../lake-manifest.json) pin Mathlib to the corresponding
release and lock every dependency revision. Both Lean datasets use the
`Lean/.lake/` cache.

## Compilation status

The source subset is `all_gaps_printed__last_gap_compiles`: every non-internal
gap was printed to Lean and the last gap compiled without errors in the
original selection. This does not guarantee that each whole exercise file or
the complete dataset will compile. `sorry` placeholders are retained, and
successful compilation alone does not establish completed proofs.

See the [benchmark overview](../../README.md) for dataset counts and provenance.
