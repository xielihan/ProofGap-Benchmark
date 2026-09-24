# ProofGap-Benchmark

A step-level benchmark for formal reasoning in mathematical analysis.
The base snapshots of `ProofGap_nfl` and `ProofGap_lean` contain NFL and Lean
statements printed from common proof-gap abstract syntax trees (ASTs).
The NFL snapshot has documented gap/answer updates below. `ProofGap_lean_llm` contains
LLM-converted Lean formalizations with reference proofs.

## Datasets

| Dataset | Representation | Exercises | Proof gaps |
| --- | --- | ---: | ---: |
| [ProofGap_nfl](ProofGap_nfl/) | NFL statements printed from proof-gap ASTs | 2,947 | 25,987 |
| [ProofGap_lean](Lean/ProofGap_lean/) | Lean statements printed from the same ASTs | 1,884 | 15,191 source gaps |
| [ProofGap_lean_llm](Lean/ProofGap_lean_llm/) | LLM-converted Lean formalizations | 3,015 | 26,116 `gapN` theorems |

The backend-printed Lean set is a selected subset of the AST-printed exercises;
its gap count is computed from the corresponding NFL exercises. The
LLM-converted set comes from a different snapshot. Exercise and gap IDs are
not fully aligned across snapshots, and equal IDs alone do not establish
semantic equivalence.

The NFL update replaces 13 gap/DSL pairs, including content changes to 8 gap
statements. These updated statements should not be assumed to match the
unchanged backend Lean snapshot.

The NFL dataset includes 9,385 accompanying DSL answer files; the remaining
16,602 gaps have no packaged DSL answer.

## Layout

```text
ProofGap-Benchmark/
├── README.md
├── ProofGap_nfl/
│   ├── README.md
│   ├── check.py
│   ├── settings.ini
│   ├── bin/
│   ├── thm/all_lib_idx.md
│   └── exercise_<id>/gap_<gap_id>/
│       ├── gap.txt
│       └── dsl.txt                  # Present for 9,385 gaps
└── Lean/
    ├── README.md
    ├── lean-toolchain
    ├── lakefile.toml
    ├── lake-manifest.json
    ├── ProofGap_lean/
    │   └── exercise_<id>.lean
    └── ProofGap_lean_llm/
        ├── ProofGapLean.lean
        └── ProofGapLean/
            ├── Prelude.lean
            ├── Prelude/
            └── Exercises/Exercise<id>.lean
```

## NFL verification

The NFL package includes the `test_dsl` verifier, its settings, and the supplied
theorem library, together with DSL answers for a subset of gaps. Check a
packaged answer from the repository root:

```sh
python3 ProofGap_nfl/check.py ProofGap_nfl/exercise_2/gap_1/gap.txt ProofGap_nfl/exercise_2/gap_1/dsl.txt
```

To evaluate a generated proof, pass the candidate file instead:

```sh
python3 ProofGap_nfl/check.py ProofGap_nfl/exercise_2/gap_1/gap.txt /path/to/candidate.dsl
```

The checker selects the packaged binary for Linux x86-64, Windows x86-64, or
macOS arm64. It preserves the source gap and writes isolated results and logs
under `ProofGap_nfl/verify/`. See the [NFL README](ProofGap_nfl/README.md) for
platform requirements, configuration, and proof acceptance criteria.

## Lean environment

Both Lean datasets share one workspace under `Lean/`, pinning Lean and Mathlib
to `v4.29.0-rc6` and all dependencies to their recorded revisions. Run Lean
commands from that directory:

```sh
cd Lean
lake exe cache get
lake build +ProofGapLean.Exercises.Exercise2
lake build +ProofGap_lean.exercise_1000
```

The last two commands check one LLM-converted exercise and one backend-printed
exercise. See the [Lean environment guide](Lean/README.md) for full build
targets, direct file checks, and editor setup.

## Provenance and scope

- The NFL base snapshot comes from `ex_gap_25987_gap_dsl_20260910.zip`:
  25,987 gap statements and 9,385 answer files are retained. Thirteen gap/DSL
  pairs were replaced byte-for-byte from
  `ProofGap_83_Linux_PASS_gap_dsl_with_logs_20260924.zip`, including content
  changes to 8 gap statements; all other gap/answer files remain unchanged.
  All 9,385 current answers passed with the updated macOS arm64 verifier and
  supplied theorem library on 2026-09-24, including all 9,372 previously
  passing answers. The bundled Linux and Windows binaries have not been
  rebuilt with the binder fix or executed on this host. Exclude answer files
  from model inputs when evaluating proof generation. The theorem library is
  the supplied `all_lib_idx(1).md`, copied unchanged as `thm/all_lib_idx.md`.
- Backend Lean files come from `all_gaps_printed__last_gap_compiles`: every
  non-internal gap was printed and the last gap compiled in the original
  selection. Whole-file or full-dataset compilation is not guaranteed;
  `sorry` placeholders are retained.
- LLM Lean sources come from `ProofGap-Lean/` in `aaai_data_anonymized.zip`.
  Their source bytes are preserved, while build configuration and documentation
  are adapted to this repository.

File hashes were checked during copying and reorganization. The
[NFL README](ProofGap_nfl/README.md) describes the verifier origins and
platform-specific validation scope. The reorganized Lean workspace was
checked with one exercise from each dataset; a full
benchmark rebuild was not performed. Successful compilation of a statement
containing `sorry` does not constitute a completed proof.
