# ProofGap-Benchmark

A step-level benchmark for formal reasoning, based on Demidovich's mathematical
analysis exercises (吉米多维奇《数学分析习题集》).
`ProofGap_nfl` and `ProofGap_lean` use NFL and Lean printers over common
proof-gap abstract syntax trees (ASTs). `ProofGap_lean_llm` contains LLM-converted
Lean formalizations with reference proofs.

## Datasets

| Dataset | Representation | Exercises | Proof gaps |
| --- | --- | ---: | ---: |
| [ProofGap_nfl](ProofGap_nfl/) | NFL statements printed from proof-gap ASTs | 2,947 | 25,987 |
| [ProofGap_lean](ProofGap_Lean/ProofGap_lean/) | Lean statements printed from the same ASTs | 1,884 | 15,191 source gaps |
| [ProofGap_lean_llm](ProofGap_Lean/ProofGap_lean_llm/) | LLM-converted Lean formalizations | 3,015 | 26,116 `gapN` theorems |

The backend-printed Lean set is a selected subset of the AST-printed exercises;
its gap count is computed from the corresponding NFL exercises. The
datasets differ in coverage and some gap statements. Exercise and gap IDs
are not fully aligned across datasets, and equal IDs alone do not establish
semantic equivalence.

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
└── ProofGap_Lean/
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

The NFL package includes the `test_dsl` verifier, its settings, and the bundled
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

Both Lean datasets share one workspace under `ProofGap_Lean/`, pinning Lean and Mathlib
to `v4.29.0-rc6` and all dependencies to their recorded revisions. Run Lean
commands from that directory:

```sh
cd ProofGap_Lean
lake exe cache get
lake build +ProofGapLean.Exercises.Exercise2
lake build +ProofGap_lean.exercise_1000
```

The last two commands check one LLM-converted exercise and one backend-printed
exercise. See the [Lean environment guide](ProofGap_Lean/README.md) for full build
targets, direct file checks, and editor setup.

## Validation and scope

- All 9,385 packaged NFL answers passed with the macOS arm64 verifier and
  bundled theorem library on 2026-09-24. The Linux and Windows binaries have
  not been rebuilt with the binder fix or executed on the macOS host.
  Exclude answer files from model inputs when evaluating proof generation.
- Backend Lean exercises were selected by compilation of the last gap.
  Whole-file or full-dataset compilation is not guaranteed; `sorry`
  placeholders are retained.
- The shared Lean workspace was checked with one exercise from each dataset;
  a full benchmark rebuild was not performed. Successful compilation of a
  statement containing `sorry` does not constitute a completed proof.

See the [NFL README](ProofGap_nfl/README.md) for platform-specific validation
details and the [Lean environment guide](ProofGap_Lean/README.md) for build instructions.
