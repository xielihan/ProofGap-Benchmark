# ProofGap_nfl

NFL proof-completion tasks based on Demidovich's mathematical analysis
exercises (吉米多维奇《数学分析习题集》).
The dataset contains **25,987 gaps from 2,947 exercises**, with **9,385 DSL
reference proofs** and a bundled verifier.

NFL (Natural Formal Language) expresses each proof obligation as assumptions
and a target. The NFL and backend Lean printers use a common proof-gap AST
representation; coverage and some statements differ between the datasets.

NFL and Lean have different logical foundations, so not every NFL gap can
be printed directly as Lean by the backend. For gaps outside direct backend
coverage, Codex conversion with semantic review and correction provides the
[LLM Lean variant](../ProofGap_Lean/ProofGap_lean_llm/).

Read the [NFL syntax reference](../document/NFL_syntax.md) for mathematical
notation and the [DSL proof guide](../document/DSL_guide.md) for writing
candidate answers.

## Data format

```text
exercise_<id>/gap_<gap_id>/
├── gap.txt    # Proof obligation
└── dsl.txt    # Reference proof, present for 9,385 gaps
```

A gap uses the following fields:

| Field | Meaning |
| --- | --- |
| `PROOF GAP` | Gap identifier within the exercise |
| `ASSUM` | Available assumptions, which may be empty |
| `GOAL` | Statement to prove |
| `METHOD` | Method field in the NFL gap format |

Use the complete `gap.txt` as the proof obligation and the bundled theorem
library as the allowed library. Keep `dsl.txt` out of model inputs.
The 16,602 gaps without reference answers use the same verification interface.

## Requirements

Python **3.9+** is required. The checker selects a packaged binary for these
platforms:

| Platform | Binary | System requirement |
| --- | --- | --- |
| macOS arm64 | `bin/test_dsl_macos_arm64` | macOS 15 or newer |
| Linux x86-64 | `bin/test_dsl` | glibc 2.34 or newer |
| Windows x86-64 | `bin/test_dsl_windows.exe` | 64-bit Windows |

For another platform or verifier build, supply a compatible executable with
`--binary /path/to/test_dsl`. Platform binaries differ in their handling of
bound variables; the validation results below apply to the macOS arm64 build.

## Run the verifier

All examples here run from `ProofGap_nfl/`.

Check a reference answer:

```sh
python3 check.py exercise_2/gap_1/gap.txt exercise_2/gap_1/dsl.txt
```

Check a generated proof:

```sh
python3 check.py exercise_2/gap_1/gap.txt /path/to/candidate.dsl
```

On Windows, use `py` instead of `python3` if needed. Input paths are relative
to the current working directory; the verifier and theorem library are
located relative to `check.py`.

| Option | Purpose | Default |
| --- | --- | --- |
| `--timeout` | Time limit in seconds | `120` |
| `--output-dir` | A new directory for this run's results | Unique directory under `verify/` |
| `--binary` | Override the packaged verifier | Native platform binary |

For example:

```sh
python3 check.py exercise_2/gap_1/gap.txt /path/to/candidate.dsl \
  --timeout 180 --output-dir verify/my-run
```

An explicit output directory must not already exist.

## Acceptance and results

`check.py` accepts a proof only if all of the following hold:

- The verifier exits with code `0` and emits schema `test_dsl_structured_v2`.
- `final_status` is `finish`; `proof_finished` and `proof_verified` are true.
- `admit_count` and `split_gap_count` are both zero.
- Standard output contains `dsl proof finished`.

The checker prints `PASS`, `FAIL`, `TIMEOUT`, or `ERROR` with the results
location. Its exit code is `0` for acceptance, `1` for rejection or timeout,
and `2` for a setup or process-launch error.

Each run records:

| Output | Contents |
| --- | --- |
| `summary.json` | Acceptance status, runtime, and input/component hashes |
| `result.json` | Structured verifier result, when available |
| `stdout.txt`, `stderr.txt` | Process output |
| `error_log.md`, `execute_log.md` | Verification logs |
| `settings.ini`, `gap.normalized.txt` | Effective configuration and normalized input |

The checker removes a UTF-8 BOM and blank lines and normalizes line endings
in a temporary copy of the gap. The original input is preserved. Run outputs
are excluded from Git.

## Configuration

`settings.ini` selects the theorem library at `thm/all_lib_idx.md`.
The key `THMEOREM_LIB_SET` preserves the spelling required by the verifier.
The checker creates a separate configuration per run with resolved paths.

To invoke `bin/test_dsl` directly with `-c settings.ini`, run from this
folder and create `verify/` first. Using `check.py` also applies the
acceptance checks above.

## Verification coverage

All **9,385 packaged reference answers** passed the macOS arm64 verifier on
2026-09-24, with zero admits and zero remaining split gaps. The bundled Linux
and Windows binaries are different verifier builds and have not been
validated on their target platforms in this evaluation.

See the [benchmark overview](../README.md) for the task and reporting guidance,
and the [Lean workspace](../ProofGap_Lean/README.md) for Lean verification.
