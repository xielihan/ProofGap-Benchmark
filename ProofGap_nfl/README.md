# ProofGap_nfl

This dataset contains 25,987 NFL proof-gap statements from 2,947 exercises.
The base snapshot was printed from the same proof-gap ASTs used by the backend
Lean printer. Each item is stored as `exercise_<id>/gap_<gap_id>/gap.txt`.
For 9,385 gaps, a sibling `dsl.txt` contains a reference answer; the remaining
16,602 gaps have no packaged answer.

The base gap and answer files come from `ex_gap_25987_gap_dsl_20260910.zip`.
On 2026-09-24, the 13 previously failing gap/DSL pairs were replaced with the
corresponding pairs from `ProofGap_83_Linux_PASS_gap_dsl_with_logs_20260924.zip`,
copied byte-for-byte. Eight gap statements have content changes; the other five
gap files only gain a final newline. Other gap/answer files retain their base
archive contents. The changed statements may differ from the unchanged
backend Lean snapshot.

On 2026-09-24, all 9,385 current packaged DSL answers passed with the macOS
arm64 verifier and supplied theorem library, with zero failures. All 9,372
previously passing answers remained unchanged and passed again. These results
apply to the updated gap statements.

Use `gap.txt` as model input and reserve `dsl.txt` for reference or evaluation.

## Check a packaged answer

From this directory, run:

```sh
python3 check.py exercise_2/gap_1/gap.txt exercise_2/gap_1/dsl.txt
```

## Packaged tools

- `check.py`: Python 3.9+ entry point for one gap and one candidate DSL proof.
- `settings.ini`: verifier settings, including the theorem-library path.
- `thm/all_lib_idx.md`: the supplied `all_lib_idx(1).md`, copied byte-for-byte.
- `bin/test_dsl`: Linux x86-64 verifier (glibc 2.34 or newer).
- `bin/test_dsl_windows.exe`: Windows x86-64 verifier.
- `bin/test_dsl_macos_arm64`: macOS arm64 verifier (macOS 15 or newer).

The Linux and Windows binaries come from the supplied AAAI artifact. The
macOS binary was built from the current proofgrader source in an isolated
build directory and depends only on the macOS system library.

The macOS binary identifies local binders from declaration positions, preserves
free bounds and limit parameters, and avoids capturing free variables during
instantiation, including compound substitution values. It does not use the
historical empty-result fallback in `get_binders`. The supplied Linux and Windows binaries
have not been rebuilt with this fix. To use the fix on those platforms, build
`test_dsl` from the updated proofgrader source and select it with `--binary`.

## Check a generated proof

From this directory, run:

```sh
python3 check.py exercise_2/gap_1/gap.txt /path/to/candidate.dsl
```

On Windows, use `py` instead of `python3` if that is your Python launcher:

```powershell
py check.py exercise_2/gap_1/gap.txt C:/path/to/candidate.dsl
```

Input paths are interpreted relative to your current working directory. The
script locates the binary, settings, and theorem library relative to itself,
so it can also be invoked from another directory. It selects a native binary
automatically; `--binary /path/to/test_dsl` selects a compatible custom build.

Use a different time limit or a new output directory when needed:

```sh
python3 check.py exercise_2/gap_1/gap.txt /path/to/candidate.dsl --timeout 180 --output-dir verify/my-run
```

The default timeout is 120 seconds. By default each run creates a unique
`verify/run-.../` directory. An explicit output directory must not already
exist, so earlier results cannot be mistaken for a fresh run.

## Settings and results

The template `settings.ini` uses `ROOT_PATH = .` and loads only
`thm/all_lib_idx.md`. The key `THMEOREM_LIB_SET` intentionally preserves the
spelling expected by `test_dsl`. When invoking the binary directly with
`-c settings.ini`, run from this directory and create `verify/` first for its
configured log paths.

`check.py` creates a separate settings file per run with resolved library
and log paths, invokes `test_dsl --result-json`, and checks the result. It
normalizes BOMs, blank lines, and line endings in a temporary copy of the gap;
the original file is preserved. Each output directory contains:

- `result.json`: the verifier's structured result, when produced.
- `summary.json`: acceptance status, timing, input and component hashes.
- `stdout.txt`, `stderr.txt`, `error_log.md`, and `execute_log.md`.
- `settings.ini` and `gap.normalized.txt` for replaying the invocation.

A proof passes only when the verifier exits with code 0, emits schema
`test_dsl_structured_v2`, reports `final_status = finish`, sets both
`proof_finished` and `proof_verified` to true, reports zero admits and zero
split gaps, and prints `dsl proof finished`. A process exit code alone is
insufficient.

The checker returns 0 for an accepted proof, 1 for rejection or timeout, and
2 for a setup or process-launch error. Run outputs are excluded from Git.

The updated macOS verifier was checked against all packaged DSL answers and
targeted semantic regressions for shadowing, tuple binders, nested scopes,
free parameters, alpha-equivalence, and capture avoidance.
The checker entry point was
previously tested for admit rejection, malformed DSL rejection, and timeout
handling. Linux and Windows binaries were inspected but were not executed on
the macOS host. See the [benchmark overview](../README.md) for the dataset sources.
