# ProofGap-Benchmark

**A benchmark for completing individual steps in mathematical proofs.**

ProofGap-Benchmark is built from Demidovich's mathematical analysis exercises
(吉米多维奇《数学分析习题集》). Each **proof gap** specifies a mathematical
claim together with the assumptions available at that step. The task is to
produce a proof that a verifier accepts.

The benchmark provides structured statements in Natural Formal Language
(NFL), Lean statements printed by the backend, and Lean formalizations
converted with Codex, with ongoing review against the NFL statements.

**Paper:** [ProofGap: Benchmarking Step-Level Formal Reasoning with Local Obligations Derived from Natural-Language Solutions](https://arxiv.org/abs/2609.29296).

[Datasets](#datasets) · [Task](#task) · [Quick start](#quick-start) ·
[Evaluation](#evaluation) · [Documentation](#documentation)

## Datasets

| Dataset | Construction | Exercises | Proof gaps | Reference proofs |
| --- | --- | ---: | ---: | --- |
| [ProofGap_nfl](ProofGap_nfl/) | NFL printed from proof-gap ASTs | 2,947 | 25,987 | 9,385 DSL answers |
| [ProofGap_lean](ProofGap_Lean/ProofGap_lean/) | Lean printed from proof-gap ASTs | 1,875 | 15,105 | Proof placeholders |
| [ProofGap_lean_llm](ProofGap_Lean/ProofGap_lean_llm/) | Codex conversion with ongoing semantic review | 1,072 | 10,882 | Proof placeholders |

**NFL and backend Lean use two printers over a common abstract syntax tree
(AST) representation.** However, NFL and Lean have different logical
foundations, so the backend cannot directly print a Lean version of every
NFL proof gap. For gaps outside direct backend coverage, we use Codex to
produce Lean formalizations, followed by semantic review and correction
against the NFL statements. The resulting exercise modules are collected in
**ProofGap_lean_llm**.

The two Lean variants partition the NFL exercise IDs without overlap.
Together, they cover all **2,947 exercises and 25,987 gap IDs** in NFL.
Matching identifiers does not by itself establish semantic equivalence;
some Lean statements differ from their NFL counterparts.
Exercise variants with suffixes, such as `131_1` and `131_2`, are distinct items.

The Lean data incorporates proofgrader updates through `f40b9866a3`
(2026-09-26). The LLM variant contains no proposition `True` tokens, and the
backend now represents subsequence index functions with `StrictMono`.
The latest refresh updates 18 LLM modules, including replacement of 125
string-length targets with mathematical statements. Exercise 4330, gap 5
also restores the two NFL premises needed for that step. Missing assumptions
remain in other statements; see the [known issues](ProofGap_Lean/KNOWN_ISSUES.md)
and [source snapshot](ProofGap_Lean/source_snapshot.json) for review status.

Use **ProofGap_nfl** for DSL proof generation with the bundled verifier,
**ProofGap_lean** for backend-generated Lean proof obligations, and
**ProofGap_lean_llm** for LLM-converted Lean proof obligations.

## Task

A benchmark item consists of an exercise identifier, a gap identifier, the
available assumptions, and a target statement.

| Representation | Model input | Expected output | Verification |
| --- | --- | --- | --- |
| NFL | A gap statement and the allowed theorem library | A DSL proof script | `test_dsl`, through `check.py` |
| Lean | A target theorem and its imports, definitions, and allowed context | A Lean proof of the target | Lean under the pinned environment |

For example, [Exercise 2, gap 1](ProofGap_nfl/exercise_2/gap_1/gap.txt) contains
this NFL goal:

```text
forall (n), n ∈ NonNegIntegerSet ∧ n = 1 ⇒ 1 = frac(n * (n + 1) * (2 * n + 1), 6)
```

The candidate must prove this goal from its stated assumptions. Reference
answers are evaluation material and should be excluded from model inputs.

## Quick start

Clone the repository:

```sh
git clone https://github.com/xielihan/ProofGap-Benchmark.git
cd ProofGap-Benchmark
```

### Check an NFL answer

Requires Python 3.9+ and a compatible platform; see the
[NFL platform requirements](ProofGap_nfl/README.md#requirements).
Run the bundled example from the repository root:

```sh
python3 ProofGap_nfl/check.py \
  ProofGap_nfl/exercise_2/gap_1/gap.txt \
  ProofGap_nfl/exercise_2/gap_1/dsl.txt
```

A successful check prints `PASS` followed by the results directory and returns
exit code `0`. To evaluate a generated proof, replace the last argument with
its path. Each run saves a structured summary and logs under
`ProofGap_nfl/verify/`.

### Check a Lean exercise

With Lean's `elan` toolchain manager installed, enter the shared workspace:

```sh
cd ProofGap_Lean
lake exe cache get

# LLM-converted exercise
lake build +ProofGap_lean_llm.exercise_100

# Backend-printed exercise
lake build +ProofGap_lean.exercise_1000
```

Both datasets use **Lean and Mathlib `v4.29.0-rc6`**, with dependency revisions
locked by the workspace configuration. These commands check the packaged
exercise modules. To evaluate a candidate, replace the selected theorem's
proof while preserving its statement and allowed context.

## Evaluation

- **NFL:** an answer is accepted only when verification finishes successfully,
  the proof is marked verified, and both the admit count and remaining split-gap
  count are zero. `check.py` enforces these conditions; its default timeout is
  120 seconds per proof.
- **Lean:** a candidate must prove the unchanged target under the pinned
  environment. Compilation alone is insufficient: the target proof and its
  dependencies must not rely on `sorry`, `admit`, or newly introduced axioms.
  Both Lean datasets contain proof placeholders. Some LLM-converted
  statements also use simplified or placeholder definitions, so compilation
  does not establish equivalence with the mathematical exercise.
  Apply the [known-issue exclusions](ProofGap_Lean/known_issues.json) and
  report the excluded IDs and resulting evaluation denominator.
- **Reporting:** identify the repository commit, dataset variant, evaluated
  exercise/gap IDs, verification environment, time limit, and number of proof
  attempts. Report accepted proofs against the full evaluated set. If you
  create train/test splits, group related gaps by exercise to limit overlap.

The NFL dataset contains 16,602 gaps without packaged reference answers; those
gaps can still be submitted to the verifier with candidate DSL proofs.
The repository does not prescribe train/validation/test splits.

### Verification coverage

All **9,385 packaged NFL answers** passed the bundled macOS arm64 verifier.
This result does not establish the same pass rate for the other platform
binaries; see the [NFL guide](ProofGap_nfl/README.md#verification-coverage).

The shared Lean environment has been checked with individual exercises from
both variants, including all statements in LLM exercises 3801 and 3802.
A complete Lean dataset build has not been validated. Backend
exercises were selected by successful compilation of their last gap, so
other gaps in an exercise may require statement-level corrections before
proof completion. Keep such corrections separate from proof-generation
results.

For the 2026-09-26 refresh, all exercise/gap IDs were checked against NFL.
Earlier complete-module checks passed for backend exercises 89, 752, and
1009 and LLM exercises 3052 and 3499. All 18 LLM modules in the latest refresh
also passed complete-module checks. The repaired statement for exercise 4330,
gap 5 was proved separately without `sorry` or added axioms; the dataset retains
its proof placeholder. Compilation of other targets does not establish
their statement fidelity or provability.

## Repository layout

```text
ProofGap-Benchmark/
├── document/
│   ├── README.md                 # Language documentation index
│   ├── NFL_syntax.md             # NFL grammar and notation
│   └── DSL_guide.md              # DSL proof commands and examples
├── ProofGap_nfl/
│   ├── exercise_<id>/gap_<id>/
│   │   ├── gap.txt               # Assumptions and target
│   │   └── dsl.txt               # Reference proof, where available
│   ├── check.py                  # NFL verification entry point
│   ├── settings.ini
│   ├── bin/                      # Platform-specific verifiers
│   └── thm/                      # Theorem library
└── ProofGap_Lean/
    ├── lean-toolchain            # Shared Lean version
    ├── lakefile.toml             # Build targets and Mathlib dependency
    ├── lake-manifest.json        # Locked dependency revisions
    ├── ProofGap_lean/
    │   └── exercise_<id>.lean
    └── ProofGap_lean_llm/
        └── exercise_<id>.lean     # LLM-converted statements
```

## Documentation

- [NFL syntax reference](document/NFL_syntax.md)
- [DSL proof guide](document/DSL_guide.md)
- [NFL data format and verifier](ProofGap_nfl/README.md)
- [Shared Lean environment](ProofGap_Lean/README.md)
- [Backend-printed Lean dataset](ProofGap_Lean/ProofGap_lean/README.md)
- [LLM-converted Lean dataset](ProofGap_Lean/ProofGap_lean_llm/README.md)
