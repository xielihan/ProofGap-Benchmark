# Language documentation

These references explain how to read the NFL proof gaps and write candidate
DSL proofs for ProofGap-Benchmark, based on Demidovich's mathematical analysis
exercises (吉米多维奇《数学分析习题集》).

| Document | Contents |
| --- | --- |
| [NFL syntax](NFL_syntax.md) | Gap format, term grammar, quantifiers, functions, calculus notation, and mathematical symbols |
| [DSL proof guide](DSL_guide.md) | A complete example, proof-state conventions, command syntax, and command semantics |

Read the NFL reference to understand a gap, then use the DSL guide to construct
a proof. Run candidates using the [NFL verifier](../ProofGap_nfl/README.md).
Named theorems must match the [allowed theorem library](../ProofGap_nfl/thm/all_lib_idx.md).
The separate [Lean workspace guide](../ProofGap_Lean/README.md) covers Lean proofs.
