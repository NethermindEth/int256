# SIMD regression fixtures

`Common/` contains the production-shaped Add/Subtract algorithms, input snapshots, scalar dispatch and lookup table. `Cases.props` registers each case, compiler symbol and test suite for both MSBuild and Python. Unknown cases fail before compilation; reports identify the registry and selected case.

Run `python verification/Tests/simd_checks.py`. The default checks both methods and all six SIMD profiles, including BMI variants. `--method`, `--profile`, `--case` and `--suite positive|negative` narrow the run. Inapplicable explicit cases fail rather than appearing to pass.

| Positive case | Checked change | Applicable profiles |
| --- | --- | --- |
| Baseline | Production-shaped control | All |
| Renamed | Discovered private helper identities | All |
| EquivalentMask | Equivalent AVX2 blend/AND incoming-lane mask | AVX2, with/without BMI |
| LaneLocals | Reordered initial vector loads | ARM, SSE |
| InlineCarry | Expanded scalar carry/borrow operations in the vector fallback | Add SSE; Subtract ARM/SSE |
| ExtractedHelper | Extracted alignment, propagation or cascade helper | All |
| ReversedStore | Rejected optional storage summary followed by successful raw execution | ARM, SSE |

Each applicable positive must change its targeted reachable CIL and pass the complete public verifier with identical handwritten proof hashes. Renaming must remove the old private identities. Source-only changes are not counted as regressions.

Semantic negatives cover incorrect 128/256-bit alignment, AVX2 blend masks, AVX512 ternary immediates, propagation predicates, table entries, table index scaling, top-limb/cross-half propagation and rereading inputs after a partially overlapping store. The runner first verifies production in its source snapshot, extracts the incorrect fixture, confirms its targeted change, and kernel-checks a concrete refutation of the unchanged full public contract using execution uniqueness. It then requires failure in the public execution proof and invalidation of the success report. Missing tools, extraction failures and resource exhaustion are inconclusive and fail the test.

The witness byte map is shared by both inputs and output: left starts at 0, right at 64; `EarlyReread` writes at 8, partially overlapping the left input. Other outputs start at 64 or 128, covering an output equal to the right input and disjoint output. `simd_checks.witness` exposes the four input words and the actual distinguishing byte for native sampling. Native sampling must record actual supported features and skip unavailable profiles explicitly; it supplements the kernel proofs.
