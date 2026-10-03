# Reporting fixtures

These fixtures reuse the versioned SIMD algorithms and expose the exact public
`AddOverflow` and `SubtractUnderflow` signatures. `Public.cs` is the shared source
anchor; `Cases.props` explicitly registers each case. Unknown cases fail before
compilation. The selected symbol is set before compiler input caching.

The positive cases rename helpers, use equivalent comparison masks, extract
helpers, or reverse storage arguments. A case counts only when its intended
reachable CIL changes and the complete verifier checks identical handwritten
proofs. EquivalentMask applies to AVX2; ReversedStore applies to ARM and SSE.

WrongFlag preserves the arithmetic result and flips the returned Boolean. The
other negatives change lane alignment, top-lane propagation, or overlapping
memory reads. Each applicable negative needs a separate kernel proof refuting
the full arithmetic, flag, and memory contract for every successful fuel before
its public proof rejection is classified. Resource exhaustion is inconclusive.

Run `python verification/Tests/reporting_checks.py` with the pinned Lean tools on
PATH. `--method`, `--profile`, and `--case` select a smaller run. The runner uses a
source snapshot, establishes fresh production and fixture baselines, checks
artifact provenance and proof hashes, and requires rejected cases to invalidate
their reports.
