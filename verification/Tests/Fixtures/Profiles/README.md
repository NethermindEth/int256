# Profile regression fixtures

The original Profiles group (`verification/uint256-memory-safety`) checked how the
extractor classifies feature getters, guards intrinsics per execution profile, and
rejects unsupported metadata. Every case tests extraction infrastructure rather than
a UInt256 contract or proof, so on the LeanCIL route the behaviour belongs to LeanCIL
and no runner certifies it here. Each case is mapped below to the LeanCIL test that
covers it at the pinned revision, or to an unfiled issue draft under
`verification/artifacts/upstream-fixture-gaps/` (gitignored).

The original sources are kept here. To re-probe a case, build with
`dotnet build verification/Tests/Fixtures/Profiles/Nethermind.Int256.csproj -c Release -p:FixtureName=<case>`
(with separate output paths) and run the pinned extractor on the public `Add`
signature from `manifests/targets.json` for each profile. At LeanCIL 7aec18e every
case was probed on scalar, x64-avx2 and x64-avx512 (`repro/observed-7aec18e.txt`,
`repro/observed-original-profiles-7aec18e.txt`); all intended rejections and
acceptances still hold. ARM and SSE profiles were not probed. "Gap" means only that no upstream
test pins the behaviour.

| Original case | Original expectation | Observed at the pin | Upstream coverage |
| --- | --- | --- | --- |
| KnownFeature | `Avx2.IsSupported` kept as a typed feature; reachability follows each profile | extracts | `Tests/Loops.cs:122-129`, `Tests/FeatureEvidence.cs` |
| UnknownFeature | `Bmi2.IsSupported` rejected: unclassified getter | `Unclassified feature getter` | gap: `01-feature-guard-tests.md` |
| UnclassifiedFeature | `Sse2.IsSupported` rejected as a new query | extracts: `Sse2` is now a classified feature | not applicable: the query is supported by design |
| PortableVector | portable `Vector256` arithmetic accepted on every profile | extracts | gap: `01-feature-guard-tests.md` |
| UnguardedAvx512 | rejected unless the profile is AVX-512 | rejected on scalar and x64-avx2, extracts on x64-avx512 | gap: `01-feature-guard-tests.md` (`Tests/Semantics.lean:26-46` is interpreter-only) |
| WeakAvx512Guard | AVX-512 under `Avx2.IsSupported` rejected on AVX2 profiles | rejected on x64-avx2, extracts on scalar (dead branch) and x64-avx512 | gap: `01-feature-guard-tests.md` |
| MergedAvx512Guard | guard merged with data rejected unless AVX-512 | rejected on scalar and x64-avx2, extracts on x64-avx512 | partial: `Tests/FeatureEvidence.lean:42-59`; gap: `01-feature-guard-tests.md` |
| GuardedAvx512 | cached and negated guards accepted; AVX-512 path live only on AVX-512 | extracts | partial: `Tests/FeatureEvidence.lean:42-59`; gap: `01-feature-guard-tests.md` |
| InheritedAvx2Guard | AVX2 intrinsic under an AVX-512 guard accepted | extracts | gap: `01-feature-guard-tests.md` |
| UnsupportedIntrinsic | unmapped intrinsic rejected | `External or mismatched managed dependency` | partial: `Tests/RuntimeBits.cs:111-143`; gap: `02-unsupported-metadata-tests.md` |
| UnsupportedUnsafe | unmapped unsafe call rejected | `External or mismatched managed dependency` (from `Vector256<int>.get_Zero`; the `Unsafe.As` cast itself is supported) | gap: `02-unsupported-metadata-tests.md` |
| StaticInitializer | helper type with a static constructor rejected | `Unsupported method metadata or static initialisation` | `Tests/InitializedTypes.cs:23,28` |
| GenericHelper | method on a generic declaring type rejected | `External or mismatched managed dependency` | gap: `02-unsupported-metadata-tests.md` |
| StaticData | RVA bytes bound into the program; changing a byte changes the program | extracts | `Tests/StaticSpans.cs:22-40` (tampered blob changes the theorem) |

The original harness also mutated metadata (feature, intrinsic and static-field
scopes, generic arguments, `UInt256` layout, mutable or initialised statics, unknown
profile names). LeanCIL tests the same class of rejection per API: scope and version
mutations in `Tests/RuntimeBits.cs:111`, `Tests/UnsafeReferences.cs:57`,
`Tests/UnsafeLayouts.cs:87`, `Tests/SkipInitialization.cs:46` and
`Tests/StaticSpans.cs:44-77`; field layout, static initializer and RVA data
mutations in `scripts/Test.cs:229-254` (driving `Tests/MetadataMutator.cs`).
These were not re-derived case by case.
