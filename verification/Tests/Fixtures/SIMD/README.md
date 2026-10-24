# SIMD regression fixtures

`Common/` holds the production-shaped Add/Subtract algorithms, scalar dispatch and
lookup table (a copy of production `UInt256.Lookups.cs` with the `WRONG_TABLE`
mutation), shared with the Reporting group. `Cases.props` registers each case and its
compiler symbol. Run `dotnet run --file verification/SimdRegression.cs -- --group SIMD`
(`--method`, `--profile` and `--case` narrow the run). The runner exits nonzero
while any case is PENDING.

Applicability per profile is the original suite's (`Positive`/`Negative` in the
runner). Each positive must change its targeted extracted program (Renamed: method
names only, identical bodies) and pass the registered production gate (EquivalentMask: its fixture proof). Each negative
needs a kernel-checked refutation of `WrappingBinaryContract` from the concrete
byte witness in `witnesses.json` (`CheckedRefutationTemplate.lean.in`, via
`checked_binary_byte_refuted`): left input at 0, right at 64, output at the witness
base, and the actual byte the mutation stores. The unchanged production proof must
then fail in proof checking without leaving a certificate.

A case is PENDING when its method and profile have no production gate, or when a
positive changes a method body without its own fixture proof: production gates bind
exact method bodies by `rfl`, so a body-changing refactor needs
`<Method>_<profile>_<Case>.lean` in this directory. EquivalentMask is the one
positive refactor fixture kept for this family; the other original body-changing
positives (LaneLocals, InlineCarry, ExtractedHelper, ReversedStore,
FeatureExpressions) were dropped. Per-runner results are in
`manifests/migration-status.json`.

Every case is a consumer contract or proof property, so every case is ported as
`SIMD/<Method>/<profile>/<Case>`; none is delegated to LeanCIL.

| Case | Kind | Applicable profiles |
| --- | --- | --- |
| Baseline | positive, production control | all four |
| Renamed | positive, helper identities only | all four |
| EquivalentMask | positive, body change | x64-v3 |
| WrongAlignment | negative, 128-bit lane alignment | arm64-advsimd, x64-sse42 |
| WrongTop | negative, top-limb propagation | arm64-advsimd; Subtract x64-sse42 |
| WrongAvxAlignment | negative, 256-bit alignment | x64-v4 |
| WrongBlend | negative, AVX2 blend mask | x64-v3 |
| WrongTernary | negative, AVX-512 ternary immediate | x64-v4 |
| WrongPredicate | negative, propagation predicate | AVX2 and AVX-512 |
| WrongTable | negative, lookup table entry | AVX2 and AVX-512 |
| WrongScale | negative, table index scaling | AVX2 and AVX-512 |
| EarlyReread | negative, reread after partially overlapping store | AVX2 and AVX-512 |

Each negative also requires the unchanged production proof to fail in proof
checking with no certificate left behind.
