# SIMD regression fixtures

`Common/` holds the production-shaped Add/Subtract algorithms, scalar dispatch and
lookup table (a copy of production `UInt256.Lookups.cs` with the `WRONG_TABLE`
mutation), shared with the Reporting group. `Cases.props` registers each case and its
compiler symbol. Run `dotnet run --file verification/SimdRegression.cs -- --group SIMD`
(`--method`, `--profile` and `--case` narrow the run). The runner exits nonzero
while any case is PENDING.

Applicability per profile is the original suite's (`Positive`/`Negative` in the
runner). Each positive must change its targeted extracted program (Renamed: method
names only, identical bodies) and pass the registered production gate. Each negative
needs a kernel-checked refutation of `WrappingBinaryContract` from the concrete
byte witness in `witnesses.json` (`CheckedRefutationTemplate.lean.in`, via
`checked_binary_byte_refuted`): left input at 0, right at 64, output at the witness
base, and the actual byte the mutation stores. The unchanged production proof must
then fail in proof checking without leaving a certificate.

A case is PENDING when its method and profile have no production gate yet (among the
SIMD profiles only arm64-advsimd Add is gated; x64-sse42 and the AVX profiles are
being proved separately), or when a positive changes a method body: production gates bind
exact method bodies by `rfl`, so LaneLocals, InlineCarry, ExtractedHelper,
ReversedStore and FeatureExpressions need their own fixture proofs
(`<Method>_<profile>_<Case>.lean` in this directory) before they can count.

The template currently hard-codes an empty static descriptor list, so witnesses for
profiles that read the lookup table (AVX) need the static-world step generalised
(as `Safety/WitnessTemplate.lean.in` does) before they can run.

Every case is a consumer contract or proof property, so every case is ported as
`SIMD/<Method>/<profile>/<Case>`; none is delegated to LeanCIL.

| Original case | Kind | Applicable profiles | Status at LeanCIL 7aec18e |
| --- | --- | --- | --- |
| Baseline | positive, production control | all six | PASS Add/arm64-advsimd; PENDING elsewhere (no gate) |
| Renamed | positive, helper identities only | all six | PASS Add/arm64-advsimd; PENDING elsewhere (no gate) |
| EquivalentMask | positive, body change | x64-avx2, x64-avx2-bmi1 | PENDING (no gate; needs fixture proof) |
| LaneLocals | positive, body change | arm64-advsimd, x64-sse42 | PENDING (needs fixture proof; no gate except Add/arm64-advsimd) |
| InlineCarry | positive, body change | Add x64-sse42; Subtract arm64-advsimd, x64-sse42 | PENDING (no gate) |
| ExtractedHelper | positive, body change | all six | PENDING (needs fixture proof) |
| ReversedStore | positive, body change | arm64-advsimd, x64-sse42 | PENDING (needs fixture proof) |
| FeatureExpressions | positive, body change | all six | PENDING (needs fixture proof) |
| WrongAlignment | negative, 128-bit lane alignment | arm64-advsimd, x64-sse42 | PASS Add/arm64-advsimd; PENDING elsewhere (no gate) |
| WrongTop | negative, top-limb propagation | arm64-advsimd; Subtract x64-sse42 | PASS Add/arm64-advsimd; PENDING elsewhere (no gate) |
| WrongAvxAlignment | negative, 256-bit alignment | x64-avx512, x64-avx512-bmi1 | PENDING (no gate) |
| WrongBlend | negative, AVX2 blend mask | x64-avx2, x64-avx2-bmi1 | PENDING (no gate) |
| WrongTernary | negative, AVX-512 ternary immediate | x64-avx512, x64-avx512-bmi1 | PENDING (no gate) |
| WrongPredicate | negative, propagation predicate | AVX2 and AVX-512 | PENDING (no gate) |
| WrongTable | negative, lookup table entry | AVX2 and AVX-512 | PENDING (no gate; static-world step) |
| WrongScale | negative, table index scaling | AVX2 and AVX-512 | PENDING (no gate) |
| EarlyReread | negative, reread after partially overlapping store | AVX2 and AVX-512 | PENDING (no gate) |

Each PASS negative also required the unchanged production proof to fail in proof
checking with no certificate left behind.
