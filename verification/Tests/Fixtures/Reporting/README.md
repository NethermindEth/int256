# Reporting regression fixtures

These fixtures expose the public `AddOverflow` and `SubtractUnderflow` signatures
over the versioned SIMD algorithms in `../SIMD/Common/`. `Cases.props` registers each
case and its compiler symbol. Run them with
`dotnet run --file verification/SimdRegression.cs -- --group Reporting`
(`--method`, `--profile` and `--case` narrow the run).

Each positive must change its targeted extracted program (Renamed: method names
only, identical bodies) and pass the registered production gate. Each negative needs
a kernel-checked refutation of `ReportingBinaryContract` from a concrete witness in
`../SIMD/witnesses.json`: `WrongFlag` returns the wrong flag for zero operands
(`checked_reporting_flag_refuted`), the others store a wrong result byte
(`checked_reporting_byte_refuted`). The unchanged production proof must then fail in
proof checking without leaving a certificate.

`WrongFlag` negates only the scalar (`AddScalar`/`SubtractImpl`) return, so it is
reachable on scalar and arm64-advsimd. The original fixture also covered the AVX
paths; those wait for their gates.

A case is PENDING when its method and profile have no production gate, or when the
positive changes a method body: production gates bind exact method bodies by `rfl`,
so such refactors need their own fixture proof.

Every case is a consumer contract property and is ported as
`Reporting/<Method>/<profile>/<Case>`. Applicability is the original suite's: the
SIMD table's profiles plus scalar for Baseline, Renamed and WrongFlag. As in the
original, ExtractedHelper is not run on scalar, where the extracted helper sits on
an unreachable vector path and the program would not change.

| Original case | Kind | Status at LeanCIL 7aec18e |
| --- | --- | --- |
| Baseline | positive, production control | PASS AddOverflow and SubtractUnderflow on scalar, AddOverflow on arm64-advsimd; PENDING elsewhere (no gate) |
| Renamed | positive, helper identities only | PASS AddOverflow and SubtractUnderflow on scalar, AddOverflow on arm64-advsimd; PENDING elsewhere (no gate) |
| EquivalentMask | positive, body change (AVX2) | PENDING (no gate; needs fixture proof) |
| ExtractedHelper | positive, body change | PENDING (needs fixture proof) |
| ReversedStore | positive, body change (ARM, SSE) | PENDING (needs fixture proof) |
| WrongFlag | negative, flag negated, result kept | PASS AddOverflow and SubtractUnderflow on scalar, AddOverflow on arm64-advsimd; PENDING elsewhere (no gate; the AVX return is not mutated yet) |
| WrongAlignment | negative, lane alignment (ARM, SSE) | PASS AddOverflow/arm64-advsimd; PENDING elsewhere (no gate) |
| WrongTop | negative, top-lane propagation (ARM; Subtract SSE) | PASS AddOverflow/arm64-advsimd; PENDING elsewhere (no gate) |
| EarlyReread | negative, reread after overlapping store (AVX) | PENDING (no gate) |
