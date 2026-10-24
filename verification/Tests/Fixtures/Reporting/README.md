# Reporting regression fixtures

These fixtures expose the public `AddOverflow` and `SubtractUnderflow` signatures
over the versioned SIMD algorithms in `../SIMD/Common/`. `Cases.props` registers each
case and its compiler symbol. Run them with
`dotnet run --file verification/SimdRegression.cs -- --group Reporting`
(`--method`, `--profile` and `--case` narrow the run).

Each positive must change its targeted extracted program (Renamed: method names
only, identical bodies) and pass the registered production gate (EquivalentMask: its fixture proof). Each negative needs
a kernel-checked refutation of `ReportingBinaryContract` from a concrete witness in
`../SIMD/witnesses.json`: `WrongFlag` returns the wrong flag for zero operands
(`checked_reporting_flag_refuted`), the others store a wrong result byte
(`checked_reporting_byte_refuted`). The unchanged production proof must then fail in
proof checking without leaving a certificate.

`WrongFlag` negates only the scalar (`AddScalar`/`SubtractImpl`) return, so it is
reachable on scalar and arm64-advsimd. The original fixture also covered the AVX
paths; those wait for their gates.

A case is PENDING when its method and profile have no production gate, or when the
positive changes a method body without its own fixture proof: production gates bind
exact method bodies by `rfl`. EquivalentMask (`<Method>_<profile>_EquivalentMask.lean`
in this directory) is the one positive refactor fixture kept for this family; the
original ExtractedHelper and ReversedStore positives were dropped.

Every case is a consumer contract property and is ported as
`Reporting/<Method>/<profile>/<Case>`. Applicability is the original suite's: the
SIMD table's profiles plus scalar for Baseline, Renamed and WrongFlag.

| Case | Kind |
| --- | --- |
| Baseline | positive, production control |
| Renamed | positive, helper identities only |
| EquivalentMask | positive, body change (AVX2) |
| WrongFlag | negative, flag negated, result kept |
| WrongAlignment | negative, lane alignment (ARM, SSE) |
| WrongTop | negative, top-lane propagation (ARM; Subtract SSE) |
| EarlyReread | negative, reread after overlapping store (AVX) |
