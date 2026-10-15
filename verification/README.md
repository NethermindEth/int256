# UInt256 verification with LeanCIL

This migration starts from `verification/uint256-memory-safety`
(`6c56716afa7860771c08815b8348e53313c7f8c8`), based on int256 `main`
(`5fa8d77429c0440754bbfc851788d1ae37aba07f`). It consumes LeanCIL at
`3e198554cf3b6af4a24f2804a4ae74886fd41ae2` through a pinned Lake dependency.
CIL semantics, extraction, and verification infrastructure belong to LeanCIL;
this directory contains only UInt256 specifications and proofs.

## Verification scope

The registered compiled-method gate is **scalar `UInt256.Add`**, including its
four reachable helpers. `proofs/AddScalar.lean` proves the allocation-aware
`WrappingBinaryContract`: finite checked execution, addition modulo 2^256 of
the initial operands, writable output, and preservation of caller bytes outside
the output. Valid overlap between inputs and output is allowed.

The theorem applies to LeanCIL's scalar feature profile and a successfully
initialized `Nethermind.Int256.UInt256` type. It does not prove the static
constructor or SIMD paths. The 87 signatures in `manifests/targets.json` are a
migration inventory, not 87 completed certificates. Other arithmetic and
profile-transport lemmas remain supporting results; a transported, assumed
certificate is not a proof of a compiled implementation.

## Run

Install .NET SDK 10.0.402 or a compatible newer SDK, PowerShell 7, Git, and elan.
Lake selects Lean 4.35.0 using `lean-toolchain`.

From the repository root:

```powershell
# Build and audit the extraction-independent supporting library.
pwsh -NoProfile -File verification/Verify.ps1 -Action Contracts

# Build the production assembly, extract scalar Add, and certify it.
pwsh -NoProfile -File verification/Verify.ps1 -Action Verify -Method Add -Profile scalar

# Extract without claiming a certificate.
pwsh -NoProfile -File verification/Verify.ps1 -Action Extract -Method Add -Profile scalar
```

`Contracts` audits theorems in the `UInt256Model` and `UInt256Proof` namespaces,
allowing only `propext`, `Classical.choice`, and `Quot.sound`. It produces no
assembly certificate. `Verify` rebuilds the proof and imports from source in a
clean package, replays the kernel, audits axioms, and records the assembly,
extraction and proof identities in `artifacts/Add/scalar/verified.json`.
Generated artifacts are ignored. The CI workflow runs both checks.

Local validation passed the fresh scalar certificate and the audit of 409
supporting theorems. As a negative check, replacing the first `add` in the
compiled `AddWithCarry` helper with `sub` made the unchanged proof build fail
in `CarryMemory`; no certificate was emitted. This is a rejection check, not
the original branch's full mutation/refutation suite.

Scalar Add defaults to `proofs/AddScalar.lean` and
`UInt256Proof.Add.scalar_correctness`. Other method/profile combinations require
both `-Proof` and `-Theorem`; proof paths are relative to `verification/` and
must be sources inside this package, outside build/artifact directories. Each
gate must be reviewed to ensure its selected theorem states the full contract.

## Upstream status and remaining work

The pinned revision contains the fixes for
[initialization assumptions (#25)](https://github.com/NethermindEth/LeanCIL/issues/25),
[consumer proof packages (#26)](https://github.com/NethermindEth/LeanCIL/issues/26),
and [`Unsafe.SkipInit<T>` (#34)](https://github.com/NethermindEth/LeanCIL/issues/34).
Scalar Add now extracts its real `StoreLimbs` helper without changing production
code. SkipInit preserves memory; the proof establishes initialization through
the subsequent writes.

The scalar execution proofs were ported from the original branch to fresh
extraction, including byte-offset field operations, parameter-home setup and
Boolean return normalization. No generated CIL, custom extractor, or CIL
semantics were copied into this package.

Remaining migration work covers other operations and feature profiles. Each
public gate must retain independent arithmetic and safety contracts, including
initial operands under valid overlap, normal finite return, caller-byte
preservation, and its claimed feature coverage. Re-run the original
mutation/refutation cases before claiming equivalent verification scope.
Further extraction or proof-composition gaps should be reproduced upstream
rather than hidden behind consumer copies of CIL infrastructure.
