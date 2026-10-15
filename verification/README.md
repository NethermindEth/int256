# UInt256 verification with LeanCIL

This migration starts from `verification/uint256-memory-safety`
(`6c56716afa7860771c08815b8348e53313c7f8c8`), based on int256 `main`
(`5fa8d77429c0440754bbfc851788d1ae37aba07f`). It consumes LeanCIL at
`01c51cddc749f73e651f46844be252b68f8193e1` through a pinned Lake dependency.
CIL semantics, extraction, and verification infrastructure belong to LeanCIL;
this directory contains only UInt256 specifications and proofs.

## Verification scope

The 41 registered scalar gates in `manifests/gates.json` cover `Add`, `AddOverflow`,
reference equality and ordering, `Equals(in UInt256)`, `CompareTo(in UInt256)`,
and 31 comparisons between UInt256 and primitive integers.
The `Add` gate includes its four reachable helpers. `proofs/AddScalar.lean` proves the allocation-aware
`WrappingBinaryContract`: finite checked execution, addition modulo 2^256 of
the initial operands, writable output, and preservation of caller bytes outside
the output. Valid overlap between inputs and output is allowed.
`AddOverflow` additionally proves the exact unsigned carry flag. The comparison
gates prove results from the initial operands, finite checked return, and
preservation of caller memory.

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
assembly certificate. `Verify` rebuilds consumer proofs and imports from source in a
clean package, reuses a source-bound kernel-checked LeanCIL library, replays the
consumer modules in the kernel, audits axioms, and records the assembly,
extraction and proof identities in `artifacts/Add/scalar/verified.json`.
Generated artifacts are ignored. CI runs all registered gates on main and on
manual dispatch. On PRs, `SelectGates.ps1` walks each proof's local import graph
and selects gates affected by changed Lean sources. Production C# and shared
build/verification configuration changes select all gates. Documentation, test-only and benchmark-only
changes skip the expensive jobs; the stable `Verify UInt256` check still runs
and requires every selected check to pass. CI builds and kernel-checks the shared
LeanCIL library once per run; certificate jobs validate the producer's manifest
digest before reusing it. Consumer proof checks remain separate for every gate.
Up to eight certificate jobs run concurrently. The registry initially orders
gates by local certificate duration, longest first; those measurements were
taken under concurrent load and can be refined using CI timings.
Each certificate job publishes stage timings in its summary and retains the
underlying command transcripts. Extraction-independent consumer modules are
still rebuilt per gate; [LeanCIL #42](https://github.com/NethermindEth/LeanCIL/issues/42)
tracks certified reuse of that common UInt256 library.

Local validation passed all 41 fresh certificates against the pinned revision,
checked their 391 recorded consumer-source hashes, and passed the audit of 409
supporting theorems. As a negative check, replacing the first `add` in the
compiled `AddWithCarry` helper with `sub` made the unchanged proof build fail
in `CarryMemory`; no certificate was emitted. This is a rejection check, not
the original branch's full mutation/refutation suite.

The runner resolves defaults from `manifests/gates.json`. Unregistered
method/profile combinations require
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

`manifests/migration-status.json` records the extraction inventory and its tested
LeanCIL revision separately
from completed gates. Of 87 scalar targets, 74 extract and 13 are blocked:

- [LeanCIL #36](https://github.com/NethermindEth/LeanCIL/issues/36): the seven
  multiplication entries need checked `Math.BigMul` support.
- [LeanCIL #37](https://github.com/NethermindEth/LeanCIL/issues/37): the six shift
  entries need unmanaged aggregate byref operations. Vector byref paths also
  need this support.
- [LeanCIL #38](https://github.com/NethermindEth/LeanCIL/issues/38): SIMD arithmetic,
  bitwise and equality paths need aggregate/vector value bitcasts.
- [LeanCIL #39](https://github.com/NethermindEth/LeanCIL/issues/39): scalar
  subtraction and underflow-reporting consumer proofs compile, but the full certificate command
  exceeds the heartbeat budget while checking generated translation evidence. They are recorded under
  `pendingGates`, not registered as completed CI gates.

- [LeanCIL #40](https://github.com/NethermindEth/LeanCIL/issues/40): constructor-based
  primitive equality and bitwise ports need reusable checked unmanaged-aggregate
  setup, private-local store and by-value parameter-home contents lemmas. This affects 31 scalar targets.

The 46 scalar targets waiting on upstream work are listed individually in
`blockedGates` in the migration report. Two of these already have completed
consumer proof ports (`Subtract` and `SubtractUnderflow`), bringing the ported
total to 43, but remain outside the certified CI registry because of #39.
The extraction failures have standalone reproductions upstream. Extraction
success is not proof completion. Remaining migration work covers the blocked
operations and feature profiles. Each
public gate must retain independent arithmetic and safety contracts, including
initial operands under valid overlap, normal finite return, caller-byte
preservation, and its claimed feature coverage. Re-run the original
mutation/refutation cases before claiming equivalent verification scope.
Further extraction or proof-composition gaps should be reproduced upstream
rather than hidden behind consumer copies of CIL infrastructure.
