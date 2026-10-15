# UInt256 verification with LeanCIL

This migration starts from `verification/uint256-memory-safety`
(`6c56716afa7860771c08815b8348e53313c7f8c8`), based on int256 `main`
(`5fa8d77429c0440754bbfc851788d1ae37aba07f`). It consumes LeanCIL at
`0eba3c565c075a233772786dd3cbe7af6c14797b` through a pinned Lake dependency.
CIL semantics, extraction, and verification infrastructure belong to LeanCIL;
this directory contains only UInt256 specifications and proofs.

## Verification scope

The 43 registered scalar gates in `manifests/gates.json` cover `Add`, `AddOverflow`, `Subtract`, `SubtractUnderflow`,
reference equality and ordering, `Equals(in UInt256)`, `CompareTo(in UInt256)`,
and 31 comparisons between UInt256 and primitive integers.
The `Add` gate includes its four reachable helpers. `proofs/AddScalar.lean` proves the allocation-aware
`WrappingBinaryContract`: finite checked execution, addition modulo 2^256 of
the initial operands, writable output, and preservation of caller bytes outside
the output. Valid overlap between inputs and output is allowed.
`AddOverflow` additionally proves the exact unsigned carry flag. Subtraction
preserves the same wrapping, overlap and caller-memory contracts;
`SubtractUnderflow` proves the exact unsigned borrow flag. The comparison
gates prove results from the initial operands, finite checked return, and
preservation of caller memory.

The theorem applies to LeanCIL's scalar feature profile and a successfully
initialized `Nethermind.Int256.UInt256` type. It does not prove the static
constructor or SIMD paths. The 87 signatures in `manifests/targets.json` are a
migration inventory, not 87 completed certificates. Other arithmetic and
profile-transport lemmas remain supporting results; a transported, assumed
certificate is not a proof of a compiled implementation.

## Run

Install .NET SDK 10.0.402 or a compatible newer SDK, Git, and elan.
Lake selects Lean 4.35.0 using `lean-toolchain`.

From the repository root:

```powershell
# Build and audit the extraction-independent supporting library.
dotnet run --file verification/Verify.cs -- --action contracts

# Build the production assembly, extract scalar Add, and certify it.
dotnet run --file verification/Verify.cs -- --action verify --method Add --profile scalar

# Extract without claiming a certificate.
dotnet run --file verification/Verify.cs -- --action extract --method Add --profile scalar
```

`Contracts` audits theorems in the `UInt256Model` and `UInt256Proof` namespaces,
allowing only `propext`, `Classical.choice`, and `Quot.sound`. It produces no
assembly certificate. `Verify` checks consumer proofs and imports in a clean
package, reuses source-bound certified artifacts where available, kernel-checks
new consumer modules, audits axioms, and records the assembly,
extraction and proof identities in `artifacts/Add/scalar/verified.json`.
Generated artifacts are ignored. CI runs all registered gates on main and on
manual dispatch. On PRs, `SelectGates.cs` walks each proof's local import graph
and selects gates affected by changed Lean sources. Production C# and shared
build/verification configuration changes select all gates. Documentation, test-only and benchmark-only
changes skip the expensive jobs; the stable `Verify UInt256` check still runs
and requires every selected check to pass. CI builds and kernel-checks the shared
LeanCIL library once per run; certificate jobs validate the producer's manifest
digest before reusing it. Consumer proof checks remain separate for every gate.
Gates are divided into at most eight batches per profile, with up to eight
batches running concurrently. Each batch builds
the extractor and production assembly once, then certifies its selected methods
sequentially. LeanCIL authenticates and reuses extraction-independent consumer
modules locally on that runner. Unchanged successful proofs can also be reused;
changed extraction and proof inputs are checked by the upstream verifier. No
consumer cache is distributed between jobs. Every selected method still needs
its own certificate, and any failure fails the batch while allowing the other
methods to report their results.
Each batch publishes stage timings and command transcripts identifying the methods.
The verifier defaults Lean to two worker threads to bound parallel kernel-replay
memory; set `LEAN_NUM_THREADS` explicitly to override this locally. CI uses two threads.
Keep the environment stable within a batch: LeanCIL binds it into cache identities.
For the same scalar subtraction proof and assembly, local Windows monitoring
observed about 51 GB peak kernel-replay working set without a thread limit and
4.7 GB with `LEAN_NUM_THREADS=2`; both full certificates passed. The runs had
different concurrent load, so their elapsed times are not a speed comparison.
Two unchanged repeats of the bounded subtraction certificate returned
`consumer-proof-cache` in 3.6 and 3.9 seconds. This measures warm reuse, not the
cost of proving a changed extraction or changed consumer sources.

Local validation passed all 43 full method certificates against the pinned
revision, checked their 641 distinct source/settings hashes, and audited 409
supporting theorems. The C# selector and batch-runner regression tests,
analyzer-enabled builds (including IDE0005), and workflow actionlint also passed.

To verify several methods with one build locally, invoke the single-file C# app:

```powershell
dotnet run --file verification/Verify.cs -- --action verify --method Subtract --method SubtractUnderflow --profile scalar
```

`SelectGates.cs`, `Verify.cs`, and `TestVerification.cs` are single-file C# apps;
their shared source files are included with `#:include`, as in LeanCIL.

The runner resolves defaults from `manifests/gates.json`. Unregistered
method/profile combinations require
both `--proof` and `--theorem`; proof paths are relative to `verification/` and
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
LeanCIL revision separately from completed gates. All 87 scalar targets now
extract. The pinned revision includes the fixes for multiplication (`Math.BigMul`,
#36), unmanaged aggregate byref operations (#37), aggregate/vector bitcasts
(#38), generated translation proof composition (#39), aggregate proof helpers
(#40), and authenticated local consumer reuse (#42).

The two subtraction proof ports can now use the normal full certificate command
without increasing the generated proof's heartbeat budget. The remaining 44
scalar targets are listed under `remainingPorts`: their consumer proofs still
need migration and certification using the new upstream APIs. SIMD profiles
also require their own proof ports and validation. Closed upstream issues do not
establish those certificates automatically.

Each public gate must retain independent arithmetic and safety contracts,
including initial operands under valid overlap, normal finite return,
caller-byte preservation, and its claimed feature coverage. Re-run the original
mutation/refutation cases before claiming equivalent verification scope.
The previous pin's negative check replaced the first `add` in the compiled
`AddWithCarry` helper with `sub`: the unchanged proof failed in `CarryMemory`
and emitted no certificate. That check was not the full mutation suite.
Further extraction or proof-composition gaps should be reproduced upstream
rather than hidden behind consumer copies of CIL infrastructure.
