# UInt256 verification with LeanCIL

This directory consumes LeanCIL at
`e3126d4b6abd651ea9afd380c5f84df8d9399d14` through the pinned Lake dependency.
CIL semantics, extraction, and verification infrastructure belong to LeanCIL;
this directory contains only UInt256 specifications and proofs.

Explicit initial frames use named fields with `stackBytes := 0`; helper lemmas
over existing frames preserve the counter. Unknown numeric-local setup supplies
the checked non-span and non-array premises. Arithmetic, overlap, termination
and caller-memory contracts retain their statements. See LeanCIL's
[consumer migration guide](https://github.com/NethermindEth/LeanCIL/blob/e3126d4b6abd651ea9afd380c5f84df8d9399d14/docs/CONSUMER-MIGRATION.md)
for the frame and instruction API changes.

## Verification scope

The 188 registered method/profile gates in `manifests/gates.json` include all
87 scalar migration targets: addition/subtraction and their reporting variants,
multiplication, bitwise operations, shifts, equality, and ordering. Accelerated
gates currently cover vector bitwise operations and shifts, vector/SSE equality,
AVX2/AVX512 ordering, all seven multiplication entries on `arm64-advsimd`, `x64-v3`,
`x64-v4`, `x64-v3-v128` and `x64-v4-v128`, and `Add`/`AddOverflow`/`Subtract`/`SubtractUnderflow`
on `arm64-advsimd`, `x64-sse42`, `x64-v3` and `x64-v4`.
Profiles follow the .NET 10 CoreCLR runtime groups (LeanCIL `docs/RUNTIME-PROFILES.md`); each method is gated
on one profile per distinct reachable body. The ordering operators' Vector256-only path needs Vector256
acceleration without AVX2, which no .NET 10 runtime reports, so it has no gate.
The Vector128 Subtract gates share one profile-parametric proof
(`UInt256/Methods/Subtract/{BorrowRun,BorrowHelper,BorrowContract,SmallHelper,Vector128*,ScalarDispatch,AcceleratedContract}.lean`);
the scalar gates compose the same `BorrowContract` borrow-helper `MethodContract`.
the AVX2/AVX512 contracts (`UInt256/Methods/{Add,Subtract}/Vector256*.lean`) bind every reachable body by `rfl`.
The `arm64-advsimd` gates cover the public entry, the `AddScalar` dispatcher, the
AdvSimd `AddVector128` helper, `AddScalarUInt64` and `StoreLimbs`. Their contracts
(`UInt256/Methods/Add/{Vector128,ARM}*.lean`, `UInt256/Methods/AddSubtract/` and
`UInt256/Safety/{HalfValue,OutputHalves}.lean`) do not import `Extracted`; each proof binds all five
extracted method bodies by `rfl`. `Add` proves `WrappingBinaryContract`; `AddOverflow`
proves `ReportingBinaryContract` with the exact unsigned carry flag.
Gates bind each reachable body either by `rfl` or by `cil_embed` modulo dead code. The multiplication
gates bind the full-width `MultiplyLimbs4x4` body with `cil_embed`, because profile-specific extraction
inserts unreachable blocks and shifts its branch targets: each gate proves its contract over
`Extracted.program.set index (Full.fullBody ...)` and transports it with `UInt256/Safety/EmbeddingTransport.lean`,
which leaves the arithmetic, overlap, finite-return and caller-memory statements unchanged. `fullBody`
includes the folded `typeof` test (`nop` x4, `const32 1`, `brzero`) on its AVX512DQ.VL and AVX2 paths.
The `Add` gate includes its four reachable helpers. `proofs/AddScalar.lean` proves the allocation-aware
`WrappingBinaryContract`: finite checked execution, addition modulo 2^256 of
the initial operands, writable output, and preservation of caller bytes outside
the output. Valid overlap between inputs and output is allowed.
`AddOverflow` additionally proves the exact unsigned carry flag. Subtraction
preserves the same wrapping, overlap and caller-memory contracts;
`SubtractUnderflow` proves the exact unsigned borrow flag. The comparison
gates prove results from the initial operands, finite checked return, and
preservation of caller memory.

Each gate applies to its registered LeanCIL feature profile and a successfully
initialized `Nethermind.Int256.UInt256` type; it does not prove the static
constructor. All 87 signatures in `manifests/targets.json` have scalar gates,
but the original accelerated profile and regression-fixture scope is still
being migrated. Supporting arithmetic and profile-transport lemmas do not
replace a certificate for the extracted compiled implementation. Changes to
shared proofs require recertification against the final source snapshot.

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

`Contracts` builds the library, then runs LeanCIL `audit-library` on the `UInt256`
module closure: it kernel-replays every module outside the certified LeanCIL library
and audits, from those replayed oleans, every theorem in the `UInt256Model` and
`UInt256Proof` namespaces (private theorems included), allowing only `propext`,
`Classical.choice`, and `Quot.sound`. No UInt256 code runs during replay or audit,
and either namespace matching no theorem fails. Modules outside the `UInt256`
import closure are neither built nor audited. It produces no assembly certificate. `Verify` checks consumer proofs and imports in a clean
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
Gates are divided into at most 32 jobs, all running concurrently; each job pays
the shared support build once, which costs about a minute. `VerificationSelection.cs`
balances jobs by the measured serial seconds per gate in `manifests/gate-seconds.json`
(module counts did not predict them; an unsampled gate takes its method's median) and
splits a profile only when it outweighs a job. Each job builds the extractor and
production assembly once, then runs one `verify-batch` session per profile
(`Verify.cs --groups-json`) with two workspaces in parallel. LeanCIL authenticates and reuses
extraction-independent consumer modules locally on that runner, across profiles. Unchanged successful proofs can also be reused;
changed extraction and proof inputs are checked by the upstream verifier. Every selected method still needs
its own certificate, and any failure fails the batch while allowing the other
methods to report their results.
Each batch publishes stage timings and command transcripts identifying the methods.
The verifier defaults Lean to two worker threads to bound parallel kernel-replay
memory; set `LEAN_NUM_THREADS` explicitly to override this locally. CI uses two threads.
Keep the environment stable within a batch: LeanCIL binds it into cache identities.

The 31 primitive comparison gates share `PrimitiveLeaf.run_template`,
`PrimitiveLeaf.checked_template`, and `PrimitiveWrapper.checked32`/`checked64`.
These theorems do not import `Extracted`:
they prove the four signed/unsigned and argument-order variants for any program
and method index whose complete method body matches the expected UInt256 helper.
Each gate checks complete helper and wrapper method equalities against its actual
extraction. The shared wrapper covers operand reversal, signed/unsigned widening,
Boolean negation, the helper call and return. Changed instructions, profile or frame
metadata must satisfy that equality; the template is not an assumed helper contract.
The independent arithmetic, checked finite return and caller-memory guarantees
remain part of each public certificate.

LeanCIL's existing authenticated support cache can reuse these compiled theorems
and their kernel checks across different gates in the same batch. The first gate
still checks the shared proof; subsequent gates freshly check their extraction,
bindings and public proof. This differs from an unchanged whole-proof cache hit.
Successful main-branch runs also export portable support: each job's last
profile group, ordered to hold the most shareable modules, writes one manifest
covering every workspace of its batch session, with the compiled artifacts
beside it. On later runs, `FindConsumerSupport.cs` discovers every job's artifact from the latest successful
push to this repository's `main` branch and obtains their digests from GitHub's
artifact metadata. PR artifacts cannot provide that trust anchor. Certificate
jobs download the manifests and give the digests separately to LeanCIL. Missing
or expired artifacts fall back to normal verification; a downloaded manifest
with an incorrect digest fails verification.

Receivers set `LEANCIL_RESTORE_CONSUMER_SUPPORT=true`, so Lake reuses the
producer's compiled support instead of rebuilding it when the sources, toolchain,
tools and bound environment match; every restored file is checked against its
manifest hash. Kernel replay is reused only for
modules whose complete compiled import closure, source snapshot, verifier,
toolchain and pinned dependencies match. Changes invalidate the affected
dependency closure, and `verified.json` records the support manifest digest.
No machine-local signing secret is exported. Publishing during existing main
batches avoids adding a producer gate to every PR's critical path. The first
main run, or a changed proof snapshot, performs normal kernel replay.
Schema 2 portable fingerprints exclude only Lean's persisted linter diagnostics,
whose temporary source filenames previously prevented comparison-helper reuse.
Declarations, semantic path strings, imports and all other extensions remain
covered, including private module parts. Original compiled artifacts retain
their raw-byte stability checks. Older manifests fall back to normal replay;
the next successful main run exports manifests for the new verifier and pin.

The wrapper refactor removes the extraction-dependent `PrimitiveSafetyLeaf` and
`PrimitiveSafetyContract` adapter modules. The supporting audit then checked 505
theorems; it now checks 3699. Binding checks distinguish reversed operands, signed versus unsigned
widening, and negation, so the reusable wrapper cannot silently accept those
instruction changes. A serial per-module profile of `LtUInt256UInt64` fell from
86.5 to 58.3 seconds with shared wrappers. These diagnostic timings include
repeated import loading and do not predict parallel end-to-end verification.

Earlier helper-only Windows measurements used LeanCIL `0eba3c5` on the same compiled assembly, with
`LEAN_NUM_THREADS=2` and a pre-certified CIL library:

| Consumer verification | Before | Shared helper proofs |
| --- | ---: | ---: |
| First `LtUInt256UInt64` certificate | 298.5 s | 144.8 s |
| Consumer proof build within that check | 115.3 s | 35.7 s |
| Kernel replay within that check | 165.7 s | 91.9 s |
| Subsequent, different `LtInt64UInt256` certificate | - | 65.3 s |

These are single local samples, not CI timing guarantees; short development
checks overlapped the baseline. Both first-gate runs built and kernel-checked
consumer proofs without consumer cache reuse. The subsequent gate reused the
authenticated shared modules, but freshly checked its extraction and public
proof (`consumer-certified-artifact`, not `consumer-proof-cache`). Its kernel
replay took 33.5 seconds and excluded the shared helper modules.
To reproduce, extract the methods once, prepare the certified CIL library with
upstream `scripts/PrepareLibrary.cs`, and set `LEANCIL_CERTIFIED_LIBRARY` and
`LEANCIL_CERTIFIED_LIBRARY_SHA256` to its directory and printed manifest digest.
Set `LEANCIL_CACHE_DIR` to a new directory and `LEAN_NUM_THREADS=2`, then keep
the environment fixed while running these commands from `verification/`:

```text
dotnet .lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll verify artifacts/LtUInt256UInt64/scalar --proof proofs/LtUInt256UInt64Scalar.lean --theorem UInt256Proof.Compare.LtUInt256UInt64.scalar_correctness --proof-root .
dotnet .lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll verify artifacts/LtInt64UInt256/scalar --proof proofs/LtInt64UInt256Scalar.lean --theorem UInt256Proof.Compare.LtInt64UInt256.scalar_correctness --proof-root .
```

The measurements exclude production/extractor builds and CIL library preparation.
The complete 31-gate comparison validation took 20 minutes 51 seconds: the first
two gates ran sequentially to measure reuse, followed by the other 29 at
concurrency four. All 31 full certificates passed, and their 631 distinct
source/settings hashes, assembly/extraction identities and allowed axioms were
audited. The expanded supporting-library audit passed 496 theorems. A direct
binding negative check rejected replacing the unsigned helper's `ltu` instruction
with `gtu`; the unchanged instruction passed. Gate selection and runner regression
checks also passed.

For the same scalar subtraction proof and assembly, local Windows monitoring
observed about 51 GB peak kernel-replay working set without a thread limit and
4.7 GB with `LEAN_NUM_THREADS=2`; both full certificates passed. The runs had
different concurrent load, so their elapsed times are not a speed comparison.
Two unchanged repeats of the bounded subtraction certificate returned
`consumer-proof-cache` in 3.6 and 3.9 seconds. This measures warm reuse, not the
cost of proving a changed extraction or changed consumer sources.

At the initial pin update, local validation passed all 43 full method certificates against the pinned
revision, checked their 641 distinct source/settings hashes, and audited 409
supporting theorems. The C# selector and batch-runner regression tests,
analyzer-enabled builds (including IDE0005), and workflow actionlint also passed.

To verify several methods with one build locally, invoke the single-file C# app:

```powershell
dotnet run --file verification/Verify.cs -- --action verify --method Subtract --method SubtractUnderflow --profile scalar
```

The runner extracts every selected method, then checks them in one LeanCIL
`verify-batch` session, which builds and replays the shared support once;
`--parallel <n>` bounds its concurrent workspaces (LeanCIL default: processor
count / 8). With `--groups-json`, the first profile runs alone to build the shared
support, then the rest run concurrently: `--group-parallel <n>` bounds them
(default: one per 8 cores and 8 GB of memory; sequential while exporting support).
Each method still receives its own certificate. When
`LEANCIL_EXPORT_CONSUMER_SUPPORT` is set, the last method runs as a single
`verify` because support export requires one request. The regression runners
likewise submit each refutation and its `expect: rejected` production proof
through one batch (`RegressionBatch.cs`). CI runs every regression runner,
sharded by profile, whenever it runs the contract audit: on changes to any
verification source, the LeanCIL pin or production code. `SelectGates.cs`
generates that matrix from `manifests/regressions.json`; each sharded runner
fails if the manifest's profiles differ from the ones it supports, and
`TestVerification.cs` fails if a runner is missing from the manifest.

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
Boolean return normalization. Extraction output remains ignored; the expected
UInt256 helper bodies in `PrimitiveLeaf` are checked against that output by each
gate. The extractor and CIL semantics remain upstream.

`manifests/migration-status.json` records the extraction inventory and its tested
LeanCIL revision separately from completed gates. All 87 scalar targets now
extract. The pinned revision includes the fixes for multiplication (`Math.BigMul`,
#36), unmanaged aggregate byref operations (#37), aggregate/vector bitcasts
(#38), generated translation proof composition (#39), aggregate proof helpers
(#40), authenticated local consumer reuse (#42), `ReadOnlySpan<byte>`
static lookup tables (#53) and linear per-site evidence checks (#54).

All scalar ports have registered certificates, and `remainingPorts` is empty.
All 256 gates were recertified on LeanCIL `17f489a` in CI run 39696707787, and every
regression runner passed; `migration-status.json` records the per-runner counts. `BitwiseRegression.cs`
and `ShiftRegression.cs` take a profile argument (default `scalar`), so a
complete run also passes `x64-v3`.

## Regression fixtures

The original fixture cases run through `BitwiseRegression.cs`,
`BitwisePositiveRegression.cs`, `ShiftRegression.cs`, `ShiftPositiveRegression.cs`,
`MultiplyRegression.cs` and `AddSubtractRegression.cs` (`dotnet run --file verification/<runner>`).
Each runner freezes a consumer snapshot, certifies positive fixtures, and for
each mutation certifies a checked contract refutation, then requires the
unchanged production proof to be rejected without leaving a certificate.
Besides its Baseline (and, where present, Renamed) control, each kernel family
keeps one positive refactor fixture, a changed method body proved against the
production contract: Add and Subtract `ExtractedHelper`, Multiply `AlternativeOrder`,
Bitwise `BitwiseHelper`, Shift `LshHelper`, SIMD and Reporting `EquivalentMask`,
Equality `EquivalentReduction` and Compare `ComparisonAlternative`.
`AddSubtractRegression.cs` reports fixtures without a proof as PENDING and
exits nonzero until each has one. Extractor rejection fixtures (unsupported instructions, static
initializers, metadata mutations) are covered by LeanCIL's own tests.

`ShiftPositiveRegression.cs [dir] [all|scalar|x64-v3]` (default `all`) certifies
`LshHelper` (count computed by a compiled helper) for `Lsh`, `LeftShift` and `op<<`.
Each case must extract differently from Baseline and is proved against the production
gate contract by `Tests/Fixtures/Shift/LshHelper/<Method>_<profile>.lean`.
The proofs bind the changed bodies by `program[i]? = some body` and reuse the canonical
proof through checked-run transport of the relocated suffix (`UInt256/Safety/Region*.lean`);
that transport is CIL-generic and belongs upstream in LeanCIL. `LshEarlyStore` (output
limb zeroed before the input is read) is an aliasing negative in `ShiftRegression.cs`.

`SimdRegression.cs` runs the SIMD (Add/Subtract) and Reporting
(AddOverflow/SubtractUnderflow) groups per profile; cases on a profile without a
production gate, and refactors that change a method body without their own
fixture proof, are PENDING. `SafetyRegression.cs` runs the compiled memory-safety
probes: each negative certifies a checked refutation of the public Add contract
from a fault pinned to its method, instruction, rule, reference and width, and each
positive certifies a valid call and
the probe's own value. The Profiles group is extractor infrastructure only. Each
group's `Tests/Fixtures/<group>/README.md` maps every original case to a runner
case, the LeanCIL test that covers it, an unfiled upstream issue draft, or names
it as a dropped positive refactor.

`EqualityRegression.cs [dir] [all|scalar|x64-v3|x64-sse42] [all|<case>]`
covers the equality gates. Baseline and Renamed are checked against the
production proof or a renamed copy of it; EquivalentReduction (xor-to-zero vector
leaf, scalar-direct vector primitive, high-half-first SSE reduction) is checked on
the vector profiles by fixture proofs under `Tests/Fixtures/Equality/EquivalentReduction/`
that state the production contract verbatim. Their extraction-independent leaf proofs
live once in `Tests/Fixtures/Equality/Shared/`, so each fixture file only binds its extraction.
WrongLane, WrongReduction, WrongReceiver, WrongSnapshot, WrongSignedEmbedding
and WrongPolarity each get a checked refutation from `witnesses.json`.

`CompareRegression.cs [dir] [all|<profile>]` covers `op<` on scalar,
x64-v3 and x64-v4, and `CompareTo(in UInt256)` on scalar.
ComparisonAlternative is proved per profile under
`Tests/Fixtures/Compare/ComparisonAlternative/`; ComparisonLowFirst,
ComparisonSigned and ThreeWayAlternative are refuted. ComparisonWrongLane mutates the
Vector256-only path, which no .NET 10 profile reaches; the runner only checks that it leaves every gated extraction unchanged.
Differences from the original group: ThreeWayAlternative (returns -7/9) is a
refutation because the CompareTo contract is the exact -1/0/1 result; the
vector mutations use `Vector256.LessThan` on sign-flipped lanes and
`GetElement` because the extractor rejects `Vector256.LessThan<long>` and
`Vector256.GreaterThan`; x64-v4 runs Baseline only because its native
`op<` path is not touched by any mutation, which the runner checks by
requiring an unchanged extraction for every inapplicable case.

Each public gate must retain independent arithmetic and safety contracts,
including initial operands under valid overlap, normal finite return,
caller-byte preservation, and its claimed feature coverage. Re-run the original
mutation/refutation cases before claiming equivalent verification scope.
The previous pin's negative check replaced the first `add` in the compiled
`AddWithCarry` helper with `sub`: the unchanged proof failed in `CarryMemory`
(now the gate's `carryBody` binding) and emitted no certificate. That check was not the full mutation suite.
Further extraction or proof-composition gaps should be reproduced upstream
rather than hidden behind consumer copies of CIL infrastructure.
