# UInt256 verification with LeanCIL

This directory consumes LeanCIL through the [pinned Lake dependency](lakefile.toml).
CIL semantics, extraction, and verification infrastructure belong to LeanCIL;
this directory contains only UInt256 specifications, proofs, regression fixtures and the
manifests that LeanCIL's `gates`, `bindings` and `templates` commands read.

Proofs establish arithmetic results, finite return, permitted overlap and preservation of
caller memory. Frame setup supplies typed storage evidence for numeric locals; initialized
values and later writes require their own checked facts. Profile-parametric comparison proofs
use `ProfileAgreement.of_flags` and a kernel-checked empty feature-read list for scalar programs.
See LeanCIL's [proof guide](https://github.com/NethermindEth/LeanCIL/blob/1d635abc3b5f86e6876d73461d9a4a355bcc417e/docs/PROOFS.md)
for the checked execution and contract APIs, and its
[consumer guide](https://github.com/NethermindEth/LeanCIL/blob/1d635abc3b5f86e6876d73461d9a4a355bcc417e/docs/CONSUMERS.md)
for the commands and manifest formats used here.

The Add/Subtract Vector128 helpers use `CodeAt` placements instead of carrying
prefixes, suffixes and their length equations through every execution lemma.
Whole-path ARM addition and multiplication proofs compose checked execution through `WP`.
Local snapshots supply initialized loads and carry updated values across actual stores;
writable unknown homes do not authorize reads. The ARM and portable paths share their state
and save operations. Add/Subtract repair proofs share frame initialization and the checked
storage-call/flag-return suffix. Mixed-vector multiplication uses the same snapshot rules for
word and vector homes, retaining the helper's exact write footprint and caller-memory obligations.

## Verification scope

The 188 method/profile gates in `gates.json` include all
87 scalar targets: addition/subtraction and their reporting variants,
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
The AVX2/AVX512 contracts (`UInt256/Methods/{Add,Subtract}/Vector256*.lean`) bind every reachable body by `rfl`.
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

Each gate applies to its LeanCIL feature profile and a successfully
initialized `Nethermind.Int256.UInt256` type (the manifest's `initializedTypes`); it does not
prove the static constructor. Every scalar target has a scalar gate,
but some accelerated profile and regression-fixture cases still require
proofs. Supporting arithmetic and profile-transport lemmas do not
replace a certificate for the extracted compiled implementation. Changes to
shared proofs require recertification against the final source snapshot.

## Run

Install .NET SDK 10.0.402 or a compatible newer SDK, PowerShell 7, Git, and elan.
Lake selects Lean 4.35.0 using `lean-toolchain`.

```powershell
# Resolve the LeanCIL pin, build its tool and the Release production assembly, and write the
# method templates and catalogued binding sources. -Check compares them instead of writing.
./verification/prepare.ps1

# From verification/: build and audit the extraction-independent supporting library.
lake build
dotnet .lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll audit-library --project . `
  --module UInt256 --prefix UInt256Model --prefix UInt256Proof --axioms propext,Quot.sound,Classical.choice

# Certify scalar Add and run its regression variants.
dotnet .lake/packages/leancil/Extractor/bin/Nethermind.LeanCIL.dll gates gates.json --only Add-scalar
```

`lake build` streams the library build, so `sorry` warnings are visible; `audit-library` then
kernel-replays every module of the `UInt256` closure outside the certified LeanCIL library and
audits, from those replayed oleans, every theorem in the `UInt256Model` and `UInt256Proof`
namespaces (private theorems included), allowing only `propext`, `Classical.choice`, and
`Quot.sound`. No UInt256 code runs during replay or audit, and either namespace matching no
theorem fails. Import new extraction-independent modules from `UInt256.lean` so the audit covers
them. The audit produces no assembly certificate.

`leancil gates` extracts each selected method from the production assembly, checks its proof and
imports in a clean package, reuses source-bound certified artifacts where available,
kernel-checks new consumer modules, audits axioms, and records the assembly, extraction and proof
identities under `artifacts/gates/`. `--only` takes a gate name, a `gate/profile` or a full row
id `gate/profile/variant` (`production` is the gate's own row); `--method` and `--profile` select
by those fields. Every row still receives its own certificate or rejection. Lean defaults to two
worker threads to bound parallel kernel-replay memory; set `LEAN_NUM_THREADS` to override this.
Keep the environment stable within a run: LeanCIL binds it into cache identities.

## Manifests and generated sources

`gates.json` is the gate manifest. Each gate names a method selector, its profiles, its proof
file and the theorem that states the full contract; review each new gate for that. Its regression
cases are the gate's `variants`. The `x64-v3-v128` and `x64-v4-v128` profiles are defined in
`manifests/profiles/`. `manifests/costs.json` holds measured serial seconds per gate and profile,
which `--plan` uses to balance jobs; a gate without a measurement costs its method's median.

`bindings.json` is the binding catalog. `leancil bindings bindings.json` expands its families
from `templates/*.lean.in` into the 142 generated proofs under `proofs/Bindings/`; the other 8
catalog entries and the remaining gate proofs are handwritten. Edit the catalog or a template
rather than a generated file. The catalog covers primitive operators, comparisons, bitwise
operations, shifts, accelerated Add/Subtract and Multiply wrappers. The contracts, checked
method-body equalities and profile theorems are part of the generated source that the verifier
hashes and checks. `--check` fails if a generated file differs from its template.

The scalar and vector Add/Subtract, Multiply, LeftShift and RightShift body families come from
`leancil templates`: `prepare.ps1` extracts 20 method/profile inputs from the production assembly
into `artifacts/templates/` and writes one `UInt256/Generated/MethodTemplates.lean` module that
shares each managed method across all roots and profiles; the proof modules specialize its flags
and callee indices. The module embeds the assembly identity, so every machine regenerates it.
It changes only the generated Lean namespace and omits unused per-PC equations with checked
schema/name guards. Generated sources are ignored by git, materialized before planning,
verification and the library audit, and remain part of the audited source closure.
Specialization wrappers retain their total definitions, including exact profile metadata and
callee parameters. The compiled-method gates still check the exact extraction-to-body
equalities; generating a template does not produce a certificate.

Alternative masked-prepare and blended-subtract regression bodies replace only their changed
instruction ranges and branch targets in the production templates. Multiply's full-entry body
remains handwritten because its merged profile template has different instruction positions.
Fixed-flag wrappers use Lean's built-in elaboration and reduction once to materialize their
specialized definitions; the kernel still checks the resulting ordinary terms. The `PrepareAdd`
flag remains a parameter. Whole-entry Add generation is blocked by the reachable
`get_BroadcastLookup` static-site metadata; the generated helpers avoid that unsupported input
without removing metadata or checks.

## Continuous integration

`.github/workflows/verification.yml` runs every gate and variant on main and on manual dispatch.
On PRs, `leancil gates --plan 8 --changed <path>...` selects the rows whose extraction, proof
imports, fixture project or template depend on a changed file. A change under `selection.all`
in `gates.json` (build configuration, the LeanCIL pin, the catalog, its templates, `prepare.ps1`,
`native-witness.ps1`, the workflow) selects every row, and test-only or benchmark-only changes
select none. The contract audit runs when a PR changes production code, build inputs, this
workflow or any verification source other than documentation. The stable `Verify UInt256` check
always runs and requires every selected check to pass.

CI builds and kernel-checks the shared LeanCIL library once per run; certificate jobs validate the
producer's manifest digest before reusing it. The plan divides the selected rows into at most
eight groups, four running concurrently. A regression variant stays in the group of its gate and
profile, since it reuses the production extraction and statement. Each group job runs
`--plan-group` with two workspaces, uploads its results, and the final job runs
`--require-results`, which fails unless every planned row has exactly one passing result. Each
group publishes stage timings and command transcripts.

Successful main-branch runs also export portable support: each group writes one manifest of the
extraction-independent support it certified, with the compiled artifacts beside it. On later
runs the select job looks up the latest successful push to this repository's `main` branch and
takes each manifest's digest from its artifact name in GitHub's metadata. PR artifacts cannot
provide that trust anchor. Group jobs download the manifests and give the digests separately to
LeanCIL with `LEANCIL_RESTORE_CONSUMER_SUPPORT=true`, so Lake reuses the producer's compiled
support when the sources, toolchain, tools and bound environment match; every restored file is
checked against its manifest hash. Kernel replay is reused only for modules whose complete
compiled import closure, source snapshot, verifier, toolchain and pinned dependencies match.
Missing or expired artifacts fall back to normal verification; a downloaded manifest with an
incorrect digest fails verification. No machine-local signing secret is exported.

## Upstream status and remaining work

The pinned extractor handles initialization assumptions, consumer proof packages and
`Unsafe.SkipInit<T>`. Scalar Add extracts its actual `StoreLimbs` helper.
SkipInit preserves memory; the proof establishes initialization through subsequent writes.
Extraction output is ignored. Each gate checks its expected UInt256 helper bodies against
that output, including byte-offset fields, parameter homes and Boolean return normalization.
The extractor and CIL semantics remain upstream. Extraction admission is separate from
certification: a certificate requires a successful proof of the selected contract for the
extracted method.

## Regression fixtures

Each variant in `gates.json` builds a fixture project under `Tests/Fixtures/<group>/` with its
`FixtureCase`, extracts the gate's method from it, and states what must hold:

- `program` compares the extracted program with the production one or with another variant's
  (`programOf`): `same` for controls that must not change the extraction, `different` for
  mutations and refactors that must.
- `expect: certifies` proves the production contract for the changed body, with the production
  proof or a fixture proof.
- `expect: rejected` requires the production proof to fail without leaving a certificate, and
  its `refutation` certifies a checked contract refutation from a fixture template filled with
  the case's witness values.
- `expect: unchanged` checks only the program relation, for a mutation that no gated
  extraction of that profile reaches.

Fixture builds enforce code style and documentation comments, so an unused directive fails them.
Besides its Baseline (and, where present, Renamed) control, each kernel family keeps one positive
refactor fixture, a changed method body proved against the production contract: Add and Subtract
`ExtractedHelper`, Multiply `AlternativeOrder`, Bitwise `BitwiseHelper`, Shift `LshHelper`, SIMD
and Reporting `EquivalentMask`, Equality `EquivalentReduction` and Compare `ComparisonAlternative`.
Extractor rejection fixtures (unsupported instructions, static initializers, metadata mutations)
are covered by LeanCIL's own tests. Each group's `Tests/Fixtures/<group>/README.md` maps its cases.

`LshHelper` (count computed by a compiled helper) is certified for `Lsh`, `LeftShift` and `op<<`
on scalar and `x64-v3` by `Tests/Fixtures/Shift/LshHelper/<Method>_<profile>.lean`.
The proofs bind the changed bodies by `program[i]? = some body` and reuse the canonical
proof through checked-run transport of the relocated suffix (`UInt256/Safety/Region*.lean`);
that transport is CIL-generic and belongs upstream in LeanCIL. `LshEarlyStore` (output
limb zeroed before the input is read) is an aliasing negative.

The rejected Bitwise mutations `BitwiseWrongOperator` and `BitwiseEarlyStore` also run natively:
after each group, `native-witness.ps1` checks that every such row in its results was rejected,
confirms the fixture assembly still matches its extraction, and runs
`Tests/Fixtures/Bitwise/NativeWitness` against it with `DOTNET_EnableHWIntrinsic` set to 1 and
to 0, so each refutation witness matches what .NET computes.

The Safety variants of scalar Add are the compiled memory-safety probes: each negative certifies
a checked refutation of the public Add contract from a fault pinned to its method, instruction,
rule, reference and width, and each positive certifies a valid call and the probe's own value.
The Profiles group is extractor infrastructure only.

Equality variants cover representative implementations and targeted wrapper faults, and every
production equality gate keeps its certificate. Baseline and Renamed are checked against the
production proof; EquivalentReduction (xor-to-zero vector leaf, scalar-direct vector primitive,
high-half-first SSE reduction) is checked on the vector profiles by fixture proofs under
`Tests/Fixtures/Equality/EquivalentReduction/` that state the production contract verbatim. Their
extraction-independent leaf proofs live once in `Tests/Fixtures/Equality/Shared/`, so each fixture
file only binds its extraction. WrongLane, WrongReduction, WrongReceiver, WrongSnapshot,
WrongSignedEmbedding and WrongPolarity each get a checked refutation and rejection of the
production proof. Helper mutations run at direct `Equals` entries; wrapper-local polarity and
snapshot mutations attach to their own wrappers. Polarity counterexamples compose a checked
child observation through the exact extracted wrapper instead of unfolding its execution again.
The [coverage map](Tests/Fixtures/Equality/README.md) explains the representatives and limits.

Compare variants cover `op<` on scalar, x64-v3 and x64-v4, and `CompareTo(in UInt256)` on scalar.
ComparisonAlternative is proved per profile under `Tests/Fixtures/Compare/ComparisonAlternative/`;
ComparisonLowFirst, ComparisonSigned and ThreeWayAlternative are refuted. The alternative proofs
reuse checked stepping with the complementary order facts required by the compiled branches, at
the default proof limit. ComparisonWrongLane mutates the Vector256-only path, which no .NET 10
profile reaches, so its variants expect an unchanged extraction. ThreeWayAlternative (returns
-7/9) is a refutation because the CompareTo contract is the exact -1/0/1 result; the vector
mutations use `Vector256.LessThan` on sign-flipped lanes and `GetElement` because the extractor
rejects `Vector256.LessThan<long>` and `Vector256.GreaterThan`. Mutations that do not touch the
native x64-v4 `op<` path expect an unchanged extraction there.

Each public gate must retain independent arithmetic and safety contracts,
including initial operands under valid overlap, normal finite return,
caller-byte preservation, and its claimed feature coverage. Re-run the original
mutation/refutation cases before claiming equivalent verification scope.
Further extraction or proof-composition gaps should be reproduced upstream
rather than hidden behind consumer copies of CIL infrastructure.
