# UInt256 verification

This project checks mathematical contracts against CIL extracted from a freshly
built Release assembly. The original static wrapping `UInt256.Add` and
`UInt256.Subtract` proofs establish, for arbitrary initial inputs:

- The output is `(left + right) mod 2^256` or `(left - right) mod 2^256`.
- Execution terminates with a normal void return for a proved finite fuel bound.
- Bytes outside the 32-byte output range are preserved.
- Inputs and output may overlap arbitrarily, including partial overlap.

The theorems are `UInt256Proof.add_correct` and `UInt256Proof.subtract_correct`.
Their audit gates, `checked_contract` and `checked_subtract_contract`, check the
exact public contract types and audit their transitive proof dependencies.

## Scope and assumptions

The [Add](manifests/add.json) and [Subtract](manifests/subtract.json) manifests
select the standard `Nethermind.Int256.dll`, net10.0, Release, and static
three-reference void entry signatures. Verification models a 64-bit little-endian
CoreCLR environment with fixed runtime feature values. The supported domain is
`CIL.FeatureProfile.Valid`: it separates ARM/x64 capabilities and requires the
prerequisites of the reachable operations. Runtime-disabled features are included;
BMI1 is independent of AVX2. The classifier partitions this domain into seven
behaviour classes:

| Representative | Selected implementation |
|---|---|
| `scalar` | All intrinsics disabled |
| `arm64-advsimd` | ARM64 AdvSimd |
| `x64-sse42` | SSE2/SSSE3/SSE4.2 |
| `x64-avx2`, `x64-avx2-bmi1` | AVX/AVX2, with BMI1 off/on |
| `x64-avx512`, `x64-avx512-bmi1` | AVX/AVX2/AVX512F.VL, with BMI1 off/on |

Other irrelevant feature values do not require additional algorithm proofs:
kernel-checked execution equivalence transports each full contract to every valid
profile in its class. These two contracts exclude instance overloads, reporting
APIs, the throwing subtraction operator and the zkEVM build.

Additional proof gates select the exact signatures
in [the API coverage manifest](manifests/api-coverage.json): comparisons, equality,
bitwise operations, arithmetic flags, shifts and wrapping multiplication. That
inventory is not a verification certificate. All selected gates are registered through the same runner; missing or failing
proofs fail explicitly. Their reports distinguish
conditional agreement on actual feature queries from a checked contract for every
valid profile. The expanded suite covers that selected scope.

Their contracts describe equality and unsigned ordering, 256-bit bitwise results,
exact overflow/underflow flags, and multiplication modulo `2^256`. Pure comparisons
preserve all caller bytes. Returning APIs also execute their actual constructors;
by-reference results retain initial-operand arithmetic and arbitrary overlap.

All six shift APIs cover every signed Int32 count. Nonnegative counts below 256
perform the mathematical shift; counts at least 256 produce zero. The existing
negative-count convention produces zero for multiples of 64 and otherwise shifts
by the count modulo 64 (for example, `-1` shifts by 63). Logical right shifts zero
fill. This public rule is separate from CIL instruction count masking.

Selected APIs also compile a generated typed wrapper that binds the audited
theorems to their independent public contract and feature-family conditions.
The reports retain that wrapper's hash; theorem names and axiom lists alone
cannot substitute for the required type.

Multiplication coverage distinguishes software, BMI2 and ARM64 wide products,
scalar/AVX2/AVX512DQ.VL upper-limb products, and independent vector storage.
Fourteen representatives cover these combinations for each of the seven selected
multiplication APIs.

The represented x86 capabilities obey .NET's inherited support chain:
`AVX512F -> AVX2 -> AVX -> SSE4.2 -> SSSE3 -> SSE2`. `AVX512F.VL` additionally
implies `AVX512F`; the reverse implication is not assumed. A stronger enclosing
guard can therefore justify instructions from an inherited ISA. BMI1 remains
independent. Runtime feature disabling must leave a valid capability combination.

ISA-specific instructions require availability at execution as well as extraction.
An unguarded AVX-512 instruction can verify for an AVX-512 profile, but prevents
complete portable coverage when reachable in a profile without its capability.
The requirement concerns reachability, not an immediately adjacent source `if`.
Portable `Vector128/256/512<T>` APIs do not acquire ISA prerequisites:
`IsHardwareAccelerated` selects performance paths, not API availability. Only
the exact portable overloads with implemented semantics are currently admitted;
an unmodelled portable overload needs model support, not an ISA guard.

Real calls must provide live readable 32-byte input ranges and a live writable
32-byte output range through return. Each base address plus 31 must fit in the
native address space. Calls require sufficient runtime stack, no concurrent
mutation or data race, and no asynchronous runtime failure. UInt256 type
initialization must already have completed successfully. Extraction rejects
helpers on other types with static constructors, including compiler-generated
`beforefieldinit` constructors, because their initialization is not modelled.

Caller memory is byte-addressed, with little-endian UInt64 loads and stores;
private locals occupy a disjoint frame/index address space. The independent
contracts use the **initial** shared memory for both operands, so overlapping
ranges do not weaken the arithmetic guarantee. The mathematical value is a
`BitVec 256` formed from UInt64 fields `u0/u1/u2/u3` at offsets `0/8/16/24`.

## Run verification

Install Python 3, .NET SDK 10.0.401 and Lean 4.34.1, including Lake. Keep `dotnet`
and `lake` on PATH; versions are pinned in `global.json`, `lean-toolchain` and the
manifests. The first build needs NuGet access for Mono.Cecil and repository
dependencies. Run from the repository root:

```sh
python verification/verify.py --method Add
python verification/verify.py --method Subtract
python verification/verify.py --method Subtract --profile x64-avx2-bmi1
python verification/verify.py --method LtUInt256UInt64
python verification/verify_all.py
python verification/verify_all.py --method Lsh
```

Use `--jobs 2` with `verify_all.py` to check two profiles concurrently. Each gets
an uncached proof directory; all use the same fresh DLL, and coverage is issued
only after every certificate and the composition audit pass. The default is one job.

Add and the scalar profile are the defaults. A selected command rebuilds the assembly and extractor, imports
that invocation's DLL into an isolated proof directory without generated data or
compiled caches, and checks the selected theorem and axiom audit. It invalidates
the previous success report before starting and rechecks source inputs and the
DLL digest before issuing a new one.

By default, `verify_all.py` covers Add/Subtract. It builds one fresh production DLL and checks both methods in all
seven classes, using isolated proof directories. It then audits the total
classification and composition rules and checks every full family certificate
before issuing `generated/coverage.json`. The proof host does not need ARM or
AVX-512 hardware: profiles parameterize the managed execution model. Native
intrinsic tests are separate checks on suitably capable hosts. `--check-reports` performs the same
composition using existing reports only if all proof and extraction inputs remain
current. A failed selected run also invalidates the aggregate report.

`--method <selector>` requires total feature coverage for one exact API and writes
its own `coverage.json` beside its scalar report. Depending on the actual program,
coverage uses an audited profile-independent proof or a complete set of family
proofs; a conditional profile-agreement proof alone is insufficient. `--expanded`
requires Add/Subtract and every selected API in the coverage manifest. It refuses
a partial success certificate if any required proof or coverage check fails.

Add `--print-plan` to print the complete method/profile matrix without building
or changing reports. CI uses `--expanded --print-plan` to select production jobs;
an incomplete plan fails before any partial matrix is emitted.
The complete plan contains 87 methods and 256 method/profile jobs. All production
gates and the 131 required regression groups have passing evidence.

Reports live at `verification/generated/report.json` for Add and
`verification/generated/subtract/report.json` for Subtract, alongside the selected
`Extracted.lean` and artifact metadata. Other profiles use
`generated/profiles/<profile>/<method>/`. Reports record source commit/status and
digests, DLL identity, coverage, toolchains, assumptions, axioms and optional
summary rejections, stage timings, exact selected/family certificates and canonical
profile audits. Shared builds bind source inputs and both assembly/extractor
digests before extraction and again before issuing reports. A fixture report is explicitly marked and cannot serve as a
production baseline. Generated files and build caches are ignored; regenerate
them rather than editing or committing them.

For local Add proof iteration after extraction:

```sh
lake -d verification build Audit
```

This does not refresh assembly identity or issue a report. Subtract verification
uses `SubtractAudit` in an isolated package containing the Subtract program as
`Extracted`; do not run that audit against the root Add extraction.

## How the proof works

The extractor discovers an acyclic graph of reachable managed calls from the
exact public entry signature. Private helper names, counts and decomposition are
not extraction requirements. It validates assembly identity, framework,
configuration, layout and reachable instructions, then emits instruction data and
kernel-checked lookup equations. Execution tactics resolve each lookup before
simplifying the selected instruction, avoiding repeated expansion of whole bodies.

ISA-specific semantics and reusable instruction lemmas live in `CIL/SIMD/`;
[the intrinsic mapping](CIL/INTRINSICS.md) records exact overloads and primary
specifications. SIMD execution proofs retain operand snapshots through early
stores and connect lane masks/cascades to the existing four-limb arithmetic.
The AVX lookup is checked against its actual extracted 512-byte RVA data, including
every indexed lane and index bounds. Immutable static data occupies a separate
address space; mutable tables and unsupported initialization fail extraction.

Fixed feature expressions may be cached in unaddressed integer locals, negated
with equality, or combined with Boolean bitwise operations. Forward reachability
merges differing facts to unknown and retains both unknown branch successors.
Address-taken locals are never treated as constant. Instructions are not rewritten:
Lean still executes the emitted feature queries, locals and Boolean operations.
Unsupported or newly variable feature distinctions still require new coverage
evidence; the analysis never assumes an unknown condition is false.

Signature-based helper summaries accelerate execution, but each summary is proved
against the current extracted body. Candidates elaborate and pass kernel checking
transactionally, without new axioms or admitted proofs. Failure rolls back their
declarations, registrations and diagnostics; automation uses only proved summaries
and otherwise executes raw CIL. Carry and borrow contracts propagate an incoming
flag bound of one. The final correctness proof composes this execution with the
independent arithmetic and byte-memory contract.

The public contract quantifies over successful finite fuel; the execution proof
derives a sufficient bound from supported reachable instructions. Excluded hardware
code does not enlarge it. Unsupported reachable CIL, malformed metadata and cyclic
dependencies fail explicitly. Invalid execution states, absent memory and exhausted
fuel return `none`, never success. Loops and exception handling are unsupported;
excluded hardware instructions also fail if executed.

The fixtures demonstrate specific implementation changes, not arbitrary algorithm
independence. A different correct implementation can still need new arithmetic
lemmas or execution support. Adding a verified method requires its own manifest,
contract, execution proof, correctness theorem and audit gate.

| Location | Purpose |
|---|---|
| `CIL/` | Interpreter, memory, execution lemmas and instruction stepping |
| `UInt256/Representation*`, `Storage*` | Limb/byte representation and storage proofs |
| `UInt256/Arithmetic/` | Pure carry and borrow arithmetic |
| `UInt256/ExecutionAutomation.lean` | Shared helper calls and execution automation |
| `UInt256/Methods/` | Independent operation contracts, execution and audits |
| `Extractor/` | Metadata validation, reachability, translation and Lean emission |
| `verify.py`, `verify_all.py`, `common.py`, `changes.py` | Fresh verification, coverage composition and CI selection |
| `Tests/` | Versioned fixtures, kernel refutations and regression runners |

Pure semantics, representation, storage lemmas and arithmetic do not import
`Extracted`; execution summaries and method proofs do. `Model.lean`, `Proof.lean`
and `Audit.lean` are compatibility imports.

## Regression tests and CI

After verifier, extractor, CIL semantics or automation changes, and before
releases, check production coverage and then the complete regression matrix:

```sh
python verification/verify_all.py --expanded --jobs 2
python verification/Tests/all_checks.py --jobs 2
```

During development, batch related changes and run affected checks first. Reuse
prior passing evidence for unaffected code after checking relevant dependency
inputs; a localized change does not require rerunning everything. Keep reports
bound to their actual artifacts and inputs. Use isolated snapshots for longer
tests while continuing independent work.

The regression command runs all 131 required groups from one captured source revision, in
isolated repositories. Each group establishes its own production baseline where
required. It checks source hashes before and after execution and retains command
logs and hashed receipts. Only a complete successful run writes
`generated/all-checks/report.json`; a failed full run invalidates the prior report.

Inspect the matrix or run one group during development:

```sh
python verification/Tests/all_checks.py --print-plan
python verification/Tests/all_checks.py --job legacy-Add
```

A selected job emits a clearly marked partial receipt and cannot certify the full
suite. Individual runners remain available under `Tests/`.

Positive fixtures are independent versioned C# programs checked with identical
handwritten proof sources and changed compiled instructions. They cover renaming,
inlining, helper extraction, alternative carry/borrow logic, external helpers,
reversed storage arguments and enlarged excluded hardware branches. Applicable
summaries must prove; complete inlining has no candidates, while reversed Add
storage deliberately exercises summary rejection and raw fallback.

Negative arithmetic and aliasing fixtures have native witnesses and kernel-checked
refutations of the full contract for every possible successful fuel. Rejection must
reach a semantic proof obligation, not a resource limit or maintenance failure.
Both negative suites check stale artifact/report invalidation. The Add suite also
covers unsupported instructions, unresolved calls, layout, cycles,
framework/configuration, static initialization and transactional summary rollback.
Keep each case's distinct algorithm and witness in its fixture files. Shared
build, extraction and rejection checks live in `Tests/support.py`; `Fixtures.props`
selects shared C# components explicitly. Readable `RefutationTemplate.lean.in`
files supply case data to shared Lean observation lemmas, which exclude every
successful execution fuel. Expected results remain independent of extracted CIL.
A direct fixture run, such as `python verification/verify.py --fixture CarryOr`,
replaces that method's extraction and report; rerun production verification before
using them as a production baseline.

SIMD fixtures cover each algorithm family and both BMI1 choices, with identical
handwritten proofs and confirmed changes in the targeted reachable CIL. Correct
variants rename, inline or extract helpers, rearrange locals and replace equivalent
masks. Wrong alignment, blend/ternary immediates, propagation, table/index scaling
and overlapping rereads require independent kernel refutations before rejection
is counted. Mixed syntax/import errors and resource limits fail the test.
Use `--method`, `--profile`, `--suite` and `--case` to select a smaller run.

Optional native comparisons record actual capabilities and complete byte maps:
`python verification/Tests/native_simd_checks.py --output native-results.json`.
Unavailable profiles are explicitly skipped; native sampling supplements proofs.
Positive samples include two large operands, vector fast paths, cross-half
carry/borrow and cascades (including ARM Add's early-store repair), with disjoint,
exactly aliased and partially overlapping outputs. Results name each sample.

The **Verify UInt256** workflow derives the required method/profile jobs from the
expanded coverage plan. Every selected gate must pass. For ordinary
C# edits under `src/`, it compares each method's generated program and validated metadata,
including reachable helpers, feature queries, exact intrinsics and static data,
against the PR base or previous push. Only DLL identity,
assembly version and metadata tokens are ignored. An unchanged comparison may
skip Lean; build/extraction failures fail the check. Other changes, manual runs
and PRs targeting branches other than main force fresh proofs.

Skipping also requires a successful main push run for the exact baseline commit,
with an actually executed, successful proof step for that method and profile.
A skipped proof does not supply baseline evidence. Missing history, API access
failures and unmatched jobs force a fresh proof.
The manual **Verify UInt256 proof tests** workflow uses the same 131 regression
groups through `all_checks.py --job`, establishing fresh baselines where required.
Its SIMD matrix covers both methods in every representative profile, and a separate
job checks complete selected-API production coverage composition. Additional jobs
run comparison, bitwise, all four returning bitwise operators and all six shift fixture runners with
scalar/vector storage, and reporting fixtures in all seven arithmetic classes.
Equality jobs derive all 52 API/profile groups from the registered contracts.
Multiplication fixtures use all 14 arithmetic/storage representatives, with
wrong-result witnesses in scalar and BMI2 profiles. Passing evidence covers every
required group; reused results retain their original identities and have checked
dependency applicability.

## Measured verification time

The expanded 87-method/256-certificate fresh production run took 12,411 seconds
(3h 26m) on Windows with SDK 10.0.401, Lean 4.34.1 and four workers. Individual
fresh kernel builds had a 74.4-second median (38.6–551.4 seconds). These are
observed timings under concurrent load. Regression acceptance uses applicable
retained group results; no new successful full-regression wall time is claimed.
Concurrent durations overlap and must not be summed.

On Windows with a Ryzen 9 9950X, SDK 10.0.401 and Lean 4.34.1, the committed
`3e2b43b` pipeline checked all 14 production families and coverage composition in
883 seconds without competing builds. Each proof used a fresh directory without
Lean caches; toolchain dependencies were already installed. The shared DLL and
extractor builds took 2.7 and 2.4 seconds, paid once. Per-profile times below
include extraction, fresh kernel checking and setup, excluding those shared builds.
The measurement retained temporary directories only for subsequent module checks.

| Profile | Add (s) | Subtract (s) |
|---|---:|---:|
| scalar | 63.1 | 56.4 |
| arm64-advsimd | 75.7 | 63.0 |
| x64-sse42 | 73.8 | 62.4 |
| x64-avx2 | 63.3 | 60.0 |
| x64-avx2-bmi1 | 54.6 | 62.4 |
| x64-avx512 | 53.4 | 57.7 |
| x64-avx512-bmi1 | 55.9 | 61.4 |

Separate standalone scalar repeats, including assembly/extractor builds, took
59.5/56.9 seconds for Add/Subtract, versus 49.9/43.2 seconds at `d937469`.
Earlier original runs took 58.7/53.0 seconds. The expanded model adds fresh-build
work; these samples show variance and do not establish unchanged pipeline speed.
With dependencies built, generated lookups took 2.3–3.6 seconds, carry/borrow
arithmetic 1.0–1.7 seconds, and SIMD execution modules 7.6–17.5 seconds.
Module timings include process/import overhead and cannot be summed as pipeline
time. No proof budgets were raised.

## Trust boundary

The Lean kernel checks proof terms; the approved foundational axioms are
`propext`, `Classical.choice` and `Quot.sound`. The final audit rejects `sorryAx`,
native-computation axioms and custom correctness axioms. A failed negative proof
may print `sorryAx` diagnostically, but cannot issue a successful report.

The compiler/build system, Mono.Cecil 0.11.6, extractor and fidelity of the formal
CIL/runtime/intrinsic models remain trusted. SHA-256 identifies an artifact without
proving extraction correctness. Feature queries use the fixed selected profile;
unsafe and vector operations use the documented executable models. These proofs
concern managed CIL execution; they do not verify CoreCLR,
JIT-generated native code or hardware.

A native multiplication witness exposed a partially overlapping struct-copy
discrepancy on .NET 10.0.12 x64. The [multiplication notes](UInt256/Methods/Multiply/README.md)
record the counterexample and reproduction command; the CIL proof does not resolve it.

Semantic references: [ECMA-335, partitions I–III](https://ecma-international.org/publications-and-standards/standards/ecma-335/),
[.NET Unsafe source](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/CompilerServices/Unsafe.cs),
and [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).
