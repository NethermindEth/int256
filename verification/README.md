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

Add `--safety` to require both arithmetic and allocation-aware
memory/reference-safety gates against the same fresh
extraction. Combined proofs cover all 87 selected APIs through these representatives:

| Methods | Profiles |
| --- | --- |
| `Add` | `scalar`, `arm64-advsimd`, `x64-sse42`, `x64-avx2`, `x64-avx2-bmi1`, `x64-avx512`, `x64-avx512-bmi1` |
| `AddOverflow` | `scalar`, `arm64-advsimd`, `x64-sse42`, `x64-avx2`, `x64-avx2-bmi1`, `x64-avx512`, `x64-avx512-bmi1` |
| `Subtract`, `SubtractUnderflow` | `scalar`, `arm64-advsimd`, `x64-sse42`, `x64-avx2`, `x64-avx2-bmi1`, `x64-avx512`, `x64-avx512-bmi1` |
| All seven multiplication APIs | All fourteen multiplication representatives (seven arithmetic classes × two Vector256 storage settings) |
| `Lsh`, `Rsh`, `LeftShift`, `RightShift`, `OperatorLsh`, `OperatorRsh` | `scalar`, `x64-vector256` |
| `LtUInt256UInt256`, `GtUInt256UInt256`, `LeUInt256UInt256`, `GeUInt256UInt256` | `scalar`, `x64-vector256`, `x64-avx2`, `x64-avx512` |
| `Xor`, `And`, `Or`, `Not`, `OperatorXor`, `OperatorAnd`, `OperatorOr`, `OperatorNot` | `scalar`, `x64-vector256` |
| `CompareToUInt256Ref`, `CompareToUInt256Value` | `scalar` (checked independence extends to every valid profile) |
| `Lt`/`Le`/`Gt`/`Ge` between `UInt256` and `Int32`, `UInt32`, `Int64`, `UInt64`, in either order | `scalar` (checked independence extends to every valid profile) |
| `EqualsUInt64`, `EqualsUInt32`, `EqualsInt64`, `EqualsInt32` | `scalar`, `x64-vector256` |
| `Eq`/`Ne` between `UInt256` and `Int32`, `UInt32`, `Int64`, `UInt64`, in either order | `scalar`, `x64-vector256` |
| `EqUInt256UInt256`, `EqualsUInt256Ref`, `NeUInt256UInt256`, `EqualsUInt256Value` | `scalar`, `x64-vector256`, `x64-sse41` |

For example, `python verification/verify.py --method EqualsUInt32 --profile scalar --safety`
writes `generated/operations/EqualsUInt32/scalar/safety/report.json`; scalar Add
writes `generated/safety/report.json`. Other representatives fail explicitly.
Primitive `Equals` and Eq/Ne gates additionally prove the combined contract for every
valid profile sharing the representative's `vector256Accelerated` flag. Each
report requires that family theorem's audit and identifies its condition.
The four UInt256 equality APIs additionally require matching `sse41` when the
vector flag is false; vector-mode families ignore that unused flag. Subtract and
SubtractUnderflow on AVX2/AVX512 check both the fast and table-based borrow-repair paths, with
private input snapshots and the actual extracted lookup bytes. Their AVX2 and
AVX512 prefixes establish the same mathematical borrow masks through their
respective comparison or ternary-logic instructions;
the BMI1 variants separately check bit extraction, byte conversion and canonical
Boolean representation. The four scalar
UInt256 relational operators cover valid profiles with `avx512FVL`, `avx2` and
`vector256Accelerated` disabled. Add, Subtract and overflow/underflow-reporting
gates additionally require a typed safety-family theorem for every valid profile
in the representative's checked feature class. Arithmetic family equivalence
alone never extends safety coverage.

ARM and SSE Add/AddOverflow check both small-operand routes and vector fast and
repair paths, including ARM early output stores, while retaining arbitrary input/output overlap. AddOverflow
also binds the returned flag to overflow of the mathematical initial-input sum.
ARM/SSE Subtract and SubtractUnderflow check the small-operand route and vector
fast/borrow-repair routes. Both retain initial-input subtraction and arbitrary
valid overlap; SubtractUnderflow also binds the exact mathematical underflow flag.

`Lsh` and `Rsh` check the full signed-count convention, private operand snapshots,
all four limb-shift routes, the extracted storage helper and frame teardown.
Each result is the mathematical shift of the initial input, with arbitrary valid
overlap and caller-byte preservation. Scalar and vector256-storage representatives
cover both values of `vector256Accelerated`; checked profile equivalence extends
each proof to every valid profile with the same flag. `LeftShift` and `RightShift`
check the actual forwarding calls with the same overlap guarantees. `OperatorLsh`
and `OperatorRsh` additionally check allocation, initialization, loading and retirement
of their private result, returning the mathematical value while preserving every
caller byte. All six APIs have exact direction and feature-family safety gates.

Both `CompareTo` gates prove the exact unsigned comparison result
`-1`, `0` or `1` and check that their extracted operations are profile-independent.
The by-value gate also checks initialization and lifetime of its private argument copy.

Equality contracts specify the Boolean result for initial inputs and preserve
all caller bytes. By-value equality checks its private argument copy; primitive
equality checks zero extension, construction and private aggregate storage.
Signed primitive equality returns false for negative arguments and checks the
unsigned child invocation for nonnegative arguments.
Vector proofs check full load widths, reference offsets and actual child calls.
Ordinary reports remain arithmetic-only. See the
[memory-safety boundary](CIL/Safety/BOUNDARY.md) for calling requirements and
unsupported CLR behaviours, including native-code and GC-root-map correctness.

Safety reports state the [alignment convention](CIL/Safety/ALIGNMENT.md): ordinary
reference-free accesses in x64/ARM64 CoreCLR normal memory permit arbitrary byte
offsets, with hardware alignment traps disabled. Aligned APIs, volatile/atomic
accesses and device memory are excluded. This target-specific convention retains
the overlap contracts; it is not a portable CLI or JIT-correctness theorem.

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

Use `--jobs 2` with `verify_all.py` to check two profiles concurrently. Each worker
starts with an empty proof directory and reuses its own checked dependencies
between jobs; workers share the fresh DLL, not their Lean caches. Extraction and
typed gates are regenerated for every job, and Lake rebuilds their dependents.
No compiled cache is imported from an earlier run. Coverage is issued only after
every certificate and the composition audit pass. The default is one worker.

Add and the scalar profile are the defaults. A selected command rebuilds the assembly and extractor, imports
that invocation's DLL into an isolated proof directory without generated data or
compiled caches, and checks the selected theorem and axiom audit. It invalidates
the previous success report before starting and rechecks source inputs and the
DLL digest before issuing a new one.

By default, `verify_all.py` covers Add/Subtract. It builds one fresh production DLL and checks both methods in all
seven classes, using worker-local proof directories. It then audits the total
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
or changing reports. CI uses `--expanded --safety --print-plan` to select production jobs;
an incomplete plan fails before any partial matrix is emitted.
The complete plan contains 87 methods and 256 method/profile jobs. All have
checked combined arithmetic and memory-safety evidence, including total valid
feature-profile coverage under the documented runtime assumptions.

Use `verify_all.py --expanded --safety --jobs 6` for combined coverage; adjust
`--jobs` for available CPU and memory. Every
certificate must include the arithmetic and safety audits, exact generated
bindings and complete safety family coverage. Arithmetic-only reports cannot
satisfy this mode. Combined aggregate reports live in a separate `safety/`
directory; `--check-reports --safety` retains the same freshness checks.

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
| `UInt256/Methods/ConstructorSafety.lean`, `ValueSafety.lean` | Extracted helper proofs shared by several operation families |
| `Extractor/` | Metadata validation, reachability, translation and Lean emission |
| `verify.py`, `verify_all.py`, `common.py`, `changes.py` | Fresh verification, coverage composition and CI selection |
| `Tests/` | Versioned fixtures, kernel refutations and regression runners |

Pure semantics, representation, storage lemmas and arithmetic do not import
`Extracted`; execution summaries and method proofs do. `Model.lean`, `Proof.lean`
and `Audit.lean` are compatibility imports.

Within a method family, related setup, execution and preservation lemmas live
together. Shared stepping tactics retain separate mathematical theorem statements
and execute the current extracted instructions. Public audit modules remain small
and separate: they bind each selected contract and feature family explicitly.
ISA semantics stay under `CIL/SIMD`; operation-specific vector proofs stay with
their method family.

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

For focused combined shift regressions, run:

```sh
python verification/Tests/Fixtures/Shift/negative_checks.py --method Lsh --profile scalar --safety
```

This requires safety reports for the production, baseline and helper-refactor
fixtures with identical handwritten proofs, then checks the arithmetic/aliasing
counterexamples and public-verifier rejection. Omitting `--safety` retains the
arithmetic-only regression mode.

The regression command runs all required groups from one captured source revision, in
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
CI groups the complete plan into at most 256 matrix entries. Each batch runs every
assigned group and retains its individual receipt, including when another group
fails. The separate coverage job requires combined arithmetic and safety gates.

Positive fixtures are independent versioned C# programs checked with identical
handwritten proof sources and changed compiled instructions. They cover renaming,
inlining, helper extraction, alternative carry/borrow logic, external helpers,
reversed storage arguments and enlarged excluded hardware branches. Applicable
summaries must prove; complete inlining has no candidates, while reversed Add
storage deliberately exercises summary rejection and raw fallback.

The combined suite also checks scalar Add's baseline, renamed helper and reversed
storage arguments, including rejected arithmetic-summary fallback. It runs the
shift fixture jobs with `--safety`. To select the Add regression:
`python verification/Tests/robustness_checks.py --method Add --case Renamed --case ReversedStore --safety`.
The baseline is always included to compare proof hashes and compiled instructions.
The other legacy fixture runs continue to check arithmetic; they do not imply
combined safety coverage for every rewrite.

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

For byte-offset and overlap samples against a specific production DLL, run
`python verification/Tests/native_alignment_checks.py --assembly <dll> --output <receipt.json>`.
The receipt binds the DLL hash and actual runtime features; the
[alignment audit](CIL/Safety/ALIGNMENT.md) explains the remaining proof obligation.

The **Verify UInt256** workflow derives the required method/profile jobs from the
expanded combined coverage plan and runs each proof with `--safety`. Every
selected arithmetic and safety gate must pass. For ordinary
C# edits under `src/`, it compares each method's generated program and validated metadata,
including reachable helpers, feature queries, exact intrinsics and static data,
against the PR base or previous push. Only DLL identity,
assembly version and metadata tokens are ignored. An unchanged comparison may
skip Lean; build/extraction failures fail the check. Other changes, manual runs
and PRs targeting branches other than main force fresh proofs.

Skipping also requires a successful main push run for the exact baseline commit,
with an actually executed, successful combined arithmetic and memory-safety
proof step for that method and profile. Arithmetic-only and skipped proofs do
not supply baseline evidence. Missing history, API access
failures and unmatched jobs force a fresh proof.
The manual **Verify UInt256 proof tests** workflow uses the same regression
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

The October 2026 consolidation reduced handwritten Lean files from 945 to 769.
Execution stages are grouped by operation and ISA; constructor proofs and shift
stepping are shared. Checked instruction equations avoid repeatedly generating
dispatcher simplification machinery. Contracts, semantics and proof budgets are
unchanged.

Representative before/after medians on Windows with Lean 4.34.1:

| Proof workload | Before (s) | After (s) |
|---|---:|---:|
| Binary bitwise vector modules, folded together | 10.12 | 2.93 |
| Scalar bitwise NOT | 7.52 | 1.98 |
| SSE equality | 8.23 | 2.79 |
| Right-shift execution | 17.20 | 9.79 |

These are paired module checks with dependencies already built, including
process/import overhead; the first three also write `.olean` output. They are
not full-pipeline timings and must not be summed into an end-to-end speedup.
Affected public gates and fixtures were checked after each batch, and unchanged
evidence was reused after comparing dependencies. Both arithmetic and safety
evidence reconcile across all 256 production jobs; this is not a new fresh
aggregate run.

For historical context, the arithmetic-only 87-method/256-certificate run took
12,411 seconds with four workers. The later combined arithmetic/safety run used
two workers followed by six; its six-worker continuation checked 50 certificates
and composed coverage in 6,524 seconds, reusing 206 completed certificates.
Those measurements cover different work and do not establish a parallel or
end-to-end speedup. No new full-regression wall time is claimed.

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
