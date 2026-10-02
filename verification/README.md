# UInt256 wrapping arithmetic verification

This project proves the static wrapping `UInt256.Add` and `UInt256.Subtract`
methods against CIL extracted from a freshly built Release assembly. For arbitrary
initial inputs, each proof establishes:

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
CoreCLR environment with `DOTNET_EnableHWIntrinsic=0`: Avx2, AdvSimd and Sse42
support queries are false. Every scalar dispatch and carry/borrow path is covered.
Hardware-enabled execution, instance overloads, `AddOverflow`, `SubtractUnderflow`,
the throwing subtraction operator and the zkEVM build are outside this scope.

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
```

Add is the default. Each command rebuilds the assembly and extractor, imports
that invocation's DLL into an isolated proof directory without generated data or
compiled caches, and checks the selected theorem and axiom audit. It invalidates
the previous success report before starting and rechecks source inputs and the
DLL digest before issuing a new one.

Reports live at `verification/generated/report.json` for Add and
`verification/generated/subtract/report.json` for Subtract, alongside the selected
`Extracted.lean` and artifact metadata. They record source commit/status and
digests, DLL identity, coverage, toolchains, assumptions, axioms and optional
summary rejections. A fixture report is explicitly marked and cannot serve as a
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
| `UInt256/Methods/{Add,Subtract}/` | Operation contracts, execution and audits |
| `Extractor/` | Metadata validation, reachability, translation and Lean emission |
| `verify.py`, `common.py`, `changes.py` | Fresh verification, shared utilities and CI selection |
| `Tests/` | Versioned fixtures, kernel refutations and regression runners |

Pure semantics, representation, storage lemmas and arithmetic do not import
`Extracted`; execution summaries and method proofs do. `Model.lean`, `Proof.lean`
and `Audit.lean` are compatibility imports.

## Regression tests and CI

Run the full suites after verifier, extractor, CIL semantics or automation changes,
and before releases. Negative checks require current successful production reports
from the verification commands above:

```sh
python verification/Tests/change_checks.py
python verification/Tests/negative_checks.py
python verification/Tests/robustness_checks.py
python verification/Tests/subtract_negative_checks.py
python verification/Tests/robustness_checks.py --method Subtract
```

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
Shared test utilities live in `Tests/support.py`;
fixture components are explicitly selected by each method's `Fixtures.props`.
A direct fixture run, such as `python verification/verify.py --fixture CarryOr`,
replaces that method's extraction and report; rerun production verification before
using them as a production baseline.

The **Verify UInt256** workflow checks Add and Subtract separately. For ordinary
C# edits under `src/`, it compares each method's generated program and validated metadata,
including all reachable helpers, against the PR base or previous push. Only DLL identity,
assembly version and metadata tokens are ignored. An unchanged comparison may
skip Lean; build/extraction failures fail the check. Other changes, manual runs
and PRs targeting branches other than main force fresh proofs.

**Main must remain a successfully verified baseline.** The comparison gate checks
unchanged verification inputs; it does not check the baseline's verification history.
The manual **Verify UInt256 proof tests** workflow runs both methods' positive and
negative suites, establishing a fresh production baseline for each regression job.

## Trust boundary

The Lean kernel checks proof terms; the approved foundational axioms are
`propext`, `Classical.choice` and `Quot.sound`. The final audit rejects `sorryAx`,
native-computation axioms and custom correctness axioms. A failed negative proof
may print `sorryAx` diagnostically, but cannot issue a successful report.

The compiler/build system, Mono.Cecil 0.11.6, extractor and fidelity of the formal
CIL/runtime models remain trusted. SHA-256 identifies an artifact without proving
extraction correctness. The external operations are modelled as false feature
queries, `Unsafe.SkipInit<UInt256>` (no write) and `Unsafe.AsRef<UInt64>` (reference
identity). These proofs concern managed CIL execution; they do not verify CoreCLR,
JIT-generated native code or hardware.

Semantic references: [ECMA-335, partitions I–III](https://ecma-international.org/publications-and-standards/standards/ecma-335/),
[.NET Unsafe source](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/CompilerServices/Unsafe.cs),
and [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).
