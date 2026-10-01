# UInt256.Add formal verification

`UInt256Proof.add_correct` proves the unrestricted public method contract for
the actual Release CIL imported from the assembly. It covers every scalar
dispatch and carry path, normal void return with a proved finite execution bound, the initial inputs'
sum modulo 2^256, and caller-memory preservation, including arbitrary overlapping
input/output ranges. `Audit.lean` checks its exact contract type and prints its
foundational axioms. The fresh-build command below ties that proof to one artifact.

## Project organization

```text
CIL/                         Values, memory, instructions, execution, memory lemmas
  ExecutionLemmas.lean       Fuel monotonicity and uniqueness of successful results
  SymbolicExecution.lean     Shared instruction stepping and candidate bounds
UInt256/
  Representation.lean        Mathematical limbs and caller bytes
  RepresentationLemmas.lean  Representation and input-load proofs
  StorageLemmas.lean         Four-limb storage and byte-memory equations
  Arithmetic/Carry.lean      Pure arithmetic, independent of extracted CIL
  Methods/Add/
    Contract.lean            Independent public contract
    HelperContracts.lean     Observable carry/storage contracts over current CIL
    Automation.lean          Apply contracts from actual symbolic call arguments
    Helpers.lean             Direct small-path execution with carry-case facts
    Small.lean               Small-operand execution and result composition
    SmallAutomation.lean     Small-path call contract automation
    SmallParents.lean        Scalar small-dispatch execution, separated from math
    General.lean             General-path four-word execution witness
    Execution.lean           Scalar arithmetic composition and case dispatch
    EntryAutomation.lean     Scalar-call contract automation
    Entry.lean               Public-entry execution
    Correctness.lean         Public wrapper and universal add_correct theorem
    Examples.lean            Supplementary concrete aliased carry check
    Audit.lean               Exact contract gate and axiom audits
Extractor/                   CLI, metadata validation, reachability, translation,
                             Lean emission and artifact reporting in separate files
Tests/
  Fixtures/                  Versioned Add fixtures independent of production
    Common/Add/              Shared methods in partial UInt256 declarations
    Add/                     Case-specific methods/types and Fixtures.props
  RegressionFixture/         Malformed artifact fixtures
  negative_checks.py         Counterexamples and fail-closed regressions
  robustness_checks.py       Fresh proofs of independent positive fixtures
common.py                    Shared process, hashing and source-selection utilities
manifests/add.json           Selected artifact, method scope and trust assumptions
generated/                   Ignored extraction, metadata and verification report
```

`Model.lean`, `Proof.lean` and `Audit.lean` are thin compatibility imports.
The proof declaration names remain in `UInt256Proof`; representation and contract
names live in `UInt256Model`, separate from the `CIL` execution definitions.
Reusable CIL, representation, storage and arithmetic modules do not import
`Extracted`. Method execution modules import the actual generated instruction data;
the final correctness module composes execution with the independent contract.
The runner copies every source module into a fresh proof directory and records
its digest, excluding generated files and compiled caches.
The final contract axiom audit includes all of its transitive proof dependencies.
Shared stepping follows the generated instructions and uses proved call contracts.
Small-path carry cases supply algorithm facts; caller-private locals and fuel
offsets are derived by the execution procedure.

For another method, add its contract, execution, correctness and audit modules
under `UInt256/Methods/`, and a method manifest. Extend the shared instruction
model and extractor only for the CIL it needs, preserving explicit rejection of
unsupported reachable operations. The current extractor selection and audit runner
still select Add: configurable method selection, new instruction semantics, loops
and exception handling are separate extensions. Shared helper execution proofs
remain bound to this extracted program and its discovered method ordering; reusing
them with another extraction requires checking that binding.

## Selected artifact and environment

`manifests/add.json` selects the standard `Nethermind.Int256.dll`, net10.0, Release,
.NET SDK 10.0.401, and the static entry:

```
System.Void Nethermind.Int256.UInt256::Add(
  Nethermind.Int256.UInt256&,
  Nethermind.Int256.UInt256&,
  Nethermind.Int256.UInt256&)
```

Use a 64-bit little-endian CoreCLR environment with `DOTNET_EnableHWIntrinsic=0`.
Avx2, AdvSimd and Sse42 support queries are modelled as false. Every scalar branch
is included. The standard assembly still contains the hardware branches: the
extractor retains their instructions and marks excluded operations unsupported;
the interpreter fails if they are executed. Hardware-enabled execution, the
instance overload, AddOverflow and the zkEVM build are outside this milestone.

UInt256 has explicit UInt64 fields `u0/u1/u2/u3` at offsets `0/8/16/24`.
The independently defined mathematical value is
`u0 + 2^64*u1 + 2^128*u2 + 2^192*u3`, as a `BitVec 256`.

## Calling and memory model

Valid real calls provide live readable 32-byte ranges for both initial inputs
and a live writable 32-byte output range. Those lifetimes extend through return;
there are no concurrent writes or data races. Each base address plus 31 fits in
the selected native address space. Input pointers may be equal. The output may
alias either or both inputs, including partially overlapping ranges. No arithmetic
edge case is excluded.

UInt256 type initialization is assumed to have completed successfully before the
call; its static initializer is outside this invocation's CIL scope. Helpers on other
managed types are accepted only if their declaring types have no static constructor,
including compiler-generated beforefieldinit constructors. Their initialization
code is not modelled; extraction rejects such dependencies explicitly. The runtime
must provide sufficient stack and avoid asynchronous failures. The method's own
normal termination and absence of interpreter failure are proved under the stated
calling assumptions.

Caller memory is byte-addressed; UInt64 loads/stores use little-endian bytes.
Private locals use a disjoint frame/index address space. `UInt256Model.Contract` in `UInt256/Methods/Add/Contract.lean`
requires successful normal void return for some finite interpreter fuel and an output
equal to addition of the **initial** inputs modulo 2^256. Its byte-memory equation
also specifies that storage outside the 32-byte output range is unchanged.
It quantifies over arbitrary initial bytes and input/output bases; overlapping
references therefore read a consistent shared initial memory.

Unsupported instructions, invalid stack types, absent memory, invalid method or
instruction indexes, and exhausted fuel return failure (`none`). They never count
as successful execution. The current scalar instruction set has no checked
arithmetic, shifts or exception regions; encountering those in a reachable block
is an extraction error. `conv.i8` sign-extends an int32, comparisons are unsigned,
and int32/int64 additions wrap at their actual widths.

## Trust boundary

The Lean kernel checks proof terms. The accepted foundational baseline is
`propext`, `Quot.sound`, and `Classical.choice`; the final theorem uses this baseline.
Native-computation axioms, `sorryAx`, custom correctness axioms and
unchecked computation are not accepted. The proof uses `omega`,
`decide`, definitional reduction and ordinary rewriting.

The extractor, Mono.Cecil 0.11.6, the SDK compiler/build system, and the relation
between the assembly and extracted data remain trusted. A SHA-256 digest identifies
an artifact; it does not prove extraction correctness. CIL-model fidelity also
remains an assumption. The theorem concerns the model of managed CIL execution;
it does not verify CoreCLR, JIT-generated native code or hardware.

The only reachable external operations are the three false feature queries,
`Unsafe.SkipInit<UInt256>` (no write), and `Unsafe.AsRef<UInt64>` (reference identity).
Reachable managed dependencies are discovered from the exact public entry signature
and imported as instruction data, rather than assigned
an assumed addition contract. Defining runtime operations does not establish that
the JIT and hardware implement them faithfully.

Semantic references: [ECMA-335, partitions I–III](https://ecma-international.org/publications-and-standards/standards/ecma-335/)
for the evaluation stack, managed pointers and instructions; [.NET Unsafe source](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/CompilerServices/Unsafe.cs)
for SkipInit and AsRef; [Lean proof validation](https://lean-lang.org/doc/reference/latest/ValidatingProofs/)
for axiom and kernel boundaries.

## Reproduce verification

Prerequisites: Python 3, .NET SDK 10.0.401 and Lean 4.34.1 (`lean-toolchain`),
including Lake, with `dotnet` and `lake` on PATH. The first build needs access to
NuGet for the pinned Mono.Cecil dependency and existing repository dependencies.
From the repository root:

```sh
python verification/verify.py
```

The command builds the selected Release assembly without incremental reuse,
extracts that invocation's DLL into a new proof directory, checks the universal
theorem and its axiom audit, and writes `verification/generated/report.json`
only after every gate passes. It removes a previous success report before starting
and rechecks source inputs and the DLL digest before reporting success. The report
includes the source commit and working-tree status, input digests, assembly digest,
method identities and CIL coverage, toolchain versions, digests of every Lean source module,
calling assumptions, runtime models and trust boundary. A dirty tree is recorded
explicitly; the input digests identify the source used in that case.

Never manually edit or commit `generated/`; regenerate it from the build.
Build outputs and Lake's cache are also ignored.

Relevant PRs and pushes to main run only the fresh production proof through
`python verification/verify.py` in the **Verify UInt256** workflow. For ordinary
C# edits, it first builds the base and current revisions and compares extracted
Add CIL, all reachable helpers and validated metadata. Unchanged extraction skips
the proof, even when other methods in the same source file changed. Verification,
build configuration or workflow changes always run it, as does a manual production
run. PRs targeting branches other than main also run a fresh proof. A skip establishes
unchanged verification inputs relative to main, so main must retain its successful
production-proof gate. Build or extraction failures fail the check rather than
count as unchanged. Any accompanying non-C# change conservatively forces a proof.
The manually triggered **Verify UInt256 proof tests** workflow runs
`python verification/Tests/negative_checks.py` and
`python verification/Tests/robustness_checks.py` in separate parallel jobs.
The regression job first verifies production to establish its fresh baseline.
Run the full suite after changes to the verifier, extractor, CIL semantics or proof
automation, and before releases. Ordinary implementation optimisations require the
fresh production proof; the full fixture matrix need not run for each optimisation.

The robustness harness checks
versioned fixture programs independent of production code, using identical handwritten
Lean sources: a scalar baseline, bitwise-OR carry flags, private-helper renaming,
complete helper inlining with small-operand dispatch, straight-line OR addition,
an additional extracted managed helper, a helper on another type without a static
constructor, reversed storage-helper arguments, and
an excluded hardware branch enlarged beyond the former 512-instruction budget.
It confirms changed instructions and the intended dependency structure. Production
Add is verified separately; fixtures are not manufactured by source-string replacement.
Run a fixture directly with `python verification/verify.py --fixture CarryOr`;
the report identifies fixture verification explicitly.

Fixture methods shared by multiple cases live in `Tests/Fixtures/Common/Add` as
partial UInt256 declarations. `Tests/Fixtures/Add/Fixtures.props` explicitly selects
those files for each named case; each case file contains its distinct methods or
helper type. The baseline selects only shared methods. Complete inlining,
straight-line addition and renamed helpers retain standalone implementations.
The enlarged excluded hardware branch stays unrolled to preserve its instruction
count. These are versioned fixture sources, independent of production source text.

Negative arithmetic and early-write aliasing fixtures have native counterexamples
and kernel-checked refutations of the complete public contract, for every fuel.
Their proofs must fail with a semantic obligation, rather than a resource timeout.
The regression script also seeds stale extraction and a prior successful report,
then requires fresh verification to fail and remove that report. Further fixtures
reject reachable unsupported `mul`, an unresolved helper, a wrong field offset,
cyclic control flow, and helper types with unmodelled static initialisation. A native
witness confirms that the explicit throwing helper constructor raises a type-initialisation
exception. Lean transaction tests check rollback of failed proofs, admitted proofs,
axioms and registrations, while retaining successful summaries. Missing fixtures, compilation failures and changed
fixture structure are maintenance errors. The runner labels fixture-build and
proof-checking failures separately; negative checks additionally require a kernel
refutation and a semantic proof obligation, rejecting resource exhaustion.
The extractor also validates assembly identity, target-framework and Release
configuration attributes; fixtures reject a changed framework or configuration.

All mutations are discarded. The valid `Audit` is checked again at the end.
Run `verify.py` first to provide the valid report used by the stale-output check.
For faster local proof iteration after extraction, use `lake -d verification build Audit`;
this does not refresh the assembly identity or issue a verification report.

Missing toolchains, changed signatures/layouts, unsupported CIL, failed proof
compilation and unapproved axioms cause explicit nonzero failures. An axiom such
as `sorryAx` printed for a failed declaration in a negative test is diagnostic
output from rejected compilation; it cannot pass the final audit or emit success.

When production CIL changes, regenerate first. The demonstrated changes reprove
with the shared execution procedure; other changes may require arithmetic lemmas
or execution support while preserving the independent contract.
The extractor discovers an acyclic graph of reachable managed dependencies;
private names, helper counts and decomposition do not determine extraction.
Optional signature-based summary candidates accelerate proofs, but their behavior
is re-proved against generated CIL. Without a candidate, execution uses raw steps. Candidates are transactional: synchronous elaboration and kernel checking must
succeed without admitted proofs or new axioms. Otherwise all attempted declarations,
registrations and diagnostics are rolled back, and raw execution continues. Call
automation checks that the proved summary exists. This does not guarantee arbitrary
algorithm independence.
The mathematical carry is the high word of the unbounded word sum, under a proved
incoming-carry invariant of zero or one. Both addition and OR of the two overflow
flags implement that result under this invariant.

The public contract resolves the generated entry symbolically and quantifies over
some successful finite fuel. Execution proofs establish sufficiency of a candidate
bound derived from reachable supported instructions; excluded hardware code does
not enlarge it. This is a termination proof, not an assumed budget. Other correct
algorithms can still require new arithmetic lemmas or execution automation; the
fixtures establish the listed transformations, not arbitrary implementation freedom.
Unsupported-feature failures require an explicit semantics extension with proofs,
or restoring the selected configuration; suppressing them is not an update path.
