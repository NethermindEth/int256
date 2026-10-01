# UInt256.Add formal verification

`UInt256Proof.add_correct` proves the unrestricted public method contract for
the actual Release CIL imported from the assembly. It covers every scalar
dispatch and carry path, normal void return within fuel 512, the initial inputs'
sum modulo 2^256, and caller-memory preservation, including arbitrary overlapping
input/output ranges. `Audit.lean` checks its exact contract type and prints its
foundational axioms. The fresh-build command below ties that proof to one artifact.

## Project organization

```text
CIL/                         Values, memory, instructions, execution, memory lemmas
UInt256/
  Representation.lean        Mathematical limbs and caller bytes
  RepresentationLemmas.lean  Representation and input-load proofs
  StorageLemmas.lean         Four-limb storage and byte-memory equations
  Arithmetic/Carry.lean      Pure arithmetic, independent of extracted CIL
  Methods/Add/
    Contract.lean            Independent public contract
    Helpers.lean             Extracted StoreLimbs, carry and small-path execution
    Small.lean               Small-operand execution and result composition
    Execution.lean           Scalar dispatch and general-path execution
    Correctness.lean         Public wrapper and universal add_correct theorem
    Examples.lean            Supplementary concrete aliased carry check
    Audit.lean               Exact contract gate and axiom audits
Extractor/                   CLI, metadata validation, reachability, translation,
                             Lean emission and artifact reporting in separate files
RegressionFixture/           Malformed artifact fixtures
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

For another method, add its contract, execution, correctness and audit modules
under `UInt256/Methods/`, and a method manifest. Extend the shared instruction
model and extractor only for the CIL it needs, preserving explicit rejection of
unsupported reachable operations. The current extractor selection and audit runner
still select Add: configurable method selection, new instruction semantics, loops
and exception handling are separate extensions. Shared helper execution proofs
remain bound to this extracted program and its validated method ordering; reusing
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
call; its static initializer is outside this invocation's CIL scope. The runtime
must provide sufficient stack and avoid asynchronous failures. The method's own
normal termination and absence of interpreter failure are proved under the stated
calling assumptions.

Caller memory is byte-addressed; UInt64 loads/stores use little-endian bytes.
Private locals use a disjoint frame/index address space. `UInt256Model.Contract` in `UInt256/Methods/Add/Contract.lean`
requires normal void return within the explicit interpreter bound and an output
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
The five managed bodies are imported as instruction data, rather than assigned
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

CI runs the same command, followed by `python verification/negative_checks.py`.
The regression script uses temporary copies to break the carry arithmetic, builds
and imports the changed assembly, runs a concrete incorrect-result witness, and
requires the original correctness proof to fail. It also seeds stale extraction
and a prior successful report, then requires the fresh-build gate to fail and
remove that report. Further fixtures reject a reachable unsupported `mul`, an
unresolved helper, a wrong field offset and cyclic control flow.
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

When production CIL changes, regenerate first, inspect changed instructions and adjust the
execution proof and arithmetic lemmas while preserving the independent contract.
Unsupported-feature failures require an explicit semantics extension with proofs,
or restoring the selected configuration; suppressing them is not an update path.
