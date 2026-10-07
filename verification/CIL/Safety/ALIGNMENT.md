# Alignment audit

The interpreter uses `ordinaryAccessAlignment = 1` for ordinary reference-free
scalar, vector and aggregate accesses in **CoreCLR x64/ARM64 normal memory with
hardware alignment traps disabled**. The source audit below supports that target
convention. JIT correspondence remains outside the kernel proof and is recorded
as a runtime assumption in every safety report. This does not certify portable
CLI conformance or other runtime implementations. No production change is needed
for this model; arbitrary caller byte offsets and overlaps are preserved.

## Specification and implementation evidence

The portable [`ldind.i8` contract](https://learn.microsoft.com/en-us/dotnet/api/system.reflection.emit.opcodes.ldind_i8?view=net-10.0)
requires natural alignment unless modified by `unaligned.`. The
[.NET memory model](https://github.com/dotnet/runtime/blob/4271d88e0aebf3d04f188f1334c2220d80555ef6/docs/design/specs/Memory-model.md)
distinguishes ordinary potentially misaligned accesses from explicitly unaligned
facilities; only the latter have a platform-independent fault-free guarantee.
Neither document makes every ordinary misaligned access fault on every target.

The following source audit uses CoreCLR **v10.0.12**, commit
`4271d88e0aebf3d04f188f1334c2220d80555ef6`:

| Path | Observed instruction-selection rule |
| --- | --- |
| Scalar integer access | `ins_Load`/`ins_Store` select ordinary MOV on x64, and LDR/STR variants on ARM64. |
| Vector indirection | The default `aligned` argument is false. x64 selects MOVUPS; ARM64 selects LDR/STR. |
| Legacy SSE memory operands | `IsContainableHWIntrinsicOp` permits ordinary SIMD16 load containment only with VEX support; explicitly aligned loads have a separate rule. |
| ARM64 ordinary stores | `genCodeForStoreInd` calls `ins_StoreFromSrc`; volatile and GC write-barrier stores follow separate paths. |
| ARM64 unrolled aggregate copy | `genCodeForCpBlkUnroll` uses `CopyBlockUnrollHelper`; its emitters include LDR/STR and LDP/STP. Alignment and overlapping-copy semantics are separate questions. |
| x64 unrolled aggregate copy | `genCodeForCpBlkUnroll` uses `simdUnalignedMovIns` and ordinary MOV for scalar remainders. |

Source locations:
[load/store selection](https://github.com/dotnet/runtime/blob/4271d88e0aebf3d04f188f1334c2220d80555ef6/src/coreclr/jit/instr.cpp),
[default alignment arguments](https://github.com/dotnet/runtime/blob/4271d88e0aebf3d04f188f1334c2220d80555ef6/src/coreclr/jit/codegeninterface.h),
[x64 indirection](https://github.com/dotnet/runtime/blob/4271d88e0aebf3d04f188f1334c2220d80555ef6/src/coreclr/jit/codegenxarch.cpp),
[SSE containment](https://github.com/dotnet/runtime/blob/4271d88e0aebf3d04f188f1334c2220d80555ef6/src/coreclr/jit/lowerxarch.cpp),
[ARM64 stores](https://github.com/dotnet/runtime/blob/4271d88e0aebf3d04f188f1334c2220d80555ef6/src/coreclr/jit/codegenarm64.cpp),
[ARM loads and block copies](https://github.com/dotnet/runtime/blob/4271d88e0aebf3d04f188f1334c2220d80555ef6/src/coreclr/jit/codegenarmarch.cpp).

Windows documents transparent handling of misaligned integer and floating-point
accesses on ARM64, while device memory retains alignment requirements.
[Windows ARM64 ABI](https://learn.microsoft.com/en-us/cpp/build/arm64-windows-abi-conventions#alignment).
This is OS/architecture evidence, not a portable CLI guarantee or a proof of
every JIT optimization. Private stack accesses may use instructions with stronger
alignment when the JIT establishes that alignment; caller and RVA references
cannot inherit that fact merely from their modeled type.

[Arm's alignment rules](https://support.arm.com/documentation/102376/latest/Alignment-and-endianness/Alignment)
distinguish Normal from Device memory and the SCTLR alignment-trap setting.
[Intel's system-programming manual](https://www.intel.com/content/dam/www/public/us/en/documents/manuals/64-ia-32-architectures-software-developer-vol-3a-part-1-manual.pdf)
likewise describes alignment-check exceptions when enabled. The memory convention
does not cover such trap-enabled execution or device mappings.

The extracted operations map to this convention as follows:

| Extracted operation | Memory effect and alignment |
| --- | --- |
| `ldind.i8` / `stind.i8` | Eight-byte ordinary load/store; no natural-alignment caller precondition. |
| UInt64 `ldfld` / `stfld` | Reference formation at the validated field offset, then the same eight-byte access. |
| Admitted `ldobj` / `stobj` | Full 16- or 32-byte reference-free snapshot access; no vector-width alignment requirement. |
| `initobj`, numeric locals and argument homes | Actual initialized byte interval is checked; private storage does not impose alignment on caller views. |
| RVA lookup and span reads | Read-only normal static storage; the exact bytes, extent and access width are checked. Pack1 RVA metadata supplies no stronger alignment. The subsequent ordinary vector dereference uses the same rule. |
| `As`, `AsRef`, field addresses and `GetReference` | Form references without accessing their bytes. Dereferencing later applies the relevant complete access check. |

These rules retain bounds, initialization, layout, lifetime and permission checks.
They do not turn byte alignment into a guarantee that an access otherwise succeeds.

## Supplementary native checks

`dotnet run --project verification/Runner.Tests -c Release -- native-alignment --assembly <production.dll> --output <receipt.json>`
builds the witness against that exact DLL and records its SHA-256, runtime,
architecture and actual feature flags. It exercises Add and Subtract over shared
initial bytes, offsets with every residue modulo eight, input/output partial
overlaps, exact aliases and disjoint outputs. Each available profile checks
41,600 results against independent BigInteger arithmetic and verifies all bytes
outside the output. Legacy SSE explicitly disables AVX; unavailable profiles are
reported separately. A mismatch fails the command and leaves no success receipt.

These samples do not prove universal safety, branch coverage, other methods,
runtime versions, JIT tiers or operating systems. They do not resolve the
separate native overlapping-struct-copy discrepancy.

## Kernel enforcement and validation

`AccessAlignment.lean` proves that a successful checked access meets its requested
alignment at every legal allocation placement. It also connects successful
scalar/vector loads and stores to the actual checked byte read/write and its
independent `AccessRequirements`. These theorems establish the interpreter's
enforcement of its supplied requirement; they do not select the right requirement
for an external runtime operation. Foundation checks audit these results and
the contrasting byte-aligned success and naturally aligned rejection examples.

`InstructionTranslation` currently rejects
`volatile.` and `unaligned.` through its unsupported-opcode fallback; neither is
silently erased. `RuntimeModels` admits exact reference casts and value-only
intrinsics, not aligned load/store APIs. The compiled `AlignedLoad` fixture is
rejected at its raw-pointer conversion, so it does not independently test an
aligned intrinsic reaching the translator. The generic memory checker retains
explicit alignment requirements for operations that need them; these are not
inferred from vector width or waived by an ordinary-access certificate.

The foundation results establish these generic enforcement lemmas; combined
production coverage is listed in the [verification README](../../README.md).
The report's `target-runtime-assumption` marker is permanent evidence
of the correspondence boundary, not a claim that native code was proved.
