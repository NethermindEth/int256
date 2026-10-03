# SIMD intrinsic model

`SIMD/Vector.lean` represents vectors by 128/256-bit patterns. Lane zero is the
least significant lane and therefore the first lane in little-endian memory.
`SIMD/Intrinsics.lean` dispatches exact overload families to separate ISA files.
Arguments retain their managed declaration order; the CIL call adapter reverses
the evaluation stack when collecting them.

The extractor must validate declaring type, overload, generic element types,
return type, immediate byte operands and feature prerequisites. The evaluator
also rejects invalid widths, arity, value categories and element indices.
This model describes intrinsic results, not JIT lowering or physical hardware.
It contains no primitive for an entire UInt256 addition or subtraction.

## Portable vector operations

The admitted Add/Subtract operations use `UInt64` lanes for wrapping addition,
subtraction, unsigned less-than and equality. Comparisons produce zero or all
64 bits set in each lane; `EqualsAll` returns a CIL Boolean instead. Construction
packs arguments in low-to-high lane order; extraction returns the selected lane.
Bitwise AND/OR/XOR/complement act on the whole pattern. `AsByte`, `AsUInt32`,
`AsUInt64`, `AsInt64` and `AsDouble` preserve the bits; no floating-point
arithmetic is modelled. Signed 64-bit arithmetic shift operates independently
on lanes, with the portable vector API's count masking modulo 64.

References: [.NET Vector256 implementation](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/Vector256.cs),
[Vector128 implementation](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/Vector128.cs),
[arithmetic shift overloads](https://learn.microsoft.com/en-us/dotnet/api/system.runtime.intrinsics.vector256.shiftrightarithmetic?view=net-10.0).

## ISA mappings

| Managed overload | Lean operation | Interpretation |
| --- | --- | --- |
| `AdvSimd.ExtractVector128(Vector128<ulong>, Vector128<ulong>, byte)` | `advSimd.extract64` | Concatenate first operand below second; shift right by `64*index`; indices 0–1. |
| `Sse2.ShiftLeftLogical128BitLane(Vector128<ulong>, byte)` | `sse.shiftLeftBytes` | Shift the 128-bit pattern left by `8*count`, filling with zero. |
| `Ssse3.AlignRight(Vector128<byte>, Vector128<byte>, byte)` | `sse.alignBytes` | Concatenate second operand below first; shift right by `8*count`. Counts at least 32 yield zero. |
| `Avx2.Permute4x64(Vector256<ulong>, byte)` | `avx2.permute4x64` | Each successive 2-bit control field selects a source 64-bit lane. |
| `Avx2.Blend(Vector256<uint>, Vector256<uint>, byte)` | `avx2.blend32` | Control bit `i` selects lane `i` from the second operand; otherwise first. |
| `Avx.MoveMask(Vector256<double>)` | `avx.moveMask64` | Collect lane sign bits into bits 0–3 of an int32. |
| `Avx.TestZ(Vector256<ulong>, Vector256<ulong>)` | `avx.testZ64` | True exactly when every bit of the bitwise intersection is zero. This is integer VPTEST, not floating VTESTPD. |
| `Avx512F.VL.AlignRight64(Vector256<ulong>, Vector256<ulong>, byte)` | `avx512.alignRight64` | Concatenate second operand below first; shift right by `64*(count & 3)`. |
| `Avx512F.VL.TernaryLogic(Vector256<ulong>, Vector256<ulong>, Vector256<ulong>, byte)` | `avx512.ternaryLogic` | For each bit, table index is `4*first + 2*second + third`. |
| `Bmi1.BitFieldExtract(uint, byte, byte)` | `bmi1.bextr32` | Extract starting at the first immediate, clamp length at the end of the word; out-of-range starts produce zero. |

Primary ISA reference: [Intel instruction-set manual, volume 2](https://cdrdv2-public.intel.com/774492/325383-sdm-vol-2abcd.pdf),
entries PSLLDQ, PALIGNR, VPERMQ, VPBLENDD, VMOVMSKPD, VPTEST, VALIGNQ,
VPTERNLOGQ and BEXTR. Managed-to-ISA declarations:
[ARM extraction](https://learn.microsoft.com/en-us/dotnet/api/system.runtime.intrinsics.arm.advsimd.extractvector128?view=net-10.0),
[TestZ](https://learn.microsoft.com/en-us/dotnet/api/system.runtime.intrinsics.x86.avx.testz?view=net-10.0),
[AVX-512 alignment](https://learn.microsoft.com/en-us/dotnet/api/system.runtime.intrinsics.x86.avx512f.vl.alignright64?view=net-10.0),
[ternary logic](https://learn.microsoft.com/en-us/dotnet/api/system.runtime.intrinsics.x86.avx512f.vl.ternarylogic?view=net-10.0),
[BMI extraction](https://learn.microsoft.com/en-us/dotnet/api/system.runtime.intrinsics.x86.bmi1.bitfieldextract?view=net-10.0).

`Unsafe.BitCast<byte,bool>` preserves the byte representation in an int32 stack
value. Branching uses zero/nonzero; no canonical-zero-or-one assumption is
introduced by the bitcast. The reachable one-bit BMI extraction supplies that
stronger property separately.

## Expanded operations and struct values

The expanded API set additionally uses the following exact operations. `Single`
arguments below carry bits; no floating-point arithmetic is modelled.

| Managed overload | Model | Behavior |
| --- | --- | --- |
| `Vector128/256<T>.op_Equality` for `uint`, `int`, `ulong` | `vector.equalsAll` | Canonical Boolean for equality of every storage bit. |
| `Vector128/256<T>.op_OnesComplement` | `vector.bnot` | Invert every storage bit. |
| `Vector128/256.CreateScalar(uint/ulong)` | `vector.createScalar32/64` | First lane receives the scalar; all upper lanes are zero. |
| `Vector128/256.Create(ulong)` | `vector.create64` | Broadcast into each UInt64 lane. |
| `Vector128/256.ExtractMostSignificantBits<ulong>` | `vector.extractMSB64` | Pack the lane sign bits into low UInt32 bits, lane zero first. |
| `Vector128/256.Sum<ulong>` | `vector.sum64` | Sum lanes modulo 2^64. |
| `Avx.MoveMask(Vector256<float>)` | `avx.moveMask32` | Pack eight 32-bit lane sign bits. |
| `Avx.Blend(Vector256<float>, ..., byte)` | `avx.blend32` | Immediate bit `i` selects lane `i` from the second operand. |
| `Avx2.Blend(Vector256<int>, ..., byte)` | `avx2.blend32` | Same eight-lane bit selection as the UInt32 overload. |
| `Avx2.Add/CompareEqual(Vector256<ulong>, ...)` | `avx2.add64/eq64` | Four wrapping sums or all-one equality masks; AVX2 availability remains required. |
| `Avx2.CompareGreaterThan(Vector256<long>, ...)` | `avx2.signedgt64` | Signed lane comparison; true lanes become all-one masks. |
| `Avx2.Multiply(Vector256<uint>, ...)` | `avx2.multiplyEven32` | Widen products of lanes 0, 2, 4 and 6 into four UInt64 lanes. |
| `Avx2.ShiftRightLogical/ShiftLeftLogical(Vector256<ulong>, byte)` | `avx2.shr64/shl64` | Shift each lane by the unsigned count; counts ≥64 produce zero. |
| `Avx512F.VL.CompareLessThan/GreaterThan/GreaterThanOrEqual(Vector256<ulong>, ...)` | `avx512.ltu64/gtu64/geu64` | Unsigned comparisons; true lanes become all-one masks. |
| `Avx512DQ.MoveMask(Vector256<ulong>)` | `avx512DQ.moveMask64` | Pack four UInt64 sign bits. |
| `Avx512DQ.VL.MultiplyLow(Vector256<ulong>, ...)` | `avx512DQ.mul64` | Four lane products modulo 2^64. |
| `Bmi2.X64.MultiplyNoFlags(ulong, ulong)` | `bmi2.multiplyHigh64` | High 64 bits of the unsigned 128-bit product. The managed return differs from the native `_mulx_u64` return convention. |
| `ArmBase.Arm64.MultiplyHigh(ulong, ulong)` | `armBase64.multiplyHigh64` | Unsigned UMULH high product word. |

Primary managed declarations and implementations are pinned to .NET 10:
[portable vectors](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/Vector256.cs),
[AVX](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/X86/Avx.cs),
[AVX2](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/X86/Avx2.cs),
[AVX-512 F](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/X86/Avx512F.cs),
[AVX-512 DQ](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/X86/Avx512DQ.cs),
[BMI2](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/X86/Bmi2.cs),
[full-product usage](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Math.cs),
and [ARM base](https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/Arm/ArmBase.cs).

`UInt256` values loaded by `ldobj` are 32-byte snapshots; `stobj` stores that
snapshot. Instance receivers are by-reference argument zero. By-value struct
arguments and locals have separate private byte homes, so `ldarga`, `ldloca` and
partial `stfld` updates retain their CIL meanings. `InitLocals=false` creates no
initialized scalar or aggregate value: reads and calls reject unknown values.
`initobj` explicitly clears the whole value. Struct `newobj` zeroes its temporary
before executing the actual extracted constructor and reading the result. This
allocation rule applies even when the calling method has `InitLocals=false`.
These rules follow
[ECMA-335](https://ecma-international.org/wp-content/uploads/ECMA-335_6th_edition_june_2012.pdf),
I.12.1.6.2, II.13.2 and III.4.13/4.21/4.28/4.29. The CIL result does not establish
that a JIT preserves those semantics for arbitrary overlapping native addresses.
The [.NET 10 JIT importer](https://github.com/dotnet/runtime/blob/v10.0.0/src/coreclr/jit/importer.cpp#L8208-L8263)
explicitly initializes value-type constructor temporaries, or records that the
initialization will occur in the method prologue.

## Checks and reusable facts

`VectorLemmas.lean` proves lane packing round trips, bit-preserving casts,
equivalent ARM/SSE incoming-lane construction, AVX2 and AVX-512 lane construction,
arithmetic sign masks, and the actual 0xD4/0x8E ternary truth tables.
`Tests/VectorSemantics.lean` checks lane/operand order, wrapping, Boolean versus
full masks, shifts, selectors, ternary operand order and rejected operands.
All use ordinary kernel-checkable proofs; tests supplement the specification
mapping and do not establish that mapping by sampling.
`Tests/ExpansionIntrinsics.lean` checks the expanded overloads, including high
versus low products, skipped odd lanes, wrapping sums and signed comparisons.
`Tests/AggregateSemantics.lean` checks copied arguments, reused private homes,
actual constructor stores and explicit rejection of unknown values.
