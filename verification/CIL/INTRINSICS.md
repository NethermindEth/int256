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

## Checks and reusable facts

`VectorLemmas.lean` proves lane packing round trips, bit-preserving casts,
equivalent ARM/SSE incoming-lane construction, AVX2 and AVX-512 lane construction,
arithmetic sign masks, and the actual 0xD4/0x8E ternary truth tables.
`Tests/VectorSemantics.lean` checks lane/operand order, wrapping, Boolean versus
full masks, shifts, selectors, ternary operand order and rejected operands.
All use ordinary kernel-checkable proofs; tests supplement the specification
mapping and do not establish that mapping by sampling.
