import CIL.SIMD.Vector
import CIL.SIMD.AVX

namespace CIL.Vector

/- VPMULLQ retains the low 64 bits of each lane product; VPMOVQ2M extracts
the sign bits. The managed MoveMask overload returns those four bits as Int32.
https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/X86/Avx512DQ.cs -/
def multiplyLow64 (left right : V256) : V256 := zip256 (· * ·) left right

end CIL.Vector
