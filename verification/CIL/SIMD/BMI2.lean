import CIL.WideMultiply

namespace CIL.X86

/- The observed two-argument managed overload returns the high product word.
Its native signature differs; the three-argument overload writes the low word.
https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/X86/Bmi2.cs
https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Math.cs -/
def multiplyNoFlags64 (left right : W64) : W64 := WideMultiply.high64 left right

end CIL.X86
