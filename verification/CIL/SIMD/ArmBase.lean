import CIL.WideMultiply

namespace CIL.Arm

/- Exact unsigned overload: A64 UMULH, rather than signed SMULH.
https://github.com/dotnet/runtime/blob/v10.0.0/src/libraries/System.Private.CoreLib/src/System/Runtime/Intrinsics/Arm/ArmBase.cs -/
def multiplyHigh64 (left right : W64) : W64 := WideMultiply.high64 left right

end CIL.Arm
