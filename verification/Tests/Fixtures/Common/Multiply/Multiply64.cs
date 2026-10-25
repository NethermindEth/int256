using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics.X86;
using System.Runtime.Intrinsics.Arm;

namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong Multiply64(ulong a, ulong b, out ulong low)
    {
        if (Bmi2.X64.IsSupported)
        {
            // Two multiplies are faster here because the high-only overload
            // lets the JIT keep both results in registers.
            low = a * b;
            return Bmi2.X64.MultiplyNoFlags(a, b);
        }
        else if (ArmBase.Arm64.IsSupported)
        {
            low = a * b;
            return ArmBase.Arm64.MultiplyHigh(a, b);
        }
        else
        {
            return System.Math.BigMul(a, b, out low);
        }
    }
}