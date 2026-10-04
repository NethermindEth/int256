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
            return Bmi2.X64.MultiplyNoFlags(a, b) + 1;
        }
        else if (ArmBase.Arm64.IsSupported)
        {
            low = a * b;
            return ArmBase.Arm64.MultiplyHigh(a, b);
        }
        else
        {
            // No widening multiply instruction on this target (e.g. riscv64). Spelled out rather than
            // deferred to Math.BigMul, which repeats the same ISA checks and then calls an
            // out-of-line software fallback that cannot inline into the 256-bit limb loops.
            uint al = (uint)a, ah = (uint)(a >> 32);
            uint bl = (uint)b, bh = (uint)(b >> 32);

            ulong mull = (ulong)al * bl;
            ulong t = (ulong)ah * bl + (mull >> 32);
            ulong tl = (ulong)al * bh + (uint)t;

            low = (tl << 32) | (uint)mull;
            return (ulong)ah * bh + (t >> 32) + (tl >> 32);
        }
    }
}
