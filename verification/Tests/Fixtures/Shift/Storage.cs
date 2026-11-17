using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;

namespace Nethermind.Int256;
public readonly partial struct UInt256
{
internal static void SetLimbs(out UInt256 res, ulong z0, ulong z1, ulong z2, ulong z3)
    {
        Unsafe.SkipInit(out res);
        if (Vector256.IsHardwareAccelerated)
        {
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.Create(z0, z1, z2, z3);
        }
        else
        {
            ref ulong p = ref Unsafe.As<UInt256, ulong>(ref res);
            p = z0;
            Unsafe.Add(ref p, 1) = z1;
            Unsafe.Add(ref p, 2) = z2;
            Unsafe.Add(ref p, 3) = z3;
        }
    }
}
