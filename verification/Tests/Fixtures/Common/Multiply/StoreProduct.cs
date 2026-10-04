using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;

namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void StoreProduct(out UInt256 res, ulong r0, ulong r1, ulong r2, ulong r3)
    {
        if (Vector256.IsHardwareAccelerated)
        {
            Unsafe.SkipInit(out res);
            Unsafe.As<UInt256, Vector256<ulong>>(ref res) = Vector256.Create(r0, r1, r2, r3);
            return;
        }
        StoreLimbs(out res, r0, r1, r2, r3);
    }
}
