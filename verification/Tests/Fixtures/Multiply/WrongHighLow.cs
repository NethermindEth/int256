using System.Runtime.CompilerServices;

namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static void Multiply(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        ulong x0 = x.u0;
        ulong y0 = y.u0;
        ulong xTop = x.u2 | x.u3;
        ulong yTop = y.u2 | y.u3;
        ulong xHigh = x.u1 | xTop;
        ulong yHigh = y.u1 | yTop;
        if ((xHigh | yHigh) == 0)
        {
            // Zero and one take this path or the one-limb ladder; a dedicated shortcut cost every call two vector tests.
            ulong high = Multiply64(x0, y0, out ulong low);
            StoreProduct(out res, high, low, 0, 0);
            return;
        }
        if (yHigh == 0)
        {
            MultiplyByUInt64(in x, y0, out res);
            return;
        }
        if (xHigh == 0)
        {
            MultiplyByUInt64(in y, x0, out res);
            return;
        }
        if ((xTop | yTop) == 0)
        {
            MultiplyLimbs2x2(in x, in y, out res);
            return;
        }
        if (xTop == 0)
        {
            MultiplyLimbs2x4(in x, in y, out res);
            return;
        }
        if (yTop == 0)
        {
            MultiplyLimbs2x4(in y, in x, out res);
            return;
        }
        MultiplyLimbs4x4(in x, in y, out res);
    }
}
