using System.Runtime.CompilerServices;

namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    [SkipLocalsInit]
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static void MultiplyLimbs2x2(in UInt256 x, in UInt256 y, out UInt256 res)
    {
        ulong x0 = x.u0;
        ulong y0 = y.u0;
        ulong x1 = x.u1;
        ulong y1 = y.u1;

        ulong h00 = Multiply64(x0, y0, out ulong r0);
        ulong h01 = Multiply64(x0, y1, out ulong l01);
        ulong carry = 0;
        ulong r1 = AddAndCountCarry(h00, l01, ref carry);
        ulong h10 = Multiply64(x1, y0, out ulong l10);
        r1 = AddAndCountCarry(r1, l10, ref carry);

        ulong r2 = carry;
        carry = 0;
        r2 = AddAndCountCarry(r2, h01, ref carry);
        r2 = AddAndCountCarry(r2, h10, ref carry);
        ulong h11 = Multiply64(x1, y1, out ulong l11);
        r2 = AddAndCountCarry(r2, l11, ref carry);
        StoreProduct(out res, r0, r1, r2, h11 + carry);
    }
}
