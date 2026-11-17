namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static bool SubtractScalar(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        ulong b0 = b.u0;
        if ((b.u1 | b.u2 | b.u3) == 0)
            return SubtractScalarUInt64(in a, b0, out res);
        ulong borrow = 0;
        SubtractWithBorrow(a.u0, b0, ref borrow, out ulong r0);
        SubtractWithBorrow(a.u1, b.u1, ref borrow, out ulong r1);
        SubtractWithBorrow(a.u2, b.u2, ref borrow, out ulong r2);
        SubtractWithBorrow(a.u3, b.u3, ref borrow, out ulong r3);
        StoreLimbs(out res, r0, r1, r2, r3);
        return borrow != 0;
    }
}
