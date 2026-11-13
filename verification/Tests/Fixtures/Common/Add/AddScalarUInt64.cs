namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static bool AddScalarUInt64(in UInt256 a, ulong b0, out UInt256 res)
    {
        ulong a0 = a.u0, a1 = a.u1, a2 = a.u2, a3 = a.u3;

        ulong r0 = a0 + b0;
        if (r0 >= a0)
        {
            StoreLimbs(out res, r0, a1, a2, a3);
            return false;
        }
        if (++a1 != 0)
        {
            StoreLimbs(out res, r0, a1, a2, a3);
            return false;
        }
        if (++a2 != 0)
        {
            StoreLimbs(out res, r0, 0, a2, a3);
            return false;
        }
        if (++a3 != 0)
        {
            StoreLimbs(out res, r0, 0, 0, a3);
            return false;
        }

        StoreLimbs(out res, r0, 0, 0, 0);
        return true;
    }
}
