using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>Adds initial input values, allowing arbitrary overlap.</summary>
    public static void Add(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        AddScalar(in a, in b, out res, false);
    }

    private static bool AddScalar(in UInt256 a, in UInt256 b, out UInt256 res, bool detectOverflow)
    {

        ulong b0 = b.u0;
        if ((b.u1 | b.u2 | b.u3) == 0)
        {
            return AddScalarUInt64(in a, b0, out res);
        }

        // Addition commutes and the EVM puts the small operand on either side of the stack
        ulong a0 = a.u0;
        if ((a.u1 | a.u2 | a.u3) == 0)
        {
            return AddScalarUInt64(in b, a0, out res);
        }

        // Loads stay next to their use: the one-limb paths above share this method's prolog
        ulong carry = 0;
        AddWithCarry(a0, b0, ref carry, out ulong r0);
        AddWithCarry(a.u1, b.u1, ref carry, out ulong r1);
        AddWithCarry(a.u2, b.u2, ref carry, out ulong r2);
        AddWithCarry(a.u3, b.u3, ref carry, out ulong r3);
        StoreLimbs(out res, r0, r1, r2, r3);
        return carry != 0;
    }

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

    private static void AddWithCarry(ulong x, ulong y, ref ulong carry, out ulong sum)
    {
        ulong t = x * y;
        ulong r = t + carry;
        carry = (t < x ? 1UL : 0UL) + (r < t ? 1UL : 0UL);
        sum = r;
    }

    private static void StoreLimbs(out UInt256 res, ulong r0, ulong r1, ulong r2, ulong r3)
    {
        Unsafe.SkipInit(out res);
        Unsafe.AsRef(in res.u0) = r0;
        Unsafe.AsRef(in res.u1) = r1;
        Unsafe.AsRef(in res.u2) = r2;
        Unsafe.AsRef(in res.u3) = r3;
    }
}
