using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>Adds initial input values, retaining the small-operand dispatch.</summary>
    public static void Add(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        ulong a0 = a.u0, a1 = a.u1, a2 = a.u2, a3 = a.u3;
        ulong b0 = b.u0, b1 = b.u1, b2 = b.u2, b3 = b.u3;
        ulong r0, r1, r2, r3;
        if ((b1 | b2 | b3) == 0)
        {
            r0 = a0 + b0;
            r1 = a1; r2 = a2; r3 = a3;
            if (r0 < a0)
            {
                r1 = a1 + 1;
                if (r1 == 0)
                {
                    r2 = a2 + 1;
                    if (r2 == 0) r3 = a3 + 1;
                }
            }
        }
        else if ((a1 | a2 | a3) == 0)
        {
            r0 = b0 + a0;
            r1 = b1; r2 = b2; r3 = b3;
            if (r0 < b0)
            {
                r1 = b1 + 1;
                if (r1 == 0)
                {
                    r2 = b2 + 1;
                    if (r2 == 0) r3 = b3 + 1;
                }
            }
        }
        else
        {
            ulong carry = 0;
            ulong t0 = a0 + b0;
            r0 = t0 + carry;
            carry = (t0 < a0 ? 1UL : 0UL) + (r0 < t0 ? 1UL : 0UL);
            ulong t1 = a1 + b1;
            r1 = t1 + carry;
            carry = (t1 < a1 ? 1UL : 0UL) + (r1 < t1 ? 1UL : 0UL);
            ulong t2 = a2 + b2;
            r2 = t2 + carry;
            carry = (t2 < a2 ? 1UL : 0UL) + (r2 < t2 ? 1UL : 0UL);
            ulong t3 = a3 + b3;
            r3 = t3 + carry;
            carry = (t3 < a3 ? 1UL : 0UL) + (r3 < t3 ? 1UL : 0UL);
        }
        Unsafe.SkipInit(out res);
        Unsafe.AsRef(in res.u0) = r0;
        Unsafe.AsRef(in res.u1) = r1;
        Unsafe.AsRef(in res.u2) = r2;
        Unsafe.AsRef(in res.u3) = r3;
    }
}
