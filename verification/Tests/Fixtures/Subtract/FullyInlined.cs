using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>Fully inlined wrapping subtraction with scalar dispatch.</summary>
    public static void Subtract(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        ulong a0 = a.u0, a1 = a.u1, a2 = a.u2, a3 = a.u3;
        ulong b0 = b.u0, b1 = b.u1, b2 = b.u2, b3 = b.u3;
        ulong r0 = a0 - b0, r1, r2, r3;
        if ((b1 | b2 | b3) == 0)
        {
            r1 = a1; r2 = a2; r3 = a3;
            if (a0 < b0)
            {
                r1 = a1 - 1;
                if (a1 == 0)
                {
                    r2 = a2 - 1;
                    if (a2 == 0) r3 = a3 - 1;
                }
            }
        }
        else
        {
            ulong borrow = a0 < b0 ? 1UL : 0UL;
            r1 = a1 - b1 - borrow;
            borrow = (a1 < b1 ? 1UL : 0UL) | (borrow & (a1 == b1 ? 1UL : 0UL));
            r2 = a2 - b2 - borrow;
            borrow = (a2 < b2 ? 1UL : 0UL) | (borrow & (a2 == b2 ? 1UL : 0UL));
            r3 = a3 - b3 - borrow;
        }
        Unsafe.SkipInit(out res);
        Unsafe.AsRef(in res.u0) = r0;
        Unsafe.AsRef(in res.u1) = r1;
        Unsafe.AsRef(in res.u2) = r2;
        Unsafe.AsRef(in res.u3) = r3;
    }
}
