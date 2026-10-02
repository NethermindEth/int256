using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>Deliberately broken early-write aliasing fixture.</summary>
    public static void Subtract(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        Unsafe.SkipInit(out res);
        ulong borrow = 0;
        SubtractWithBorrow(a.u0, b.u0, ref borrow, out ulong r0);
        Unsafe.AsRef(in res.u0) = r0;
        SubtractWithBorrow(a.u1, b.u1, ref borrow, out ulong r1);
        Unsafe.AsRef(in res.u1) = r1;
        SubtractWithBorrow(a.u2, b.u2, ref borrow, out ulong r2);
        Unsafe.AsRef(in res.u2) = r2;
        SubtractWithBorrow(a.u3, b.u3, ref borrow, out ulong r3);
        Unsafe.AsRef(in res.u3) = r3;
    }
}
