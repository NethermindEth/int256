using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static void StoreLimbs(out UInt256 res, ulong r0, ulong r1, ulong r2, ulong r3)
    {
        Unsafe.SkipInit(out res);
        Unsafe.AsRef(in res.u0) = r0;
        Unsafe.AsRef(in res.u1) = r1;
        Unsafe.AsRef(in res.u2) = r2;
        Unsafe.AsRef(in res.u3) = r3;
    }
}
