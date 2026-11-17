using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static partial void Probe(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        if (Avx2.IsSupported) StoreLimbs(out res, a.u0, a.u1, a.u2, a.u3);
        else StoreLimbs(out res, b.u0, b.u1, b.u2, b.u3);
    }
}
