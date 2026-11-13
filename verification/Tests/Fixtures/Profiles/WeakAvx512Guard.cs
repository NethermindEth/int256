using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static partial void Probe(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        if (Avx2.IsSupported)
        {
            Vector256<ulong> vector = Vector256.Create(a.u0, a.u1, a.u2, a.u3);
            vector = Avx512F.VL.TernaryLogic(vector, vector, vector, 0xF0);
            StoreLimbs(out res, vector.GetElement(0), vector.GetElement(1), vector.GetElement(2), vector.GetElement(3));
        }
        else StoreLimbs(out res, b.u0, b.u1, b.u2, b.u3);
    }
}
