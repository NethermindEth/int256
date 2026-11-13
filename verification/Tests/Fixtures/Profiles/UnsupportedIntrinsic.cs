using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static partial void Probe(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        Vector256<uint> vector = Avx2.Add(Vector256<uint>.Zero, Vector256<uint>.Zero);
        Unsafe.SkipInit(out res);
        Unsafe.As<UInt256, Vector256<uint>>(ref res) = vector;
    }
}
