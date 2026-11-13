using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static partial void Probe(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        Unsafe.SkipInit(out res);
        Unsafe.As<UInt256, Vector256<int>>(ref res) = Vector256<int>.Zero;
    }
}
