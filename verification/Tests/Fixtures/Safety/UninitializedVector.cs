using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    [SkipLocalsInit]
    private static ulong Probe(in UInt256 input)
    {
        Unsafe.SkipInit(out UInt256 snapshot);
        Unsafe.AsRef(in snapshot.u0) = 7;
        return Unsafe.As<UInt256, Vector256<ulong>>(ref snapshot).GetElement(0);
    }
}
