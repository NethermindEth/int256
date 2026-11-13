using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static ulong Probe(in UInt256 input) =>
        Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in input)).GetElement(0);
}
