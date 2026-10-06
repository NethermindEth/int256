using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static ulong Probe(in UInt256 input)
    {
        ref Vector256<ulong> start = ref Unsafe.As<UInt256, Vector256<ulong>>(ref Unsafe.AsRef(in input));
        return Unsafe.Add(ref start, unchecked((nuint)ulong.MaxValue)).GetElement(0);
    }
}
