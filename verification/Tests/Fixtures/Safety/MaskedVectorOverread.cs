using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static ulong Probe(in UInt256 input)
    {
        ref ulong start = ref Unsafe.Add(ref Unsafe.AsRef(in input.u0), 1);
        Vector256<ulong> loaded = Unsafe.As<ulong, Vector256<ulong>>(ref start);
        return (loaded & Vector256.Create(ulong.MaxValue, 0ul, 0ul, 0ul)).GetElement(0);
    }
}
