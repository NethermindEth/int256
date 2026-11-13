using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static ulong Probe(in UInt256 input) =>
        Unsafe.Add(ref Unsafe.Add(ref Unsafe.AsRef(in input.u0), 4), -3);
}
