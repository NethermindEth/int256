using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static ulong Probe(in UInt256 input)
    {
        ref ulong target = ref Unsafe.AsRef(in input.u0);
        ulong saved = target;
        target = saved ^ 1;
        target = saved;
        return saved;
    }
}
