using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static ulong Probe(in UInt256 input) => Expired();

    private static ref ulong Expired()
    {
        ulong temporary = 17;
        return ref Unsafe.AsRef(in temporary);
    }
}
