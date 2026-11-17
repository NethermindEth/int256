using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static ulong ReadSnapshot(UInt256 snapshot)
    {
        Unsafe.AsRef(in snapshot.u1) = 17;
        return snapshot.u1;
    }
}
