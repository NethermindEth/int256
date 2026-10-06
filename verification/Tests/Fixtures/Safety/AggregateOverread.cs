using System.Runtime.CompilerServices;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static ulong ReadSnapshot(UInt256 snapshot) =>
        Unsafe.Add(ref Unsafe.AsRef(in snapshot.u0), 4);
}
