using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static ulong Probe(in UInt256 input) =>
        Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(Lookup)).GetElement(0);
}
