using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static unsafe ulong Probe(in UInt256 input) =>
        Sse2.LoadAlignedVector128((ulong*)Unsafe.AsPointer(ref Unsafe.AsRef(in input))).GetElement(0);
}
