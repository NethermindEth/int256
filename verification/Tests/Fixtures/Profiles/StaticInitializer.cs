using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;
using System.Runtime.Intrinsics;

namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static partial void Probe(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        ulong word = Unsafe.As<byte, Vector256<ulong>>(ref MemoryMarshal.GetReference(ProfileLookup.Bytes)).GetElement(0);
        StoreLimbs(out res, word, 0, 0, 0);
    }
}

internal static class ProfileLookup
{
    static ProfileLookup() => throw new InvalidOperationException("Unsupported initialization");
    internal static ReadOnlySpan<byte> Bytes => [1, 0, 0, 0, 0, 0, 0, 0];
}
