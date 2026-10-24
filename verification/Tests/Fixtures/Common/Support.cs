using System.Runtime.InteropServices;

namespace Nethermind.Int256;

/// <summary>Fixture ABI matching the verified UInt256 representation.</summary>
[StructLayout(LayoutKind.Explicit, Size = 32)]
public readonly partial struct UInt256
{
    /// <summary>Low word.</summary>
    [FieldOffset(0)] public readonly ulong u0;
    /// <summary>Second word.</summary>
    [FieldOffset(8)] public readonly ulong u1;
    /// <summary>Third word.</summary>
    [FieldOffset(16)] public readonly ulong u2;
    /// <summary>High word.</summary>
    [FieldOffset(24)] public readonly ulong u3;

    /// <summary>Constructs a value from four words.</summary>
    public UInt256(ulong low, ulong second, ulong third, ulong high)
    {
        u0 = low;
        u1 = second;
        u2 = third;
        u3 = high;
    }
}
