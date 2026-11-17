using System.Runtime.InteropServices;

namespace Nethermind.Int256;

/// <summary>Fixture ABI matching the verified UInt256 representation.</summary>
[StructLayout(LayoutKind.Explicit, Size = 32)]
public readonly partial struct UInt256
{
    private const int Len = 4;
    /// <summary>Invokes the left shift wrapper.</summary>
    public void LeftShift(int n, out UInt256 result) => Lsh(this, n, out result);
    /// <summary>Invokes the right shift wrapper.</summary>
    public void RightShift(int n, out UInt256 result) => Rsh(this, n, out result);
    /// <summary>Returns the left shift result.</summary>
    public static UInt256 operator <<(in UInt256 value, int count) { value.LeftShift(count, out UInt256 result); return result; }
    /// <summary>Returns the right shift result.</summary>
    public static UInt256 operator >>(in UInt256 value, int count) { value.RightShift(count, out UInt256 result); return result; }
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
