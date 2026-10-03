using System.Runtime.InteropServices;
namespace Nethermind.Int256;
[StructLayout(LayoutKind.Explicit, Size = 32)]
public readonly partial struct UInt256
{
    [FieldOffset(0)] public readonly ulong u0;
    [FieldOffset(8)] public readonly ulong u1;
    [FieldOffset(16)] public readonly ulong u2;
    [FieldOffset(24)] public readonly ulong u3;
    public UInt256(ulong a, ulong b, ulong c, ulong d) { u0 = a; u1 = b; u2 = c; u3 = d; }
}
