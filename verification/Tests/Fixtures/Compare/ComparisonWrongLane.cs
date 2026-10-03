namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    public static bool operator <(in UInt256 a, in UInt256 b)
    {
        if (System.Runtime.Intrinsics.Vector256.IsHardwareAccelerated)
        {
            var av = System.Runtime.CompilerServices.Unsafe.BitCast<UInt256, System.Runtime.Intrinsics.Vector256<ulong>>(a);
            var bv = System.Runtime.CompilerServices.Unsafe.BitCast<UInt256, System.Runtime.Intrinsics.Vector256<ulong>>(b);
            return System.Runtime.Intrinsics.Vector256.GetElement(av, 0) < System.Runtime.Intrinsics.Vector256.GetElement(bv, 0);
        }
        if (a.u3 != b.u3) return a.u3 < b.u3;
        if (a.u2 != b.u2) return a.u2 < b.u2;
        if (a.u1 != b.u1) return a.u1 < b.u1;
        return a.u0 < b.u0;
    }
    public static bool operator >(in UInt256 a, in UInt256 b) => b < a;
}
