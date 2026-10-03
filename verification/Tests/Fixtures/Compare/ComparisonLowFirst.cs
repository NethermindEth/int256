namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    public static bool operator <(in UInt256 a, in UInt256 b)
    {
        if (a.u0 != b.u0) return a.u0 < b.u0;
        if (a.u2 != b.u2) return a.u2 < b.u2;
        if (a.u1 != b.u1) return a.u1 < b.u1;
        return a.u3 < b.u3;
    }
    public static bool operator >(in UInt256 a, in UInt256 b) => b < a;
}
