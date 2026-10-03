namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    public static bool operator <(in UInt256 a, in UInt256 b)
    {
        if (a.u3 != b.u3) return (long)a.u3 < (long)b.u3;
        if (a.u2 != b.u2) return a.u2 < b.u2;
        if (a.u1 != b.u1) return a.u1 < b.u1;
        return a.u0 < b.u0;
    }
    public static bool operator >(in UInt256 a, in UInt256 b) => b < a;
}
