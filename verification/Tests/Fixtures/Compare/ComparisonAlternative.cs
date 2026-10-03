namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    public static bool operator <(in UInt256 a, in UInt256 b)
    {
        if (a.u3 < b.u3) return true;
        if (b.u3 < a.u3) return false;
        if (a.u2 < b.u2) return true;
        if (b.u2 < a.u2) return false;
        if (a.u1 < b.u1) return true;
        if (b.u1 < a.u1) return false;
        return a.u0 < b.u0;
    }
    public static bool operator >(in UInt256 a, in UInt256 b) => b < a;
}
