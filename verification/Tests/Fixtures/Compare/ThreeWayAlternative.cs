namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    public int CompareTo(in UInt256 b)
    {
        if (u3 != b.u3) return u3 < b.u3 ? -7 : 9;
        if (u2 != b.u2) return u2 < b.u2 ? -7 : 9;
        if (u1 != b.u1) return u1 < b.u1 ? -7 : 9;
        return u0 == b.u0 ? 0 : u0 < b.u0 ? -7 : 9;
    }
}
