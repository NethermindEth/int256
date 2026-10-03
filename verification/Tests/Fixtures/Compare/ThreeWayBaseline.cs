namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    public int CompareTo(in UInt256 b)
    {
        if (u3 != b.u3) return u3 < b.u3 ? -1 : 1;
        if (u2 != b.u2) return u2 < b.u2 ? -1 : 1;
        if (u1 != b.u1) return u1 < b.u1 ? -1 : 1;
        return u0 == b.u0 ? 0 : u0 < b.u0 ? -1 : 1;
    }
}
