namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    private static ulong WordXor(ulong a, ulong b) => (a | b) & ~(a & b);
    public static void Xor(in UInt256 a, in UInt256 b, out UInt256 res)
        => res = new UInt256(WordXor(a.u0,b.u0), WordXor(a.u1,b.u1), WordXor(a.u2,b.u2), WordXor(a.u3,b.u3));
}
