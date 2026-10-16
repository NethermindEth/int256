namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    public static void Xor(in UInt256 a, in UInt256 b, out UInt256 res)
        => res = new UInt256(a.u0 ^ b.u0, a.u1 ^ b.u1, a.u2 ^ b.u2, a.u3 ^ b.u3);
}
