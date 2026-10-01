namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static void AddWithCarry(ulong x, ulong y, ref ulong carry, out ulong sum)
    {
        ulong t = x * y;
        ulong r = t + carry;
        carry = (t < x ? 1UL : 0UL) + (r < t ? 1UL : 0UL);
        sum = r;
    }
}
