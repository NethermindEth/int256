namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static void AddWithCarry(ulong x, ulong y, ref ulong carry, out ulong sum)
    {
        ulong r = x + y + carry;
        carry = 0;
        sum = r;
    }
}
