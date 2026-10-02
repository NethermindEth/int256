namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static void SubtractWithBorrow(ulong a, ulong b, ref ulong borrow, out ulong res)
    {
        ulong intermediate = a - b;
        res = intermediate - borrow;
        borrow = (a < b ? 1UL : 0UL) + (intermediate < borrow ? 1UL : 0UL);
    }
}
