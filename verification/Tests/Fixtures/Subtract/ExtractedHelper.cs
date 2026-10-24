namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static void SubtractWithBorrow(ulong a, ulong b, ref ulong borrow, out ulong res)
    {
        res = DifferencePair(a, b) - borrow;
        borrow = (a < b ? 1UL : 0UL) | (borrow & (a == b ? 1UL : 0UL));
    }

    private static ulong DifferencePair(ulong a, ulong b) => a - b;
}
