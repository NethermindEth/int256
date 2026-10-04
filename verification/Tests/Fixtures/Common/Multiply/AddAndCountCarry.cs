using System.Runtime.CompilerServices;

namespace Nethermind.Int256;
public readonly partial struct UInt256
{
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    private static ulong AddAndCountCarry(ulong x, ulong y, ref ulong carry)
    {
        ulong sum = x + y;
        carry += sum < x ? 1UL : 0UL;
        return sum;
    }
}
