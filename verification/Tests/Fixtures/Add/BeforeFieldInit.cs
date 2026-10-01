namespace Nethermind.Int256;

static class ArithmeticHelper
{
    internal static readonly ulong Seed = Fail();
    private static ulong Fail() => throw new InvalidOperationException();
    public static ulong AddPair(ulong x, ulong y) => x + y;
}
