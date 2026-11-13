namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static partial void Probe(in UInt256 a, in UInt256 b, out UInt256 res) =>
        StoreLimbs(out res, GenericStorage<int>.Low(in a), 0, 0, 0);
}

internal static class GenericStorage<T> where T : unmanaged
{
    internal static ulong Low(in UInt256 value) => value.u0;
}
