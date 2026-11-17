namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static ReadOnlySpan<byte> Lookup =>
        [42, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
}
