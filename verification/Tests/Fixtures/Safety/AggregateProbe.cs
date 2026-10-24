namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    private static ulong Probe(in UInt256 input) =>
        ReadSnapshot(new UInt256(7, 8, 9, 10));
}
