namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>Entry for feature, overload and static-data extraction checks.</summary>
    /// <remarks>These infrastructure fixtures do not claim arithmetic correctness.</remarks>
    public static void Add(in UInt256 a, in UInt256 b, out UInt256 res) => Probe(in a, in b, out res);

    private static partial void Probe(in UInt256 a, in UInt256 b, out UInt256 res);
}
