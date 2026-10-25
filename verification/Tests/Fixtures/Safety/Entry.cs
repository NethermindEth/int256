namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>Executes the safety probe, then computes the ordinary sum.</summary>
    public static void Add(in UInt256 a, in UInt256 b, out UInt256 result)
    {
        // Calling the probe preserves the actual load in CIL even though its
        // returned value is unused. The arithmetic result ignores that value.
        _ = Probe(in a);
        AddScalar(in a, in b, out result, false);
    }
}
