namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>Adds initial input values, allowing arbitrary overlap.</summary>
    public static void Add(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        AddScalar(in a, in b, out res, false);
    }
}
