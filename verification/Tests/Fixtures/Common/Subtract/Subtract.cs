namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    /// <summary>Subtracts initial input values modulo 2^256, allowing overlap.</summary>
    public static void Subtract(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        SubtractImpl(in a, in b, out res);
    }

    private static bool SubtractImpl(in UInt256 a, in UInt256 b, out UInt256 res)
    {
        return SubtractScalar(in a, in b, out res);
    }
}
