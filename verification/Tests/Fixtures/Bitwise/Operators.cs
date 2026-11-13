namespace Nethermind.Int256;

public readonly partial struct UInt256
{
    public static UInt256 operator ^(in UInt256 left, in UInt256 right)
    {
        Xor(in left, in right, out UInt256 result);
        return result;
    }
    public static UInt256 operator &(in UInt256 left, in UInt256 right)
    {
        And(in left, in right, out UInt256 result);
        return result;
    }
    public static UInt256 operator |(in UInt256 left, in UInt256 right)
    {
        Or(in left, in right, out UInt256 result);
        return result;
    }
    public static UInt256 operator ~(in UInt256 input)
    {
        Not(in input, out UInt256 result);
        return result;
    }
}
