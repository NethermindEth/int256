using System.Numerics;

namespace Nethermind.Int256.Benchmark
{
    public static class Numbers
    {
        public static readonly BigInteger TwoTo64 = new BigInteger(ulong.MaxValue) + 1;
        public static readonly BigInteger TwoTo128 = TwoTo64 * TwoTo64;
        public static readonly BigInteger UInt128Max = TwoTo128 - 1;
        public static readonly BigInteger TwoTo192 = TwoTo128 * TwoTo64;
        public static readonly BigInteger UInt192Max = TwoTo192 - 1;
        public static readonly BigInteger TwoTo256 = TwoTo128 * TwoTo128;
        public static readonly BigInteger UInt256Max = TwoTo256 - 1;

        public static readonly BigInteger Int256Max = ( BigInteger.One << 255 ) - 1;
        public static readonly BigInteger Int256Min = -Int256Max;
    }
}
