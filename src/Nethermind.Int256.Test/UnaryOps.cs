using System.Numerics;

namespace Nethermind.Int256.Test
{
    public static class UnaryOps
    {
        public static BigInteger[] TestCases =
        {
            0,
            1,
            2,
            3,
            short.MaxValue,
            ushort.MaxValue,
            int.MaxValue,
            uint.MaxValue,
            long.MaxValue,
            ulong.MaxValue,
            TestNumbers.TwoTo64,
            TestNumbers.TwoTo128,
            TestNumbers.TwoTo192,
            TestNumbers.UInt128Max,
            TestNumbers.UInt192Max,
            TestNumbers.UInt256Max,
        };
        
        public static ulong[] ULongTestCases =
        {
            0ul,
            1ul,
            2ul,
            3ul,
            ushort.MaxValue,
            int.MaxValue,
            uint.MaxValue,
            long.MaxValue,
            ulong.MaxValue,
        };
    }
}