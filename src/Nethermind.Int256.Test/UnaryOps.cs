using System;
using System.Collections.Generic;
using System.Linq;
using System.Numerics;

namespace Nethermind.Int256.Test
{
    public static class UnaryOps
    {
        public static IEnumerable<BigInteger> TestCases = new[]{
            0,
            1,
            2,
            3,
            short.MaxValue,
            ushort.MaxValue - 1,
            ushort.MaxValue,
            ushort.MaxValue + 1,
            int.MaxValue,
            uint.MaxValue - 1,
            uint.MaxValue,
            uint.MaxValue + 1ul,
            long.MaxValue,
            ulong.MaxValue - 1,
            ulong.MaxValue,
            BigInteger.Parse("080000000000000008000000000000001", System.Globalization.NumberStyles.HexNumber),
            TestNumbers.TwoTo64,
            TestNumbers.TwoTo128,
            TestNumbers.TwoTo192,
            TestNumbers.UInt128Max,
            TestNumbers.UInt192Max,
            TestNumbers.UInt256Max,
        }.Concat(RandomUnsigned(5));

        public static IEnumerable<BigInteger> SignedTestCases = new[]{
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
            TestNumbers.Int256Max,
            TestNumbers.Int256Min,
        }.Concat(RandomSigned(5));

        public static IEnumerable<ulong> ULongTestCases =
        new ulong[]{
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

        public static IEnumerable<int> ShiftTestCases => Enumerable.Range(0, 257);

        const int Seed = 0;

        public static IEnumerable<BigInteger> RandomSigned(int count)
        {
            Random rand = new(Seed);
            byte[] data = new byte[256 / 8];
            for (int i = 0; i < count; i++)
            {
                rand.NextBytes(data);
                yield return new BigInteger(data);
            }
        }

        public static IEnumerable<BigInteger> RandomUnsigned(int count)
        {
            Random rand = new(Seed);
            byte[] data = new byte[256 / 8];
            for (int i = 0; i < count; i++)
            {
                rand.NextBytes(data);
                data[^1] &= 0x7F;
                yield return new BigInteger(data);
            }
        }

        public static IEnumerable<int> RandomInt(int count)
        {
            Random rand = new(Seed);
            for (int i = 0; i < count; i++)
            {
                yield return rand.Next();
            }
        }
    }
}
