using System.Numerics;
using System.Collections.Generic;
using System.Linq;

namespace Nethermind.Int256.Test
{
    public static class UnaryOps
    {
        public static IEnumerable<BigInteger> TestCases = Enumerable.Concat(
        new[]{
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
        },
        RandomUnsinged(5)
                              );

        public static IEnumerable<BigInteger> SignedTestCases = Enumerable.Concat(
        new[]{
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
        },
        RandomSinged(5)
                              );

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

        public static IEnumerable<int> ShiftTestCases
        {
            get
            {
                for (int i = 0; i <= 256; i++)
                {
                    yield return i;
                }
            }
        }

        public static IEnumerable<BigInteger> RandomSinged(int count)
        {
            var rand = new System.Random();
            byte[] data = new byte[256 / 8];
            for (int i = 0; i < count; i++)
            {
                rand.NextBytes(data);
                yield return new BigInteger(data);
            }
        }

        public static IEnumerable<BigInteger> RandomUnsinged(int count)
        {
            var rand = new System.Random();
            byte[] data = new byte[256 / 8];
            for (int i = 0; i < count; i++)
            {
                rand.NextBytes(data);
                data[data.Length - 1] &= (byte)0x7F;
                yield return new BigInteger(data);
            }
        }

        public static IEnumerable<int> RandomInt(int count)
        {
            var rand = new System.Random();
            for (int i = 0; i < count; i++)
            {
                yield return rand.Next();
            }
        }
    }
}
