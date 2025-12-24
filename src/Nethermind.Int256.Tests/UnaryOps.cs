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
            TestNumbers.TwoTo64 - 1,
            TestNumbers.TwoTo64,
            TestNumbers.TwoTo64 + 1,
            TestNumbers.TwoTo128 - 1,
            TestNumbers.TwoTo128,
            TestNumbers.TwoTo128 + 1,
            TestNumbers.TwoTo192 - 1,
            TestNumbers.TwoTo192,
            TestNumbers.TwoTo192 + 1,
            TestNumbers.UInt128Max - 1,
            TestNumbers.UInt128Max,
            TestNumbers.UInt128Max + 1,
            TestNumbers.UInt192Max - 1,
            TestNumbers.UInt192Max,
            TestNumbers.UInt192Max + 1,
            TestNumbers.UInt256Max - 1,
            TestNumbers.UInt256Max,
            // j=0 - 0 corrections
            (BigInteger)new UInt256(0xF6BE55883FD648AF, 0xBE16F18C94CBF8C2, 0x139B2FDC0D975979),
            (BigInteger)new UInt256(0x0D3000A2AD2C9E9F, 0xD911C522570ED689),
            // j=0 - 1 correction
            (BigInteger)new UInt256(0xE688558F6E158B6D, 0xC4FF6E1D86DB666F, 0x55B9AD38D5464280),
            (BigInteger)new UInt256(0xEA9108D3F5A64EFA, 0xB3C9574B96942351),
            // j=0 - 2 corrections (triggers both the qhat adjustment and the add-back correction)
            (BigInteger)new UInt256(0x6EC311A3B68AFEAE, 0x34B0045330F4129E, 0x83C781A177368C89),
            (BigInteger)new UInt256(0xE946BAB2D13F0B5B, 0x94F2E9ADF2BF1ABE),

            (BigInteger)new UInt256(0xA65CCF8CB37CD823, 0xE3C6A3017C245FE9, 0x88CA61E7342CA727, 0x845E2203A13CF891),
            (BigInteger)new UInt256(0xC43555303099DAA4, 0x917AEC80C08B64C1),
            // x.u3 == y1, x.u2 == 0 ensures j=2 correction triggers
            (BigInteger)new UInt256(0, 0, 0, 0x8000000000000001),
            (BigInteger)new UInt256(0xFFFFFFFFFFFFFFFF, 0x8000000000000001),
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
