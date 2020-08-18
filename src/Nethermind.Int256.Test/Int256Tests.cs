using System;
using System.Numerics;
using FluentAssertions;
using NUnit.Framework;

namespace Nethermind.Int256.Test
{
    public class Int256Tests : UInt256TestsTemplate<Int256>
    {

        private static BigInteger Postprocess(BigInteger big)
        {
            var bytes = big.ToByteArray();
            return new BigInteger(bytes.AsSpan().Slice(0, Math.Min(256 / 8, bytes.Length)));
        }

        public Int256Tests() : base((BigInteger x) => new Int256(x), (int x) => new Int256(x), Postprocess, TestNumbers.Int256Max) { }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
        public override void Add((BigInteger A, BigInteger B) test) => base.Add(test);

        [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.SignedModTestCases))]
        public override void AddMod((BigInteger A, BigInteger B, BigInteger M) test) => base.AddMod(test);

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
        public override void Subtract((BigInteger A, BigInteger B) test) => base.Subtract(test);

        [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.SignedModTestCases))]
        public void SubtractMod((BigInteger A, BigInteger B, BigInteger M) test)
        {
            if (test.M.IsZero)
            {
                return;
            }

            BigInteger resBigInt = ((test.A - test.B) % test.M) % (BigInteger.One << 256);
            resBigInt = postprocess(resBigInt);

            Int256 uint256a = convert(test.A);
            Int256 uint256b = convert(test.B);
            Int256 uint256m = convert(test.M);
            uint256a.SubtractMod(uint256b, uint256m, out Int256 res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
        public override void Multiply((BigInteger A, BigInteger B) test) => base.Multiply(test);

        [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.SignedModTestCases))]
        public override void MultiplyMod((BigInteger A, BigInteger B, BigInteger M) test) => base.MultiplyMod(test);

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedTestCases))]
        public override void Div((BigInteger A, BigInteger B) test) => base.Div(test);

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedShiftTestCases))]
        public override void Exp((BigInteger A, int n) test) => base.Exp(test);

        [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.SignedModTestCases))]
        public override void ExpMod((BigInteger A, BigInteger B, BigInteger M) test) => base.ExpMod(test);

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedShiftTestCases))]
        public override void Lsh((BigInteger A, int n) test) => base.Lsh(test);

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.SignedShiftTestCases))]
        public override void Rsh((BigInteger A, int n) test) => base.Rsh(test);

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.SignedTestCases))]
        public override void ToBigIntegerAndBack(BigInteger test) => base.ToBigIntegerAndBack(test);

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.SignedTestCases))]
        public override void ToString(BigInteger test) => base.ToString(test);
    }
}
