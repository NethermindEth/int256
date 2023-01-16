using System;
using System.Numerics;
using FluentAssertions;
using NUnit.Framework;

namespace Nethermind.Int256.Test
{
    [Parallelizable(ParallelScope.All)]
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
        public override void SubtractMod((BigInteger A, BigInteger B, BigInteger M) test) => base.SubtractModCore(test, false);

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

        [TestCaseSource(typeof(Convertibles), nameof(Convertibles.SignedTestCases))]
        public void Convert(Type type, object value, Type expectedException, string expectedString)
        {
            string Expected(string valueString)
            {
                if (valueString.Contains("Infinity"))
                {
                    return valueString.StartsWith('-') ? "-∞" : "∞" ;
                }
                string expected = valueString.Replace(",", "");
                return type == typeof(float) ? expected[..Math.Min(6, expected.Length)] : type == typeof(double) ? expected[..Math.Min(14, expected.Length)] : expected;
            }

            string valueString = value.ToString()!;
            Int256 item = (Int256)BigInteger.Parse(valueString);
            try
            {
                string expected = expectedString ?? Expected(valueString);
                string convertedValue = Expected(((IFormattable)System.Convert.ChangeType(item, type)).ToString("0.#", null));
                convertedValue.Should().BeEquivalentTo(expected);
            }
            catch (Exception e) when(e.GetType() == expectedException) { }
        }
    }
}
