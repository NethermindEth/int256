using System;
using System.Numerics;
using FluentAssertions;
using NUnit.Framework;

namespace Nethermind.Int256.Test
{
    public abstract class UInt256TestsTemplate<T> where T : IInteger<T>
    {
        protected readonly Func<BigInteger, T> convert;
        protected readonly Func<int, T> convertFromInt;
        protected readonly Func<BigInteger, BigInteger> postprocess;
        protected readonly BigInteger maxValue;

        protected UInt256TestsTemplate(Func<BigInteger, T> convert, Func<int, T> convertFromInt, Func<BigInteger, BigInteger> postprocess, BigInteger maxValue)
        {
            this.convert = convert;
            this.convertFromInt = convertFromInt;
            this.postprocess = postprocess;
            this.maxValue = maxValue;
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public virtual void Add((BigInteger A, BigInteger B) test)
        {
            BigInteger resBigInt = test.A + test.B;
            resBigInt %= (BigInteger.One << 256);
            resBigInt = postprocess(resBigInt);

            T a = convert(test.A);
            T b = convert(test.B);
            a.Add(b, out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            a.Add(b, out a);
            a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public virtual void AddOverflow((BigInteger A, BigInteger B) test)
        {
            BigInteger resUInt256;
            BigInteger resBigInt = test.A + test.B;
            resBigInt %= (BigInteger.One << 256);
            resBigInt = postprocess(resBigInt);
            T uint256a = convert(test.A);
            T uint256b = convert(test.B);

            bool overflow = T.AddOverflow(uint256a, uint256b, out T res);
            res.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);

            if (test.A + test.B <= (BigInteger)UInt256.MaxValue)
            {
                overflow.Should().Be(false);
            }
            else
            {
                overflow.Should().Be(true);
            }

            overflow = T.AddOverflow(uint256a, uint256b, out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
            if (test.A + test.B <= (BigInteger)UInt256.MaxValue)
            {
                overflow.Should().Be(false);
            }
            else
            {
                overflow.Should().Be(true);
            }
        }

        [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.TestCases))]
        public virtual void AddMod((BigInteger A, BigInteger B, BigInteger M) test)
        {
            if (test.M.IsZero)
            {
                return;
            }
            BigInteger resBigInt = (test.A + test.B) % test.M;
            resBigInt %= (BigInteger.One << 256);
            resBigInt = postprocess(resBigInt);

            T uint256a = convert(test.A);
            T uint256b = convert(test.B);
            T uint256m = convert(test.M);
            uint256a.AddMod(uint256b, uint256m, out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            uint256a.AddMod(uint256b, uint256m, out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public virtual void Subtract((BigInteger A, BigInteger B) test)
        {
            if (test.A < test.B)
            {
                return;
            }

            BigInteger resBigInt = test.A - test.B;
            resBigInt %= BigInteger.One << 256;
            resBigInt = postprocess(resBigInt);

            T uint256a = convert(test.A);
            T uint256b = convert(test.B);
            uint256a.Subtract(uint256b, out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            uint256a.Subtract(uint256b, out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }
        
        [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.TestCases))]
        public virtual void SubtractMod((BigInteger A, BigInteger B, BigInteger M) test)
        {
            SubtractModCore(test, true);
        }

        protected void SubtractModCore((BigInteger A, BigInteger B, BigInteger M) test, bool convertToUnsigned)
        {
            if (test.M.IsZero)
            {
                return;
            }
            BigInteger resBigInt = (test.A - test.B) % test.M;

            // convert to unsigned modular value
            if (convertToUnsigned && resBigInt.Sign == -1)
            {
                resBigInt = test.M + resBigInt;
            }

            resBigInt %= (BigInteger.One << 256);
            resBigInt = postprocess(resBigInt);

            T uint256a = convert(test.A);
            T uint256b = convert(test.B);
            T uint256m = convert(test.M);
            uint256a.SubtractMod(uint256b, uint256m, out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            uint256a.SubtractMod(uint256b, uint256m, out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public virtual void SubtractOverflow((BigInteger A, BigInteger B) test)
        {
            BigInteger resUInt256;
            BigInteger resBigInt = test.A - test.B;
            resBigInt %= BigInteger.One << 256;
            resBigInt = postprocess(resBigInt);
            T uint256a = convert(test.A);
            T uint256b = convert(test.B);

            if (test.A >= test.B)
            {
                if (uint256a is UInt256 a && uint256b is UInt256 b)
                {
                    UInt256 res = a - b;
                    res.Convert(out resUInt256);
                    resUInt256.Should().Be(resBigInt);
                }
                else
                {
                    uint256a.Subtract(uint256b, out T res);
                    res.Convert(out resUInt256);
                    resUInt256.Should().Be(resBigInt);

                    uint256a.Subtract(uint256b, out uint256a);
                    uint256a.Convert(out resUInt256);
                    resUInt256.Should().Be(resBigInt);
                }
            }
            else
            {
                if (uint256a is UInt256 a && uint256b is UInt256 b)
                {
                    a.Invoking(y => y - b)
                        .Should().Throw<ArithmeticException>()
                        .WithMessage($"Underflow in subtraction {a} - {b}");
                }
                else
                {
                    uint256a.Subtract(uint256b, out T res);
                    res.Convert(out resUInt256);
                    resUInt256.Should().Be(resBigInt);

                    uint256a.Subtract(uint256b, out uint256a);
                    uint256a.Convert(out resUInt256);
                    resUInt256.Should().Be(resBigInt);
                }
            }
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public virtual void Multiply((BigInteger A, BigInteger B) test)
        {
            BigInteger resBigInt = (test.A * test.B) % (BigInteger.One << 256);
            resBigInt = postprocess(resBigInt);

            T uint256a = convert(test.A);
            T uint256b = convert(test.B);
            uint256a.Multiply(uint256b, out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            uint256a.Multiply(uint256b, out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.TestCases))]
        public virtual void MultiplyMod((BigInteger A, BigInteger B, BigInteger M) test)
        {
            if (test.M.IsZero)
            {
                return;
            }
            BigInteger resBigInt = ((test.A * test.B) % test.M) % (BigInteger.One << 256);
            resBigInt = postprocess(resBigInt);

            T uint256a = convert(test.A);
            T uint256b = convert(test.B);
            T uint256m = convert(test.M);
            uint256a.MultiplyMod(uint256b, uint256m, out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            uint256a.MultiplyMod(uint256b, uint256m, out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public virtual void Div((BigInteger A, BigInteger B) test)
        {
            if (test.B.IsZero)
            {
                return;
            }
            BigInteger resBigInt = (test.A / test.B) % (BigInteger.One << 256);
            resBigInt = postprocess(resBigInt);

            T uint256a = convert(test.A);
            T uint256b = convert(test.B);
            uint256a.Divide(uint256b, out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            uint256a.Divide(in uint256b, out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }
        
        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public virtual void And((BigInteger A, BigInteger B) test)
        {
            BigInteger resBigInt = test.A & test.B;
            resBigInt = postprocess(resBigInt);

            T uint256a = convert(test.A);
            T uint256b = convert(test.B);
            T.And(uint256a, uint256b, out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            T.And(uint256a, uint256b, out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public virtual void Or((BigInteger A, BigInteger B) test)
        {
            BigInteger resBigInt = test.A | test.B;
            resBigInt = postprocess(resBigInt);

            T uint256a = convert(test.A);
            T uint256b = convert(test.B);
            T.Or(uint256a, uint256b, out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            T.Or(uint256a, uint256b, out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.TestCases))]
        public virtual void Xor((BigInteger A, BigInteger B) test)
        {
            BigInteger resBigInt = test.A ^ test.B;
            resBigInt = postprocess(resBigInt);

            T uint256a = convert(test.A);
            T uint256b = convert(test.B);
            T.Xor(uint256a, uint256b, out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            T.Xor(uint256a, uint256b, out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.ShiftTestCases))]
        public virtual void Exp((BigInteger A, int n) test)
        {
            BigInteger resBigInt = BigInteger.Pow(test.A, test.n);
            resBigInt %= (BigInteger.One << 256);
            resBigInt = postprocess(resBigInt);

            T uint256a = convert(test.A);

            uint256a.Exp(convertFromInt(test.n), out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            uint256a.Exp(convertFromInt(test.n), out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(TernaryOps), nameof(TernaryOps.TestCases))]
        public virtual void ExpMod((BigInteger A, BigInteger B, BigInteger M) test)
        {
            if (test.M.IsZero || test.B < 0)
            {
                return;
            }
            BigInteger resBigInt = BigInteger.ModPow(test.A, test.B, test.M);
            resBigInt %= (BigInteger.One << 256);
            resBigInt = postprocess(resBigInt);

            T uint256a = convert(test.A);
            T uint256b = convert(test.B);
            T uint256m = convert(test.M);

            uint256a.ExpMod(uint256b, uint256m, out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            uint256a.ExpMod(uint256b, uint256m, out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.ShiftTestCases))]
        public virtual void Lsh((BigInteger A, int n) test)
        {
            if (test.n == 0)
            {
                return;
            }
            BigInteger resBigInt = test.A << test.n;
            resBigInt %= (BigInteger.One << 256);
            resBigInt = postprocess(resBigInt);

            T uint256a = convert(test.A);
            uint256a.LeftShift(test.n, out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            uint256a.LeftShift(test.n, out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(BinaryOps), nameof(BinaryOps.ShiftTestCases))]
        public virtual void Rsh((BigInteger A, int n) test)
        {
            if (test.n == 0)
            {
                return;
            }
            BigInteger resBigInt = test.A >> test.n;
            resBigInt %= (BigInteger.One << 256);
            resBigInt = postprocess(resBigInt);

            T uint256a = convert(test.A);
            uint256a.RightShift(test.n, out T res);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().Be(resBigInt);

            uint256a.RightShift(test.n, out uint256a);
            uint256a.Convert(out resUInt256);

            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
        public virtual void ToBigIntegerAndBack(BigInteger test)
        {
            T uint256 = convert(test);
            uint256.Convert(out BigInteger res);
            res.Should().Be(test);
        }

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
        public virtual void Not(BigInteger test)
        {
            BigInteger resBigInt = ~test;
            resBigInt %= (BigInteger.One << 256);
            if (typeof(T) == typeof(UInt256))
            {
                ((Int256)resBigInt)._value.Convert(out resBigInt);
            }
            T uint256 = convert(test);
            T.Not(uint256, out T res);
            res.Convert(out BigInteger resUInt256);
            resUInt256.Should().Be(resBigInt);

            T.Not(in uint256, out uint256);
            uint256.Convert(out resUInt256);
            resUInt256.Should().Be(resBigInt);
        }

        [TestCaseSource(typeof(UnaryOps), nameof(UnaryOps.TestCases))]
        public virtual void ToString(BigInteger test)
        {
            T uint256 = convert(test);
            uint256.ToString().Should().Be(test.ToString());
        }
    }

    [Parallelizable(ParallelScope.All)]
    public class UInt256Tests : UInt256TestsTemplate<UInt256>
    {
        public UInt256Tests() : base((BigInteger x) => (UInt256)x, (int x) => (UInt256)x, x => x, TestNumbers.UInt256Max) { }

        [Test]
        public virtual void Zero_is_min_value()
        {
            convert(1).ZeroValue.Should().Be(UInt256.MinValue);
        }

        [Test]
        public virtual void Zero_is_zero()
        {
            convert(1).ZeroValue.Should().Be(convert(BigInteger.Zero));
        }

        [Test]
        public virtual void Is_zero()
        {
            convert(1).ZeroValue.IsZero.Should().BeTrue();
            UInt256.One.IsZero.Should().BeFalse();
        }

        [Test]
        public virtual void One_is_one()
        {
            convert(1).OneValue.Should().Be(convert(BigInteger.One));
        }

        [Test]
        public virtual void Is_one()
        {
            convert(1).OneValue.IsOne.Should().BeTrue();
            convert(1).ZeroValue.IsOne.Should().BeFalse();
        }

        [Test]
        public virtual void Max_value_is_correct()
        {
            convert(1).MaximalValue.Should().Be(convert(maxValue));
        }
        
        [Test]
        public virtual void ToBigEndian_And_Back()
        {
            byte[] bidEndian = convert(1000000000000000000).ToBigEndian();
            new UInt256(bidEndian, true).Should().Be(convert(1000000000000000000));
        }
        
        [Test]
        public virtual void ToLittleEndian_And_Back()
        {
            byte[] bidEndian = convert(1000000000000000000).ToLittleEndian();
            new UInt256(bidEndian).Should().Be(convert(1000000000000000000));
        }
        
        [Test]
        public virtual void Check_For_Correct_Big_And_Little_Endian()
        {
            byte[] bigEndianRepresentation =
            {
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 224, 182, 179, 167, 100,
                0, 0
            };
            convert(1000000000000000000).ToBigEndian().Should().BeEquivalentTo(bigEndianRepresentation);
            
            byte[] littleEndianRepresentation =
            {
                0, 0, 100, 167, 179, 182, 224, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
            };
            convert(1000000000000000000).ToLittleEndian().Should().BeEquivalentTo(littleEndianRepresentation);
        }
        
        [TestCaseSource(typeof(Convertibles), nameof(Convertibles.TestCases))]
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
            if (!valueString.StartsWith('-'))
            {
                try
                {
                    UInt256 item = (UInt256)BigInteger.Parse(valueString);
                    string expected = expectedString ?? Expected(valueString);
                    string convertedValue = Expected(((IFormattable)System.Convert.ChangeType(item, type)).ToString("0.#", null));
                    convertedValue.Should().BeEquivalentTo(expected);
                }
                catch (Exception e) when (e.GetType() == expectedException) { }
            }
        }

        [TestCaseSource(typeof(Convertibles), nameof(Convertibles.TestCasesConvertFrom))]
        public void ConvertFrom(Type type, BigInteger bigIntValue)
        {
            UInt256 ConvertToUInt256(Type type, BigInteger number) =>
                type switch
                {
                    var t when type == typeof(byte) => (UInt256)(byte)number,
                    var t when type == typeof(sbyte) => (UInt256)(sbyte)number,
                    var t when type == typeof(short) => (UInt256)(short)number,
                    var t when type == typeof(ushort) => (UInt256)(ushort)number,
                    var t when type == typeof(int) => (UInt256)(int)number,
                    var t when type == typeof(uint) => (UInt256)(uint)number,
                    var t when type == typeof(long) => (UInt256)(long)number,
                    var t when type == typeof(ulong) => (UInt256)(ulong)number,
                    var t when type == typeof(float) => (UInt256)(float)number,
                    var t when type == typeof(double) => (UInt256)(double)number,
                    var t when type == typeof(decimal) => (UInt256)(decimal)number,
                    var t when type == typeof(BigInteger) => (UInt256)(BigInteger)number,
                    _ => throw new ArgumentOutOfRangeException(nameof(type), type, null)
                };

            UInt256 res = ConvertToUInt256(type, bigIntValue);
            res.Convert(out BigInteger resUInt256);

            resUInt256.Should().BeEquivalentTo(bigIntValue);
        }
    }
}
